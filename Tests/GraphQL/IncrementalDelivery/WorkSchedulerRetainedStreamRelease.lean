import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamOpenness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectStreamSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasedObjectStreamHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectStreamCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleasePublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedClosureLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulSettlementAcceptance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayValueConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegisteredCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupEventAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamReplay
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A retained successful child releases its stream during its parent's recursive drain. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedStreamRelease
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Shared producer settlement waits for its surviving latent owner
-----------------------------------------------------------------------------------------

private def root : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def stream : DeliveryNode := { ref := 3, path := [.field "values"] }
private def failedTask : Occurrence := .executionGroup [1, 0]
private def producerTask : Occurrence := .executionGroup [1, 1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]

private def entries : List (Result ResponseValue × Execution.Work) :=
  [
    (.ok (.scalar "x", 0), .empty),
    (.ok (.null, 0), .empty),
    (.ok (.scalar "z", 0), .empty)
  ]

private def children : Execution.Work :=
  .combine (.combine .empty (.stream stream entries)) .empty

private def producerValue : ExecutionGroupValue :=
  { deliveryGroups := [root, child], path := [], data := [("values", .list [])] }

private def parentValue : ExecutionGroupValue :=
  { deliveryGroups := [parent], path := [], data := [("b", .scalar "b")] }

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩] [] (.error 1) .empty)
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] []
          (.ok (producerValue.data, 0)) children)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (parentValue.data, 0))
            (.combine .empty .empty)) .empty)))

private def first : GraphEvent := .taskFailure failedTask 1

private def produced : GraphEvent :=
  .taskSuccess producerTask
    { value := producerValue, work := Work.fromExecution children [1, 1, 0, 0] }

private def finish : GraphEvent :=
  .taskSuccess parentTask { value := parentValue }

private def initial : State := State.initialize (Work.fromExecution work)
private def waiting : State := (initial.runNormalized [[first], [produced]]).1

/-- The shared stream producer comes from execution of overlapping defers R and C.
Witness: the actual executor retains C's dependency on P and the producer's stream subtree.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "first"), field "values" [] [.stream]] (some "R"),
      defer [field "b", defer [field "values" [] [.stream]] (some "C")] (some "P")], ?_⟩
  cbv

/-- All three settlements have exact fixed outcomes and fresh, root-produced identities.
Witness: locate each generated task, check child lowering, then append legal source inputs.
-/
theorem inputs_valid : ValidGraphEvents work [first, produced, finish] := by
  have failed : TaskAt work failedTask [root.ref] none (.object [] (.error 1)) :=
    ⟨[⟨root, []⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩
  have producer : TaskAt work producerTask [root.ref, child.ref] none
      (.object [] (.ok (producerValue.data, 0))) :=
    ⟨[⟨root, []⟩, ⟨child, [parent]⟩], [], .ok (producerValue.data, 0), children, [],
      rfl, rfl, rfl⟩
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok (parentValue.data, 0))) :=
    ⟨[⟨parent, []⟩], [], .ok (parentValue.data, 0), .combine .empty .empty, [],
      rfl, rfl, rfl⟩
  have prior : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, _, failed⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, failed, by intro source impossible; cases impossible⟩
  have middle : ValidGraphEvents work [first, produced] :=
    .append prior ⟨_, _, producer, by cbv, by cbv⟩
      (by simp [first, produced, failedTask, producerTask, GraphEvent.Fresh,
        GraphEvent.identities])
      ⟨_, _, _, producer, by intro source impossible; cases impossible⟩
  exact .append middle ⟨_, _, parentKnown, by cbv, by cbv⟩
    (by simp [first, produced, finish, failedTask, producerTask, parentTask,
      GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩

/-- The generated stream retains the shared task as its unique structural producer.
Witness: the exact child address, including both enclosing defer owners.
-/
private theorem streamKnown
    : NodeAt work stream .stream [root.ref, child.ref] (some producerTask) := by
  refine ⟨[1, 1, 0, 0, 0, 1], entries, ?_⟩
  cbv

/-- The retained shared producer's stream announcement is globally unique across batches.
Witness: the actual initialized inventory theorem on the same generated failed-owner case;
the producer waits under C, then is consumed inside P's recursive release drain.
-/
theorem stream_notice_inventory_unique
    : (initial.initialStreams.map DeliveryNode.ref
        ++ (initial.runNormalized [[first], [produced], [finish]]).2.flatten.flatMap
            streamNoticeRefs).Nodup :=
  createWorkQueue_runNormalized_streamNoticeRefs_nodup generated inputs_valid

/-- The successful producer remains buffered after R fails, with its stream still inactive.
Witness: real replay emits only R's failure and retains the producer's value and child ref.
-/
theorem retained_producer
    : (initial.runNormalized [[first], [produced]]).2 = [[.groupFailure root 1]]
      ∧ waiting.rootStreams = []
      ∧ (waiting.taskNode? producerTask).bind TaskNode.value = some producerValue
      ∧ (waiting.taskNode? producerTask).map TaskNode.childStreams
        = some [stream.ref] := by
  constructor
  · cbv
  constructor
  · cbv
  constructor <;> cbv

/-- The shared buffered producer retains every structural child stream after another owner fails.
Witness: find the actual retained value, then derive its child ref from the general replay
completeness invariant rather than assume the child list or a successful release.
-/
theorem retained_child_stream_complete
    : ∃ node,
        (initial.replayGraphEvents [first, produced]).taskNode? producerTask = some node
        ∧ node.value = some producerValue
        ∧ stream.ref ∈ node.childStreams := by
  have complete := generated.replayGraphEvents_storedStreamsComplete
    (inputs_valid.prefix (before := [first, produced]) ⟨[finish], rfl⟩)
  have buffered : ((initial.replayGraphEvents [first, produced]).taskNode?
      producerTask).bind TaskNode.value = some producerValue := by cbv
  cases found : (initial.replayGraphEvents [first, produced]).taskNode? producerTask with
  | none => simp only [found, Option.bind_none, reduceCtorEq] at buffered
  | some node =>
      have stored : node.value = some producerValue := by
        simpa only [found, Option.bind_some] using buffered
      refine ⟨node, rfl, stored, ?_⟩
      exact complete node (State.taskNode?_some found).1
        (by rw [stored]; rfl)
        (by simp)
        stream [root.ref, child.ref]
        ((State.taskNode?_some found).2.symm ▸ streamKnown)

-----------------------------------------------------------------------------------------
-- Parent release drains C, publishing the retained producer before its stream notice
-----------------------------------------------------------------------------------------

/-- Retirement of the surviving owner forces the retained producer's child notice.
Witness: complete stored links and general source-replay stream conservation; only the
concrete owner's presence, noncancellation, and retirement are evaluated for this fixture.
-/
theorem retained_child_stream_must_release
    : stream.ref
      ∈ ((initial.replayGraphEvents [first, produced]).rawEventReplay [finish]).2.flatMap
          rawStreamNoticeRefs := by
  obtain ⟨node, found, stored, attached⟩ := retained_child_stream_complete
  have groups : node.task.groups = [root, child] := by
    have actual : ((initial.replayGraphEvents [first, produced]).taskNode? producerTask).map
        (fun task => task.task.groups) = some [root, child] := by cbv
    simpa only [found, Option.map_some, Option.some.injEq] using actual
  apply (generated.replayGraphEvents_bufferedStreamsConserved
          (before := [first, produced]) (events := [finish]) inputs_valid
          (by cbv)).retired_notice
    found stored attached (owner := child.ref)
  · simp only [groups, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, or_true]
  · cbv; exact .tail _ (.head _)
  · cbv; intro impossible; cases impossible
  · cbv
    intro impossible
    cases impossible with
    | tail _ impossible => cases impossible

/-- Separate or joined inputs release the child stream only after the stored producer patch.
Witness: exact normalized output order; the stream remains active with its items pending.
-/
theorem released_output
    : ∀ batches ∈ [[[first], [produced], [finish]], [[first, produced, finish]]],
        inputsStarted work batches = true
        ∧ (initial.runNormalized batches).2.flatten
          = [
            .groupFailure root 1,
            .groupValues parent [parentValue],
            .groupSuccess parent [child] [],
            .groupValues child [producerValue],
            .groupSuccess child [] [stream]
          ]
        ∧ (initial.runNormalized batches).1.rootStreams = [stream.ref]
        ∧ (initial.runNormalized batches).1.terminated = false := by
  intro batches member
  have choices : batches = [[first], [produced], [finish]]
      ∨ batches = [[first, produced, finish]] := by simpa using member
  rcases choices with rfl | rfl <;> exact ⟨by cbv, by cbv, by cbv, by cbv⟩

/-- One fresh occurrence inventory places the retained producer before the drain's notice.
Witness: the general replay release theorem, instantiated at C's actual carrier index.
This is publication support, not a full scheduler-admission or failure-cut witness.
-/
theorem released_inventory
    : ∀ batches ∈ [[[first], [produced], [finish]], [[first, produced, finish]]],
        ∃ published : List ObjectPublication,
          (published.map Prod.fst).Nodup
          ∧ published.map (fun publication => publication.2)
            = [parentValue, producerValue]
          ∧ producerTask ∈ (published.take 2).map Prod.fst := by
  intro batches member
  have choices : batches = [[first], [produced], [finish]]
      ∨ batches = [[first, produced, finish]] := by simpa using member
  have flat : batches.flatten = [first, produced, finish] := by
    rcases choices with rfl | rfl <;> rfl
  have output := (released_output batches member).2.1
  obtain ⟨published, values, ledger, supported⟩ :=
    createWorkQueue_runNormalized_streamReleasePublications generated (flat ▸ inputs_valid)
  have carrier : (initial.runNormalized batches).2.flatten[4]?
      = some (.groupSuccess child [] [stream]) := by rw [output]; rfl
  obtain ⟨occurrence, producer, earlier⟩ :=
    supported 4 child [] [stream] carrier stream List.mem_cons_self
      [root.ref, child.ref] (some producerTask) streamKnown
  have same := Option.some.inj producer
  subst occurrence
  refine ⟨published, ledger.unique, ?_, ?_⟩
  · change published.map (fun publication => publication.2)
        = (initial.runNormalized batches).2.flatten.flatMap normalizedObjectValues at values
    rw [output] at values
    exact values
  · change producerTask ∈ (published.take
        (((initial.runNormalized batches).2.flatten.take 4).flatMap
          normalizedObjectValues).length).map Prod.fst at earlier
    rw [output] at earlier
    exact earlier

/-- Incoming and retained values share the ledger supporting the released stream.
Witness: the actual healthy task-success branch, with all queue invariants derived from
the prior valid replay. The parent is covered before its carrier and the old producer
before its child's carrier using the very same fresh occurrence labels.
-/
theorem released_joint_ledger
    : ∃ published : List ObjectPublication,
        (published.map Prod.fst).Nodup
        ∧ published.map Prod.snd = [parentValue, producerValue]
        ∧ (parentTask, parentValue) ∈ published.take 1
        ∧ producerTask ∈ (published.take 2).map Prod.fst := by
  have valid : ValidGraphEvents work [[first], [produced]].flatten :=
    inputs_valid.prefix ⟨[finish], rfl⟩
  have started : inputsStarted work [[first], [produced]] = true := by cbv
  have accounted := generated.runNormalized_pendingLedger _ valid started
  have links := generated.runNormalized_storedTaskLinks _ valid started
  have settled := createWorkQueue_runNormalized_childStreamsSettled (Work.fromExecution work)
    [[first], [produced]]
  have provenance := createWorkQueue_runNormalized_childStreamsMatchWork valid
  have inventory : waiting.PublicationInventory (fun _ _ => True) [] :=
    ⟨by simp, by simp, fun _ _ _ _ => ⟨trivial, by simp⟩⟩
  have found : waiting.taskNode? parentTask = some { task := ⟨parentTask, [parent]⟩ } := by
    cbv
  have matching := inputs_valid.event_matches (event := finish) (by simp)
  have memberships : waiting.GroupMembershipOrder := by
    simpa only [waiting, initial, State.runNormalized_stateFold, List.foldl_cons,
      List.foldl_nil]
      using ((createWorkQueue_groupMembershipOrder
                (Work.fromExecution work)).handleGraphEvents
              [first]).handleGraphEvents
        [produced]
  obtain ⟨published, values, final, covered, _, supported, _⟩ :=
    inventory.taskSuccess_preparedCoverage generated accounted links settled provenance
      parentTask { value := parentValue } matching _ found (by cbv)
      (by simp [GraphEvent.taskSettlements, GraphEvent.groupSuccesses,
        GraphEvent.groupFailures, first, produced, failedTask, producerTask, parentTask])
      trivial (by simp) memberships
  have output : (waiting.taskSuccess parentTask { value := parentValue }).2
      = [.groupValues parent [parentValue], .groupSuccess parent [child] [],
        .groupValues child [producerValue], .groupSuccess child [] [stream]] := by cbv
  have carrier : (waiting.taskSuccess parentTask { value := parentValue }).2[3]?
      = some (.groupSuccess child [] [stream]) := by rw [output]; rfl
  obtain ⟨occurrence, producer, earlier⟩ :=
    supported 3 child [] [stream] carrier stream List.mem_cons_self
      [root.ref, child.ref] (some producerTask) streamKnown
  have same := Option.some.inj producer
  subst occurrence
  refine ⟨published, final.unique, ?_, ?_, ?_⟩
  · simpa only [output, List.flatMap_cons, List.flatMap_nil, WorkQueueEvent.objectValues,
      List.append_nil, List.nil_append, List.cons_append] using values
  · have parentCovered := covered 1 parent [child] [] (by rw [output]; rfl)
      parentTask { task := ⟨parentTask, [parent]⟩, value := some parentValue }
      parentValue (by cbv) rfl (by simp)
    simpa [output, WorkQueueEvent.objectValues] using parentCovered
  · simpa [output, WorkQueueEvent.objectValues] using earlier

/-- The shared conformance witness retains P's data before its same-handler child flush.
Witness: recover the final task handler's internal drain certificate from the full replay
ledger. At drain entry P is already retired, forcing its just-installed value into the
earlier ledger prefix; the common matching interprets that prefix before C's value atom.
-/
theorem released_drain_prefix_on_common_witness
    : ∃ w : ConformancePlan.Witness,
        w.events = initial.nonterminalAtoms [[first], [produced], [finish]]
        ∧ Published w.matching (w.events.take 3) parentTask := by
  let batches := [[first], [produced], [finish]]
  obtain ⟨w, history, _, _, _, _, _, _, _, _, ledger⟩ :=
    ConformancePlan.mixed_groupAccountingCertificates (inputs := batches)
      generated inputs_valid (by cbv)
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  have replay := batched.flatten (by cbv)
  have prefixes := replay.atPrefixDrainOwners [first, produced] finish []
  have stateEq : (ConformancePlan.initialQueue work).replayGraphEvents [first, produced]
      = waiting := by cbv
  have offsetEq : (((ConformancePlan.initialQueue work).rawEventReplay
      [first, produced]).2.flatMap WorkQueueEvent.objectValues).length = 0 := by cbv
  have countEq : ((waiting.handleGraphEvent finish).2.flatMap
      WorkQueueEvent.objectValues).length = 2 := by cbv
  dsimp only at prefixes
  rw [stateEq, offsetEq, countEq, List.drop_zero] at prefixes
  let incoming : TaskNode := { task := ⟨parentTask, [parent]⟩ }
  let prepared := ((waiting.putTaskNode
    { incoming with value := some parentValue }).maybeIntegrateWork {} (some parentTask)).1
  let released := [parent].foldl successGroupStep (prepared, [], {})
  let activated := released.1.startNewWork released.2.2
  have handlerPrefixes := prefixes incoming (by cbv) (by cbv)
  have boundary := handlerPrefixes.drain 0 (by decide)
  simp only [State.drainReadyGroups.go, List.append_nil] at boundary
  change prepared.StoredOwnersConserved
    ((published.take 2).take (released.2.1.flatMap WorkQueueEvent.objectValues).length)
    activated at boundary
  have firstCount : (released.2.1.flatMap WorkQueueEvent.objectValues).length = 1 := by
    dsimp only [released, prepared, incoming]
    cbv
  rw [firstCount] at boundary
  have buffered : prepared.taskNode? parentTask
      = some { incoming with value := some parentValue } := by
    dsimp only [prepared, incoming]
    cbv
  have present : parent.ref ∈ prepared.groupNodes.map (fun node => node.group.node.ref) := by
    dsimp only [prepared, incoming]
    cbv; exact .head _
  have uncancelled : parent.ref ∉ activated.cancelledGroups := by
    dsimp only [activated, released, prepared, incoming]
    cbv; intro impossible; cases impossible; contradiction
  have emitted := boundary parentTask { incoming with value := some parentValue } parentValue
    buffered rfl parent.ref (by simp [incoming]) present uncancelled
  have parentPublished : (parentTask, parentValue) ∈ published.take 1 := by
    rcases emitted with emitted | retained
    · simpa only [List.take_take, Nat.min_eq_left (by decide : 1 ≤ 2)] using emitted
    · have absent : parent.ref ∉ activated.groupNodes.map (fun node => node.group.node.ref) := by
        dsimp only [activated, released, prepared, incoming]
        cbv; intro impossible; cases impossible; contradiction
      exact False.elim (absent retained.2)
  refine ⟨w, history, interpret 3 (by rw [history]; cbv) parentTask ?_⟩
  have count : ((w.events.take 3).flatMap normalizedObjectValues).length = 1 := by
    rw [history]
    cbv
  rw [count, ← List.map_take]
  exact List.mem_map.mpr ⟨_, parentPublished, rfl⟩

/-- General handler coverage uses exact earlier source provenance, not an arbitrary label.
Witness: replay supplies the empty prior publication ledger and every queue invariant;
the common event certificate covers the retained producer at C's strict carrier prefix.
-/
theorem released_handler_coverage
    : ∃ published : List ObjectPublication,
        (published.map Prod.fst).Nodup
        ∧ (producerTask, producerValue) ∈ published.take 2
        ∧ waiting.PreparedClosuresCovered finish published
        ∧ StreamReleasePublications work published
            (waiting.handleGraphEvent finish).2 := by
  have valid : ValidGraphEvents work [[first], [produced]].flatten :=
    inputs_valid.prefix ⟨[finish], rfl⟩
  have started : inputsStarted work [[first], [produced]] = true := by cbv
  obtain ⟨prior, priorValues, inventory⟩ := createWorkQueue_runNormalized_publications valid
  have emptyValues : prior.map (fun publication => publication.2) = [] := by
    change prior.map (fun publication => publication.2)
        = (initial.runNormalized [[first], [produced]]).2.flatten.flatMap
          normalizedObjectValues at priorValues
    rw [retained_producer.1] at priorValues
    exact priorValues
  have empty : prior = [] := List.map_eq_nil_iff.mp emptyValues
  subst prior
  have accounted := generated.runNormalized_pendingLedger _ valid started
  have links := generated.runNormalized_storedTaskLinks _ valid started
  have settled := createWorkQueue_runNormalized_childStreamsSettled (Work.fromExecution work)
    [[first], [produced]]
  have provenance := createWorkQueue_runNormalized_childStreamsMatchWork valid
  have laws := inputs_valid.atPrefix (before := [first, produced])
    (event := finish) ⟨[], rfl⟩
  have memberships : waiting.GroupMembershipOrder := by
    simpa only [waiting, initial, State.runNormalized_stateFold, List.foldl_cons,
      List.foldl_nil]
      using ((createWorkQueue_groupMembershipOrder
                (Work.fromExecution work)).handleGraphEvents
              [first]).handleGraphEvents
        [produced]
  obtain ⟨published, _, final, covered, prepared, streams, _, _, _⟩ :=
    inventory.handleGraphEvent_bufferedCoverage generated accounted
      (GraphEvent.taskSettlements_subsetIdentities _) links settled provenance finish
      laws.1 laws.2.1 memberships
  have producerCovered := covered 3 child [] [stream] (by cbv) producerTask
    { task := ⟨producerTask, [root, child]⟩, value := some producerValue,
      childStreams := [stream.ref] } producerValue (by cbv) rfl (by simp)
  refine ⟨published, final.unique, ?_, prepared, streams⟩
  have count : (((waiting.handleGraphEvent finish).2.take 3).flatMap
      WorkQueueEvent.objectValues).length = 2 := by cbv
  change (producerTask, producerValue) ∈ published.take
    (((waiting.handleGraphEvent finish).2.take 3).flatMap WorkQueueEvent.objectValues).length
    at producerCovered
  rwa [count] at producerCovered

/-- Split and joined source batches share their closure and release occurrence witness.
Witness: the general normalized replay construction, retaining its batch/handler slices
and stream-release certificate alongside the actual two-value wire projection.
-/
theorem released_replay_ledger
    : ∀ batches ∈ [[[first], [produced], [finish]], [[first, produced, finish]]],
        ∃ published : List ObjectPublication,
          (published.map Prod.fst).Nodup
          ∧ published.map (fun publication => publication.2)
            = [parentValue, producerValue]
          ∧ initial.BatchClosuresCovered batches published
          ∧ NormalizedStreamReleasePublications work published
              (initial.runNormalized batches).2.flatten := by
  intro batches member
  have choices : batches = [[first], [produced], [finish]]
      ∨ batches = [[first, produced, finish]] := by simpa using member
  have flat : batches.flatten = [first, produced, finish] := by
    rcases choices with rfl | rfl <;> rfl
  obtain ⟨published, values, inventory, covered, supported, _⟩ :=
    generated.runNormalized_bufferedCoverage batches (flat ▸ inputs_valid)
      (released_output batches member).1
  refine ⟨published, inventory.unique, ?_, covered, supported⟩
  change published.map (fun publication => publication.2)
      = (initial.runNormalized batches).2.flatten.flatMap normalizedObjectValues at values
  rw [(released_output batches member).2.1] at values
  exact values

-----------------------------------------------------------------------------------------
-- The first item after release uses a previously announced, already published producer
-----------------------------------------------------------------------------------------

private def item : StreamItem :=
  { occurrence := .item [1, 1, 0, 0, 0, 1] 0, value := ⟨.scalar "x", 0⟩ }

private def next : GraphEvent := .streamItems stream [item]
private def continued : List (List GraphEvent) := [[first], [produced], [finish], [next]]

/-- The first stream item obeys the source laws after the parent's drain starts its stream.
Witness: exact item location, fresh identity, prior successful producer input, and the
implementation's real acceptance check through the failure/retention/release prefix.
-/
theorem continued_inputs
    : ValidGraphEvents work continued.flatten ∧ inputsStarted work continued = true := by
  have located : Located work [1, 1, 0, 0, 0, 1] (.stream stream entries)
      (some producerTask) [root.ref, child.ref] := by cbv
  refine ⟨.append inputs_valid ?_ ?_ ?_, by cbv⟩
  · intro supplied member
    have same := List.mem_singleton.mp member
    subst supplied
    exact ⟨[stream.ref], some producerTask,
      ⟨stream, entries, [root.ref, child.ref], .ok (.scalar "x", 0), .empty,
        located, rfl, rfl, rfl⟩, by cbv⟩
  · simp [next, item, first, produced, finish, failedTask, producerTask, parentTask,
      GraphEvent.Fresh, GraphEvent.identities]
  · refine ⟨[1, 1, 0, 0, 0, 1], entries, some producerTask, [root.ref, child.ref],
      located, by simp, ?_, ?_, by cbv⟩
    · simp [first, produced, finish, GraphEvent.identities]
    · intro source same
      cases same
      simp [first, produced, finish, GraphEvent.successes]

/-- Buffered memberships survive the mixed failure, delayed release, and stream-item input.
Witness: the general source-replay invariant, instantiated with the generated work and
the existing exact source-validity/start proof.
-/
theorem continued_buffered_links : (initial.runNormalized continued).1.StoredTaskLinks :=
  generated.runNormalized_storedTaskLinks continued continued_inputs.1 continued_inputs.2

/-- A stream activated by recursive draining has an emitted notice, not an invented root.
Witness: the general activation/announcement theorem; this query has no initial streams.
-/
theorem released_stream_announced
    : stream.ref
      ∈ (initial.runNormalized [[first], [produced], [finish]]).2.flatten.flatMap
          streamNoticeRefs := by
  have active : stream.ref ∈
      (initial.runNormalized [[first], [produced], [finish]]).1.rootStreams := by
    rw [(released_output _ List.mem_cons_self).2.2.1]
    exact List.mem_cons_self
  have noticed := createWorkQueue_runNormalized_streamRoots (Work.fromExecution work)
    [[first], [produced], [finish]] active
  exact noticed

/-- The first item references an already-announced stream under the contract's ref projection.
Witness: the general strict-prefix announcement theorem at the actual item output index.
-/
theorem first_item_announced
    : stream.ref
      ∈ announcedRefs
          ((initial.initialGroups ++ initial.initialStreams).map DeliveryNode.ref)
          (((initial.runNormalized continued).2.flatten.flatMap publicationAtoms).take
            5) := by
  exact createWorkQueue_runNormalized_streamAnnouncedAt continued_inputs.1
    (index := 5) (event := .streamValues stream [⟨.scalar "x", 0⟩] [] [])
    (by cbv) List.mem_cons_self

/-- The retained child's first stream reference is still open, not merely once announced.
Witness: generated group/stream ref separation and source closure ordering rule out an
earlier completion of this stream, even across the intervening group-failure/drain events.
-/
theorem first_item_open
    : Open ((initial.initialGroups ++ initial.initialStreams).map DeliveryNode.ref)
        (((initial.runNormalized continued).2.flatten.flatMap publicationAtoms).take 5)
        stream.ref := by
  exact createWorkQueue_runNormalized_streamOpenAt generated continued_inputs.1
    (index := 5) (event := .streamValues stream [⟨.scalar "x", 0⟩] [] [])
    (by cbv) List.mem_cons_self

/-- The same fresh output matching gives the later item its actual published producer.
Witness: the general stream-reference readiness theorem, not merely source settlement.
The prior independent failure remains in this history; no cancellation claim is inferred.
-/
theorem first_item_producer_published
    : let outputs := (initial.runNormalized continued).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ Published matching (atoms.take 5) producerTask
        ∧ ∀ index event,
            atoms[index]? = some event
            → IsValue event
            → ¬Published matching (atoms.take index) (matching index) := by
  obtain ⟨matching, batching, values, _, references⟩ :=
    createWorkQueue_runNormalized_streamProducerReadinessMatching generated
      continued_inputs.1 continued_inputs.2
  refine ⟨matching, batching, ?_, fun index event atEvent value =>
    (values index event atEvent value).2.1⟩
  exact references 5 (.streamValues stream [⟨.scalar "x", 0⟩] [] []) (by cbv)
    stream [root.ref, child.ref] (some producerTask) List.mem_cons_self streamKnown _ rfl

-----------------------------------------------------------------------------------------
-- A healthy retired co-owner protects the released stream despite the earlier R failure
-----------------------------------------------------------------------------------------

private def cuts : FailureCuts := [(0, failedTask)]

private theorem failed_known
    : TaskAt work failedTask [root.ref] none (.object [] (.error 1)) :=
  ⟨[⟨root, []⟩], [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem producer_known
    : TaskAt work producerTask [root.ref, child.ref] none
        (.object [] (.ok (producerValue.data, 0))) :=
  ⟨
    [⟨root, []⟩, ⟨child, [parent]⟩],
    [],
    .ok (producerValue.data, 0),
    children,
    [],
    rfl,
    rfl,
    rfl
  ⟩

private theorem failed_payloads
    : ∀ cut occurrence,
        (cut, occurrence) ∈ cuts
        → ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true := by
  intro cut occurrence member
  have same := List.mem_singleton.mp member
  cases same
  exact ⟨_, _, _, failed_known, rfl⟩

/-- Successful stream release has removed C, so the live guard intentionally rejects it.
Witness: exact source replay after the recursive drain. The health theorem below uses
uncancelled retirement instead of treating absence as a successful live lookup.
-/
theorem released_owner_retired
    : (initial.replayGraphEvents [first, produced, finish]).groupNode? child.ref = none
      ∧ (initial.replayGraphEvents [first, produced, finish]).groupIsHealthy child.ref
        = false := by cbv

/-- The actual carrier supplies an uncancelled retired dependency for its shared stream.
Witness: general release-health replay derives both ownership and uncancelledness;
computation checks only the emitted carrier and the source start discipline.
-/
theorem released_owner_support
    : child.ref ∈ [root.ref, child.ref]
      ∧ (initial.replayGraphEvents [first, produced, finish]).RetiredGroup child.ref
      ∧ child.ref
        ∉ (initial.replayGraphEvents [first, produced, finish]).cancelledGroups := by
  have support := generated.runNormalized_streamHealthyDependency
    (batches := [[first], [produced], [finish]]) inputs_valid (by cbv)
    (group := child) (groups := []) (streams := [stream]) (by
      change WorkQueueEvent.groupSuccess child [] [stream]
        ∈ (initial.runNormalized [[first], [produced], [finish]]).2.flatten
      rw [(released_output _ List.mem_cons_self).2.1]
      simp) List.mem_cons_self streamKnown
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore
    (work := work) (batches := [[first], [produced], [finish]]) (by cbv)
  rw [same] at support
  exact support

/-- Actual replay supplies the healthy retired C dependency, even though co-owner R failed.
Witness: the general object-stream guard bridge; the source prefix has no item successes,
and its accepted object inventory is precisely the retained R failure. The observed
history and matching are arbitrary here; producer publication is not assumed.
-/
theorem released_stream_healthy (matching : PublicationMatching)
    (events : List WorkQueueEvent)
    : ¬TaskCancelled work matching events cuts producerTask
      ∧ ¬NodeFailed work matching events cuts stream.ref := by
  apply generated.runNormalized_releasedObjectStreamHealthy_of_itemSafety
    (batches := [[first], [produced], [finish]])
    inputs_valid
    (by cbv)
    (group := child)
    (groups := [])
    (streams := [stream])
    (by
      change WorkQueueEvent.groupSuccess child [] [stream]
        ∈ (initial.runNormalized [[first], [produced], [finish]]).2.flatten
      rw [(released_output _ List.mem_cons_self).2.1]
      simp)
    List.mem_cons_self streamKnown failed_payloads
  · intro occurrence owners producer path result known member
    have same : occurrence = failedTask := by simpa [cuts, failedBefore] using member
    subst occurrence
    cbv
    exact List.mem_cons_self
  · intro address index member
    simp [first, produced, finish, GraphEvent.successes, producerTask, parentTask] at member
  · intro occurrence owners ⟨producer, payload, known⟩ owner member
    have same : occurrence = failedTask := by simpa [cuts, failedBefore] using member
    subst occurrence
    rw [(known.unique failed_known).1] at owner
    simp [root, stream] at owner

-----------------------------------------------------------------------------------------
-- A later co-owner failure cannot invalidate the dependency that released the stream
-----------------------------------------------------------------------------------------

/-- The same generated work permits releasing C before receiving R's independent failure.
Witness: the three exact root-produced settlements are fresh in the alternate order;
each producer premise is empty, so no source dependency is reordered.
-/
theorem delayed_failure_inputs : ValidGraphEvents work [produced, finish, first] := by
  have parentKnown : TaskAt work parentTask [parent.ref] none
      (.object [] (.ok (parentValue.data, 0))) :=
    ⟨[⟨parent, []⟩], [], .ok (parentValue.data, 0), .combine .empty .empty, [],
      rfl, rfl, rfl⟩
  have one : ValidGraphEvents work [produced] :=
    .append .nil (inputs_valid.eachMatches (by simp))
      (by simp [produced, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, producer_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [produced, finish] :=
    .append one (inputs_valid.eachMatches (by simp))
      (by simp [produced, finish, producerTask, parentTask, GraphEvent.Fresh,
        GraphEvent.identities])
      ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩
  exact .append two
    (inputs_valid.eachMatches (by simp))
    (by simp [first, produced, finish, failedTask, producerTask, parentTask,
      GraphEvent.Fresh, GraphEvent.identities])
    ⟨_, _, _, failed_known, by intro source impossible; cases impossible⟩

/-- R's failure cannot erase a value already buffered for surviving C.
Witness: derive the common ledger for success-then-failure, restrict it to the failure
suffix, and apply general replay conservation. Its empty publication prefix forces exact
lookup retention; the final value is not justified by a direct evaluation of that lookup.
-/
theorem buffered_before_failure_retained
    : ∃ node,
        (initial.replayGraphEvents [produced, first]).taskNode? producerTask = some node
        ∧ node.value = some producerValue := by
  have prior : ValidGraphEvents work [produced] :=
    delayed_failure_inputs.prefix ⟨[finish, first], rfl⟩
  have valid : ValidGraphEvents work [produced, first] :=
    .append prior (inputs_valid.eachMatches (by simp))
      (by simp [first, produced, failedTask, producerTask, GraphEvent.Fresh,
        GraphEvent.identities])
      ⟨_, _, _, failed_known, by intro source impossible; cases impossible⟩
  obtain ⟨published, values, _, covered, _⟩ :=
    generated.rawEventReplay_bufferedCoverage [produced, first] valid (by cbv)
  have noValues : (initial.rawEventReplay [produced, first]).2.flatMap
      WorkQueueEvent.objectValues = [] := by cbv
  have empty : published = [] := by
    apply List.map_eq_nil_iff.mp
    exact values.trans noValues
  subst published
  have suffix := covered.afterPrefix [produced] [first]
  have accounted := (createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated [produced] prior (by cbv)
  have conserved := suffix.conserves accounted.liveGroups accounted.taskGroups
    accounted.started (fun event member => valid.eachMatches
      (List.mem_append_right [produced] member))
  let node : TaskNode :=
    { task := ⟨producerTask, [root, child]⟩,
      value := some producerValue, childStreams := [stream.ref] }
  have found : (initial.replayGraphEvents [produced]).taskNode? producerTask
      = some node := by cbv
  have survivor : ∃ owner,
      ((initial.replayGraphEvents [produced]).replayGraphEvents [first]).groupNode?
        child.ref = some owner := by
    cases lookup
          : ((initial.replayGraphEvents [produced]).replayGraphEvents [first]).groupNode?
              child.ref with
    | none => cbv at lookup; cases lookup
    | some owner => exact ⟨owner, rfl⟩
  obtain ⟨owner, live⟩ := survivor
  rcases conserved producerTask node producerValue found rfl
      ⟨child, by simp [node], owner, live⟩ with impossible | retained
  · simp at impossible
  · exact ⟨node, retained, rfl⟩

/-- Later failure of co-owner R leaves the released stream's C dependency uncancelled.
Witness: general carrier health and retirement stability, for separated and aggregated
host batches. No fixture-specific uncancelledness or healthy-owner premise is supplied.
-/
theorem delayed_failure_owner_support
    : ∀ batches ∈ [[[produced], [finish], [first]], [[produced, finish, first]]],
        child.ref ∈ [root.ref, child.ref]
        ∧ (initial.runNormalized batches).1.RetiredGroup child.ref
        ∧ ¬GroupRecordInvalidated work
            (initial.objectFailureContributions batches.flatten) child.ref
        ∧ child.ref ∉ (initial.runNormalized batches).1.cancelledGroups := by
  intro batches member
  have choices : batches = [[produced], [finish], [first]]
      ∨ batches = [[produced, finish, first]] := by simpa using member
  have flat : batches.flatten = [produced, finish, first] := by
    rcases choices with rfl | rfl <;> rfl
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl <;> cbv
  have output : (initial.runNormalized batches).2.flatten = [
      .groupValues parent [parentValue], .groupSuccess parent [child] [],
      .groupValues child [producerValue], .groupSuccess child [] [stream],
      .groupFailure root 1] := by
    rcases choices with rfl | rfl <;> cbv
  have carrier : WorkQueueEvent.groupSuccess child [] [stream]
      ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten := by
    change WorkQueueEvent.groupSuccess child [] [stream] ∈ (initial.runNormalized batches).2.flatten
    rw [output]
    simp
  have valid := flat ▸ delayed_failure_inputs
  obtain ⟨_, _, retired, healthy, uncancelled⟩ :=
    generated.runNormalized_successfulCarrier_retiredHealthy valid started carrier
  exact ⟨(generated.runNormalized_streamHealthyDependency valid started carrier
    List.mem_cons_self streamKnown).1, retired, healthy, uncancelled⟩

-----------------------------------------------------------------------------------------
-- Actual publication readiness and later-item health reuse the derived release certificate
-----------------------------------------------------------------------------------------

/-- The actual first item after retained-producer release satisfies full publication readiness.
Witness: the existing joint output matching supplies freshness, item order, and producer
publication. The new replay-derived C guard discharges historical cancellation under
the nonempty R-failure inventory, without an assumed publication-support certificate.
This is `CanPublish`, not yet the complete event or general conformance statement.
-/
theorem first_item_ready
    : let outputs := (initial.runNormalized continued).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ CanPublish work matching (atoms.take 5) cuts (matching 5)
            (some producerTask) := by
  obtain ⟨matching, batching, _, items⟩ :=
    createWorkQueue_runNormalized_streamPublicationReadinessMatching generated
      continued_inputs.1 continued_inputs.2
  obtain ⟨value, producer, _, known, ready⟩ :=
    items 5 stream [⟨.scalar "x", 0⟩] [] [] (by cbv)
  obtain ⟨_, dependencies, descriptor⟩ := itemTask_owner_nodeAt known
  have same := generated.streamProducer_unique descriptor streamKnown rfl
  subst producer
  refine ⟨matching, batching, (ready cuts).mpr ?_⟩
  have healthy := released_stream_healthy matching
    (((initial.runNormalized continued).2.flatten.flatMap publicationAtoms).take 5)
  have success : TaskSucceeds work producerTask := ⟨_, _, _, producer_known, rfl⟩
  apply task_uncancelled_of_producerSafety failed_payloads
    (.child ⟨_, _, known⟩ success (.root ⟨_, _, producer_known⟩)) known
    List.mem_cons_self healthy.2
  intro parent same
  cases same
  exact healthy.1

/-- The earlier release certificate remains usable after the first item has settled.
Witness: durable retired-dependency health at a strictly longer accepted source prefix.
The earlier local safety theorem supplies that one successful item's induction premise;
the historical R failure remains in the cut inventory throughout the continuation.
-/
theorem released_stream_healthy_after_item
    (matching : PublicationMatching) (events : List WorkQueueEvent)
    : ¬TaskCancelled work matching events cuts producerTask
      ∧ ¬NodeFailed work matching events cuts stream.ref := by
  apply generated.replayGraphEvents_objectStreamHealthy_after_retirement
    continued_inputs.1 (by cbv) streamKnown
    (by
      simp [continued, first, produced, finish, next, producerTask, GraphEvent.successes])
    released_owner_support.1 (before := [first, produced, finish]) ⟨[next], rfl⟩
    released_owner_support.2.1 released_owner_support.2.2 failed_payloads
  · intro occurrence owners producer path result known member
    have same : occurrence = failedTask := by simpa [cuts, failedBefore] using member
    subst occurrence
    cbv
    exact List.mem_cons_self
  · intro address index member
    have same : Occurrence.item address index = item.occurrence := by
      simpa [continued, first, produced, finish, next, item, producerTask, parentTask,
        GraphEvent.successes]
        using member
    rw [same]
    have known : TaskAt work item.occurrence [stream.ref] (some producerTask)
        (.item stream (.ok (.scalar "x", 0))) :=
      ⟨stream, entries, [root.ref, child.ref], .ok (.scalar "x", 0), .empty,
        by cbv, rfl, rfl, rfl⟩
    have healthy := released_stream_healthy matching events
    have success : TaskSucceeds work producerTask := ⟨_, _, _, producer_known, rfl⟩
    apply task_uncancelled_of_producerSafety failed_payloads
      (.child ⟨_, _, known⟩ success (.root ⟨_, _, producer_known⟩)) known
      List.mem_cons_self healthy.2
    intro parent same
    cases same
    exact healthy.1
  · intro occurrence owners ⟨producer, payload, known⟩ owner member
    have same : occurrence = failedTask := by simpa [cuts, failedBefore] using member
    subst occurrence
    rw [(known.unique failed_known).1] at owner
    simp [root, stream] at owner

-----------------------------------------------------------------------------------------
-- A multi-item handler uses the common witness without assuming its own items safe
-----------------------------------------------------------------------------------------

private def secondItem : StreamItem :=
  { occurrence := .item [1, 1, 0, 0, 0, 1] 1, value := ⟨.null, 0⟩ }

private def twoItems : GraphEvent := .streamItems stream [item, secondItem]

/-- The retained stream may supply its first two items in one source event.
Witness: both exact item locations and the contiguous source cursor range, after the same
failure and recursive release prefix. No output-admission or cancellation premise is used.
-/
theorem two_item_inputs : ValidGraphEvents work [first, produced, finish, twoItems] := by
  have located : Located work [1, 1, 0, 0, 0, 1] (.stream stream entries)
      (some producerTask) [root.ref, child.ref] := by cbv
  apply ValidGraphEvents.append inputs_valid
  · intro supplied member
    have choices : supplied = item ∨ supplied = secondItem := by simpa [twoItems] using member
    rcases choices with rfl | rfl
    · exact ⟨[stream.ref], some producerTask,
        ⟨stream, entries, [root.ref, child.ref], .ok (.scalar "x", 0), .empty,
          located, rfl, rfl, rfl⟩, by cbv⟩
    · exact ⟨[stream.ref], some producerTask,
        ⟨stream, entries, [root.ref, child.ref], .ok (.null, 0), .empty,
          located, rfl, rfl, rfl⟩, by cbv⟩
  · simp [twoItems, item, secondItem, first, produced, finish, failedTask, producerTask,
      parentTask, GraphEvent.Fresh, GraphEvent.identities]
  · refine ⟨[1, 1, 0, 0, 0, 1], entries, some producerTask, [root.ref, child.ref],
      located, by simp, ?_, ?_, by cbv⟩
    · simp [first, produced, finish, GraphEvent.identities]
    · intro source same
      cases same
      simp [first, produced, finish, GraphEvent.successes]

/-- Both first-handler items are safe under the actual common mixed-failure witness.
Witness: the general boundary bridge recovers an item-free earlier source prefix for
both atoms, including the second atom of the same handler. Producer and stream health
then give prefix safety; each publication protects its item at later cuts. The actual
R failure is retained, for separate and aggregated host batching, not replaced by empty cuts.
-/
theorem two_items_canonical_safe
    : ∀ batches ∈
        [
          [[first], [produced], [finish], [twoItems]],
          [[first, produced, finish, twoItems]]
        ],
        ∃ w : ConformancePlan.Witness,
          w.events = initial.nonterminalAtoms batches
          ∧ ConformancePlan.BatchShape work batches w
          ∧ ConformancePlan.AnnouncedFailures work w
          ∧ w.failures ≠ []
          ∧ ∀ index ∈ [5, 6],
              ¬TaskCancelled work w.matching w.events w.failures (w.matching index) := by
  intro batches member
  have choices : batches = [[first], [produced], [finish], [twoItems]]
      ∨ batches = [[first, produced, finish, twoItems]] := by simpa using member
  have flat : batches.flatten = [first, produced, finish, twoItems] := by
    rcases choices with rfl | rfl <;> rfl
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl <;> cbv
  obtain ⟨w, history, shape, announced, values, _, boundaries⟩ :=
    ConformancePlan.objectStreamBoundaryCertificates generated (flat ▸ two_item_inputs) started
  have nonempty : w.failures ≠ [] := by
    intro empty
    have atFailure : w.events[0]? = some (.groupFailure root 1) := by
      rw [history]
      rcases choices with rfl | rfl <;> cbv
    obtain ⟨count, _, total⟩ := announced.1.2.2.2.1 0 root 1 atFailure
    simp [empty, failedBefore] at total
  refine ⟨w, history, shape, announced, nonempty, ?_⟩
  intro index member
  have position : index = 5 ∨ index = 6 := by simpa using member
  let value : StreamItemValue := { item := if index = 5 then .scalar "x" else .null }
  have selected : w.events[index]? = some (.streamValues stream [value] [] []) := by
    rw [history]
    rcases choices with rfl | rfl <;> rcases position with rfl | rfl <;> cbv
  obtain ⟨before, input, after, split, _, healthy⟩ := boundaries index
    (.streamValues stream [value] [] []) stream [root.ref, child.ref]
    [1, 1, 0] false selected streamKnown rfl (by intros; intro impossible; cases impossible)
  have earlierLength : before.length ≤ 3 := by
    have sizes := congrArg List.length split
    rw [flat] at sizes
    simp only [List.length_append, List.length_cons, List.length_nil] at sizes
    omega
  have earlier : before.Subset [first, produced, finish] := by
    have same : before = batches.flatten.take before.length := by rw [split]; simp
    rw [same]
    have included := List.take_subset_take_left batches.flatten earlierLength
    intro event member
    simpa only [flat, List.take_succ_cons, List.take_zero] using included member
  have health := healthy (by
    intro address ordinal success
    obtain ⟨source, member, settled⟩ := List.mem_flatMap.mp success
    have observed := List.mem_flatMap.mpr ⟨source, earlier member, settled⟩
    simp [first, produced, finish, GraphEvent.successes, producerTask, parentTask] at observed)
  obtain ⟨owners, producer, descriptor⟩ := (values index _ selected trivial).1
  obtain ⟨ownerEq, dependencies, located⟩ := itemTask_owner_nodeAt descriptor
  have parentEq := generated.streamProducer_unique located streamKnown rfl
  subst owners producer
  apply uncancelled_of_safe_publication selected trivial rfl
  apply task_uncancelled_of_producerSafety
    (fun cut occurrence included => (announced.1.2.2.1 (cut, occurrence) included).2.2)
    (.child ⟨_, _, descriptor⟩ ⟨_, _, _, producer_known, rfl⟩
      (.root ⟨_, _, producer_known⟩))
    descriptor List.mem_cons_self health.2
  intro parent same
  cases same
  exact health.1

/-- General item safety covers both retained-stream items under either host batching.
Witness: instantiate the mixed successful-item certificates directly, without supplying
an item-free boundary, lineage, or cancellation premise. The actual R failure is retained.
-/
theorem two_items_general_certificates
    : ∀ batches ∈
        [
          [[first], [produced], [finish], [twoItems]],
          [[first, produced, finish, twoItems]]
        ],
        ∃ w : ConformancePlan.Witness,
          w.events = initial.nonterminalAtoms batches
          ∧ ConformancePlan.BatchShape work batches w
          ∧ ConformancePlan.AnnouncedFailures work w
          ∧ ConformancePlan.SuccessfulItemsSafe work batches.flatten w
          ∧ w.failures ≠ []
          ∧ ¬TaskCancelled work w.matching w.events w.failures item.occurrence
          ∧ ¬TaskCancelled work w.matching w.events w.failures secondItem.occurrence := by
  intro batches member
  have choices : batches = [[first], [produced], [finish], [twoItems]]
      ∨ batches = [[first, produced, finish, twoItems]] := by simpa using member
  have flat : batches.flatten = [first, produced, finish, twoItems] := by
    rcases choices with rfl | rfl <;> rfl
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl <;> cbv
  obtain ⟨w, history, shape, announced, safe⟩ :=
    ConformancePlan.successfulItemCertificates generated (flat ▸ two_item_inputs) started
  refine ⟨w, history, shape, announced, safe, ?_, ?_, ?_⟩
  · intro empty
    have atFailure : w.events[0]? = some (.groupFailure root 1) := by
      rw [history]
      rcases choices with rfl | rfl <;> cbv
    obtain ⟨count, _, total⟩ := announced.1.2.2.2.1 0 root 1 atFailure
    simp [empty, failedBefore] at total
  · apply safe _ _
    simp [flat, first, produced, finish, twoItems, item, GraphEvent.successes]
  · apply safe _ _
    simp [flat, first, produced, finish, twoItems, secondItem, GraphEvent.successes]

/-- Both retained-stream items now satisfy full admission under either host batching.
Witness: one canonical licensed history supplies stream readiness and unique healthy
ownership, including the predecessor publication for the second item. Their actual
events carry no child notices, so the remaining announcement clauses are empty.
-/
theorem two_items_admitted
    : ∀ batches ∈
        [
          [[first], [produced], [finish], [twoItems]],
          [[first, produced, finish, twoItems]]
        ],
        ∃ w : ConformancePlan.Witness,
          w.events = initial.nonterminalAtoms batches
          ∧ ConformancePlan.BatchShape work batches w
          ∧ FailureWitness work (ConformancePlan.initialRefs work)
              w.matching w.events w.failures
          ∧ ∀ index ∈ [5, 6],
              EventAllowed work (ConformancePlan.initialRefs work) w.matching
                (w.events.take index) w.failures
                (.streamValues stream
                  [{ item := if index = 5 then .scalar "x" else .null }] [] []) := by
  intro batches member
  have choices : batches = [[first], [produced], [finish], [twoItems]]
      ∨ batches = [[first, produced, finish, twoItems]] := by simpa using member
  have flat : batches.flatten = [first, produced, finish, twoItems] := by
    rcases choices with rfl | rfl <;> rfl
  have started : inputsStarted work batches = true := by
    rcases choices with rfl | rfl <;> cbv
  obtain ⟨w, history, shape, announced, uncancelled, _, _, ready⟩ :=
    ConformancePlan.mixed_eventCertificates generated (flat ▸ two_item_inputs) started
  refine ⟨w, history, shape, ConformancePlan.failureWitness announced uncancelled, ?_⟩
  intro index member
  apply ConformancePlan.streamValueAllowed_without_notices ready
  have position : index = 5 ∨ index = 6 := by simpa using member
  rw [history]
  rcases choices with rfl | rfl <;> rcases position with rfl | rfl <;> cbv

/-- The parent and recursively drained child close while open and remain healthy.
Witness: actual same-handler notices supply child openness; durable group health shares
the canonical mixed witness with the earlier R failure and both later item publications.
Task accounting and notice eligibility are not assumed or claimed by this regression.
-/
theorem successful_groups_open_and_healthy
    : ∃ w : ConformancePlan.Witness,
        w.events = initial.nonterminalAtoms [[first, produced, finish, twoItems]]
        ∧ ConformancePlan.BatchShape work [[first, produced, finish, twoItems]] w
        ∧ FailureWitness work (ConformancePlan.initialRefs work)
            w.matching w.events w.failures
        ∧ Open (ConformancePlan.initialRefs work) (w.events.take 2) parent.ref
        ∧ Open (ConformancePlan.initialRefs work) (w.events.take 4) child.ref
        ∧ ¬NodeFailed work w.matching w.events w.failures parent.ref
        ∧ ¬NodeFailed work w.matching w.events w.failures child.ref := by
  let batches := [[first, produced, finish, twoItems]]
  obtain ⟨w, history, shape, announced, uncancelled, _, _, _, healthy⟩ :=
    ConformancePlan.mixed_groupHealthCertificates (inputs := batches) generated two_item_inputs
      (by cbv)
  have parentAt : w.events[2]? = some (.groupSuccess parent [child] []) := by
    rw [history]
    cbv
  have childAt : w.events[4]? = some (.groupSuccess child [] [stream]) := by
    rw [history]
    cbv
  refine ⟨w, history, shape, ConformancePlan.failureWitness announced uncancelled,
    ?_, ?_, healthy 2 parent [child] [] parentAt, healthy 4 child [] [stream] childAt⟩
  · obtain ⟨selected, beforeEq⟩ := ConformancePlan.Witness.canonical_event history parentAt
    have opened := createWorkQueue_runNormalized_groupClosureOpenAt (batches := batches)
      generated two_item_inputs selected List.mem_cons_self
    dsimp only at opened
    rwa [beforeEq] at opened
  · obtain ⟨selected, beforeEq⟩ := ConformancePlan.Witness.canonical_event history childAt
    have opened := createWorkQueue_runNormalized_groupClosureOpenAt (batches := batches)
      generated two_item_inputs selected List.mem_cons_self
    dsimp only at opened
    rwa [beforeEq] at opened

/-- C's retained producer had a real storing boundary despite R's earlier failure.
Witness: apply the general root-contributor processing theorem to C's actual later
carrier; the source split and healthy task guard are derived, not supplied assumptions.
-/
theorem retained_success_processed
    : ∃ earlier result later node,
        [first, produced, finish] = earlier ++ .taskSuccess producerTask result :: later
        ∧ (initial.replayGraphEvents earlier).taskNode? producerTask = some node
        ∧ (initial.replayGraphEvents earlier).taskHasHealthyOwner node.task = true := by
  have known : TaskAt work producerTask [root.ref, child.ref] none
      (.object [] (.ok (producerValue.data, 0))) :=
    ⟨[⟨root, []⟩, ⟨child, [parent]⟩], [], .ok (producerValue.data, 0), children, [],
      rfl, rfl, rfl⟩
  exact generated.successfulCarrier_rootContributor_processed
    (before := [first, produced])
    (event := finish)
    (group := child)
    (groups := [])
    (streams := [stream])
    inputs_valid
    (by cbv)
    (by
      cbv
      exact List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    known
    (by simp)

/-- The retained producer publishes before C closes on the licensed mixed failure witness.
Witness: general atomic carrier coverage transports the same canonical ledger through
batching and normalization. No concrete raw prefix count, registry entry, or buffer lookup
is supplied. Every structural contributor is also accounted for at C's carrier.
-/
theorem closure_ledger_shared_failure_witness
    : ∃ w : ConformancePlan.Witness,
        w.events
          = (ConformancePlan.initialQueue work).nonterminalAtoms
              [[first, produced, finish, twoItems]]
        ∧ ConformancePlan.BatchShape work [[first, produced, finish, twoItems]] w
        ∧ FailureWitness work (ConformancePlan.initialRefs work) w.matching w.events
            w.failures
        ∧ ConformancePlan.GroupSuccessesHealthy work w
        ∧ ConformancePlan.BufferedClosureLedger work [[first, produced, finish, twoItems]]
            w
        ∧ NodeAccounted work w.matching (w.events.take 4) w.failures child.ref
        ∧ Published w.matching (w.events.take 4) producerTask := by
  let batches := [[first, produced, finish, twoItems]]
  obtain ⟨w, history, shape, announced, uncancelled, _, _, _, healthy, accounted, ledger⟩ :=
    ConformancePlan.mixed_groupAccountingCertificates (inputs := batches)
      generated two_item_inputs (by cbv)
  have selected : w.events[4]? = some (.groupSuccess child [] [stream]) := by
    rw [history]
    cbv
  refine ⟨w, history, shape, ConformancePlan.failureWitness announced uncancelled,
    healthy, ledger, accounted _ _ _ _ selected, ?_⟩
  exact ConformancePlan.groupSuccess_objectContributorsPublished (inputs := batches)
    generated two_item_inputs (by cbv) history ledger selected producer_known (by simp)

/-- Retained stream release and a later multi-item carrier keep every announced stream
active or completed. Witness: general raw replay tracking, without assuming output admission.
-/
theorem retained_stream_notices_tracked
    : StreamNoticeCompletion initial.rootStreams
        (initial.rawEventReplay [first, produced, finish, twoItems]) :=
  initial.rawEventReplay_streamNoticeCompletion _

/-- Completing all three items and their retained stream closes every stream notice.
Witness: the generic terminal theorem, with concrete start checks and an empty final root
set after the stream-success input. Earlier shared-owner failure does not erase the notice.
-/
theorem retained_stream_terminal_completions
    : let last : StreamItem :=
        { occurrence := .item [1, 1, 0, 0, 0, 1] 2, value := ⟨.scalar "z", 0⟩ }
      let events :=
        [
          first,
          produced,
          finish,
          .streamItems stream [item, secondItem, last],
          .streamSuccess stream
        ]
      ∀ ref ∈
        initial.initialStreams.map DeliveryNode.ref
        ++ (initial.rawEventReplay events).2.flatMap rawStreamNoticeRefs,
        ref ∈ (initial.rawEventReplay events).2.flatMap rawStreamClosureRefs := by
  intro last events ref announced
  exact createWorkQueue_terminalStreamCompleted (inputs := [events])
    (by cbv) (by cbv) announced

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerRetainedStreamRelease
