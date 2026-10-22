import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TerminalReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A shared success can register a child after its failed parent has been removed. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerLateFailedParent
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated shared work and the concrete late-registration replay
-----------------------------------------------------------------------------------------

private def p : DeliveryNode := ⟨0, [], some (.string "P")⟩
private def q : DeliveryNode := ⟨1, [], some (.string "Q")⟩
private def r : DeliveryNode := ⟨2, [], some (.string "R")⟩
private def s : DeliveryNode := ⟨3, [], some (.string "S")⟩
private def c : DeliveryNode := ⟨4, [.field "user"], some (.string "C")⟩
private def d : DeliveryNode := ⟨5, [.field "user"], some (.string "D")⟩
private def pTask : Occurrence := .executionGroup [1, 0]
private def uTask : Occurrence := .executionGroup [1, 1, 0]
private def xTask : Occurrence := .executionGroup [1, 1, 0, 0, 0, 1, 0]
private def yTask : Occurrence := .executionGroup [1, 1, 0, 0, 0, 1, 1, 0]
private def qTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def rTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def userData : List (Name × ResponseValue) := [("user", .object [])]
private def keepData : List (Name × ResponseValue) := [("keepQ", .scalar "a")]

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.combine
        (.executionGroup [⟨c, [p]⟩, ⟨d, [q]⟩, ⟨r, []⟩] [.field "user"]
          ({ result := .error 1, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨d, [q]⟩, ⟨s, []⟩] [.field "user"]
            ({ result := .error 1, cause := some 1 }) .empty)
          .empty)))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨p, []⟩] [] ({ result := .error 1, cause := some 1 }) .empty)
      (.combine
        (.executionGroup [⟨p, []⟩, ⟨q, []⟩, ⟨r, []⟩, ⟨s, []⟩] []
          ({ result := .ok (userData, 0) }) children)
        (.combine
          (.executionGroup [⟨q, []⟩] [] ({ result := .ok (keepData, 0) })
            (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨r, []⟩] [] ({ result := .error 2, cause := some 1 })
              .empty)
            .empty))))

private def killP : GraphEvent := .taskFailure pTask 1
private def killY : GraphEvent := .taskFailure yTask 1
private def killR : GraphEvent := .taskFailure rTask 1
private def killX : GraphEvent := .taskFailure xTask 1

private def expand : GraphEvent :=
  .taskSuccess uTask
    {
      value :=
        { path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] }
      work := Work.fromExecution children [1, 1, 0, 0]
    }

private def finish : GraphEvent :=
  .taskSuccess qTask
    {
      value := { path := [], data := keepData, errors := 0, deliveryGroups := [q] }
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def inputs : List (List GraphEvent) :=
  [[killP], [expand], [killY], [killR], [killX], [finish]]

private def rejectedOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure p 1],
    [.groupFailure s 1],
    [.groupFailure r 2],
    [
      .groupValues q
        [{ path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] }],
      .groupValues q
        [{ path := [], data := keepData, errors := 0, deliveryGroups := [q] }],
      .groupSuccess q [d] [],
      .groupFailure d 2,
      .workQueueTermination
    ]
  ]

private def correctedOutputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure p 1],
    [.groupFailure s 1],
    [.groupFailure r 1],
    [
      .groupValues q
        [{ path := [], data := userData, errors := 0, deliveryGroups := [p, q, r, s] }],
      .groupValues q
        [{ path := [], data := keepData, errors := 0, deliveryGroups := [q] }],
      .groupSuccess q [d] [],
      .groupFailure d 1,
      .workQueueTermination
    ]
  ]

/-- Pure query execution generates every task and ancestor in this fixture.
Witness: shared user selections create C/D/R and D/S tasks; R also owns a two-error task.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "pBad"),
      field "user" [defer [field "required" [] [] (some "x")] (some "C")]] (some "P"),
     defer [field "a" [] [] (some "keepQ"),
      field "user" [defer [field "required" [] [] (some "x"),
        field "required" [] [] (some "y")] (some "D")]] (some "Q"),
     defer [field "required" [] [] (some "rBad"), field "required" [] [] (some "rBad2"),
      field "user" [field "required" [] [] (some "x")]] (some "R"),
     defer [field "user" [field "required" [] [] (some "y")]] (some "S")], ?_⟩
  cbv

/-- P's private failure descriptor. Witness: the root task's structural address. -/
private theorem p_known : TaskAt work pTask [p.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

/-- P's first failure establishes causal support for every ref it cancels.
Witness: the general handler theorem with generated parent metadata and actual task
registration; no admitted output or presumed final cancellation state is used. -/
theorem first_failure_cancellation_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).handleGraphEvent killP).1 work
        [pTask] := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  apply State.CancelledRecordsSupported.handleGraphEvent
    (createWorkQueue_cancelledRecordsSupported _ _ _)
    (createWorkQueue_cachedFailuresSupported _ _ _)
    (createWorkQueue_startedTasksRegistered _)
    (createWorkQueue_fromSpec_registeredTasksMatch _)
    (createWorkQueue_groupNodesMatchWork _)
    (createWorkQueue_childLinksCanonical _ parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical
          (Located.root (root := work)) canonical member))
    canonical killP ⟨_, _, _, p_known⟩
  intro occurrence errors same _ _
  have equal : occurrence = pTask := by cases same; rfl
  simp [equal]

/-- The shared producer descriptor. Witness: its four root owners and fixed user value. -/
private theorem u_known
    : TaskAt work uTask [p.ref, q.ref, r.ref, s.ref] none
        (.object [] (.ok (userData, 0))) :=
  ⟨_, [], { result := .ok (userData, 0) }, children, [], rfl, rfl, rfl⟩

/-- X's descriptor. Witness: the first nested failure under the shared producer. -/
private theorem x_known
    : TaskAt work xTask [c.ref, d.ref, r.ref] (some uTask)
        (.object [.field "user"] (.error 1)) :=
  ⟨_, _, { result := .error 1, cause := some 1 }, .empty, _, rfl, rfl, rfl⟩

/-- Y's descriptor. Witness: the second nested failure under the shared producer. -/
private theorem y_known
    : TaskAt work yTask [d.ref, s.ref] (some uTask)
        (.object [.field "user"] (.error 1)) :=
  ⟨_, _, { result := .error 1, cause := some 1 }, .empty, _, rfl, rfl, rfl⟩

/-- Q's remaining success descriptor. Witness: its root address and fixed scalar value. -/
private theorem q_known
    : TaskAt work qTask [q.ref] none (.object [] (.ok (keepData, 0))) :=
  ⟨_, [], { result := .ok (keepData, 0) }, .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- R's private two-error descriptor. Witness: the last root task's structural address. -/
private theorem r_known : TaskAt work rTask [r.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 2, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

/-- Every settlement matches its fixed outcome, is fresh, and follows its producer.
Witness: six source-extension steps; the nested failures follow the shared user success.
-/
theorem source_valid : ValidGraphEvents work inputs.flatten := by
  have zero : ValidGraphEvents work [killP] :=
    .append .nil ⟨_, _, _, p_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP])
      ⟨_, _, _, p_known, by intro source impossible; cases impossible⟩
  have one : ValidGraphEvents work [killP, expand] :=
    .append zero ⟨_, _, u_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, pTask, uTask])
      ⟨_, _, _, u_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [killP, expand, killY] :=
    .append one ⟨_, _, _, y_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY,
        pTask, uTask, yTask])
      ⟨_, _, _, y_known, by simp [GraphEvent.successes, killP, expand]⟩
  have three : ValidGraphEvents work [killP, expand, killY, killR] :=
    .append two ⟨_, _, _, r_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR,
        pTask, uTask, yTask, rTask])
      ⟨_, _, _, r_known, by intro source impossible; cases impossible⟩
  have four : ValidGraphEvents work [killP, expand, killY, killR, killX] :=
    .append three ⟨_, _, _, x_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR, killX,
        pTask, uTask, yTask, rTask, xTask])
      ⟨_, _, _, x_known, by simp [GraphEvent.successes, killP, expand, killY, killR]⟩
  exact .append four ⟨_, _, q_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR, killX,
      finish, pTask, uTask, yTask, rTask, xTask, qTask])
    ⟨_, _, _, q_known, by intro source impossible; cases impossible⟩

/-- The actual start checker accepts all six settlements, including the late failure.
Witness: executable initialization and replay; X was started through R before R failed.
-/
theorem inputs_started : inputsStarted work inputs = true := by cbv

/-- Presence accepts X's late rejection as well as the three earlier source failures.
Witness: the projection follows every actual handler boundary.
-/
theorem accepted_failure_inventory
    : (State.initialize (Work.fromExecution work)).objectFailureContributions
        inputs.flatten
      = [xTask, rTask, yTask, pTask] := by cbv

/-- Every cancellation in the complete split-batch replay has an accepted failure cause.
Witness: generated replay covers late registration and the retained-rejection drain
under the complete received-failure inventory. -/
theorem replay_cancellation_supported
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.CancelledRecordsSupported
        work [xTask, rTask, yTask, pTask] := by
  have supported := generated.runNormalized_cancelledRecordsSupported inputs source_valid
    inputs_started
  simpa only [accepted_failure_inventory] using supported

/-- Joined input batching derives the same complete cancellation inventory.
Witness: start discipline for the joined batch and general normalized replay support. -/
theorem joined_cancellation_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).runNormalized [inputs.flatten]).1
        work [xTask, rTask, yTask, pTask] := by
  have valid : ValidGraphEvents work [inputs.flatten].flatten := by
    simpa using source_valid
  have supported := generated.runNormalized_cancelledRecordsSupported [inputs.flatten]
    valid (by cbv)
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil,
    accepted_failure_inventory]
    using supported

/-- The queue emits P1, S1, R1, then announces D and replays one registered rejection.
Witness: executable queue and publisher replay, including the final termination marker.
-/
theorem output
    : let queue := State.initialize (Work.fromExecution work)
      queue.initialGroups = [p, q, r, s]
      ∧ queue.initialStreams = []
      ∧ (queue.runNormalized inputs).2 = correctedOutputs := by cbv

/-- P's retirement blocks late registration of C and prevents its use as a healthy owner.
Witness: replay up to X's settlement retains cancellation refs for both P and C.
-/
theorem late_child_stays_cancelled
    : let before :=
        ((State.initialize (Work.fromExecution work)).runNormalized (inputs.take 4)).1
      before.groupNode? p.ref = none
      ∧ before.groupNode? c.ref = none
      ∧ before.cancelledGroups.contains p.ref = true
      ∧ before.cancelledGroups.contains c.ref = true
      ∧ before.cancelledGroups.contains c.ref = true := by cbv

/-- The same correction holds when the host supplies all settlements in one batch.
Witness: executable replay preserves the corrected atomic outputs under joined input.
-/
theorem joined_output
    : ((State.initialize (Work.fromExecution work)).runNormalized [inputs.flatten]).2
      = [correctedOutputs.flatten] := by cbv

/-- C's cancellation does not discard X while another contributing owner is healthy.
Witness: after the shared success, D and R still admit X's settlement and R closes.
-/
theorem healthy_coowner_preserved
    : let before :=
        ((State.initialize (Work.fromExecution work)).runNormalized (inputs.take 2)).1
      (before.taskNode? xTask).isSome = true
      ∧ (before.taskFailure xTask 1).2 = [.groupFailure r 1] := by cbv

private def grandchild : DeliveryNode := ⟨6, [.field "user"], none⟩

/-- A refused child carries cancellation onward to later grandchildren.
Witness: two successive registrations after P's failed retirement install no live nodes.
-/
theorem transitive_late_registration
    : let retired : State := { registeredGroups := [p.ref], cancelledGroups := [p.ref] }
      let next := (retired.addGroup ⟨c, some p.ref⟩).addGroup ⟨grandchild, some c.ref⟩
      next.groupNodes = []
      ∧ next.cancelledGroups.contains grandchild.ref = true
      ∧ next.registeredGroups.contains grandchild.ref = true := by cbv

/-- Refusal permanently retires C, regardless of any later host events or batching.
Witness: the general refused-child retirement theorem, not finite trace enumeration. -/
theorem late_child_never_recreated (later : List (List GraphEvent))
    : let retired : State := { registeredGroups := [p.ref], cancelledGroups := [p.ref] }
      (((retired.addGroup ⟨c, some p.ref⟩).runNormalized later).1.groupNode? c.ref)
      = none := by
  apply State.addGroup_cancelled_child_never_recreated
  · simp [p, c]
  · rfl
  · rfl
  · simp

/-- Candidate order cannot hide the subsequently discovered cancellation of a parent.
Witness: register a grandchild first, then retire C; its retained parent link records the cancellation boundary.
-/
theorem child_first_registration
    : let retired : State := { registeredGroups := [p.ref], cancelledGroups := [p.ref] }
      let next := (retired.addGroups [⟨grandchild, some c.ref⟩, ⟨c, some p.ref⟩]).1
      next.groupNode? c.ref = none
      ∧ next.cancelledGroups.contains c.ref = true
      ∧ (next.groupNode? grandchild.ref).map (fun node => node.group.parent)
        = some (some c.ref) := by cbv

/-- Initialization of the generated fixture does not invent a cancelled group.
Witness: the general initialization equation, independent of outcomes and source order. -/
theorem initialization_has_no_cancellations
    : (State.initialize (Work.fromExecution work)).cancelledGroups = [] :=
  createWorkQueue_cancelledGroups_empty _

/-- Closing P successfully neither adds P nor forgets any earlier cancellation refs.
Witness: the general successful-closure equation for an arbitrary retained history. -/
theorem successful_retirement_keeps_cancellations (prior : NodeRefs)
    : let parent : GroupNode := { group := ⟨p, none⟩ }
      let queue : State :=
        {
          registeredGroups := [p.ref],
          cancelledGroups := prior,
          rootGroups := [p.ref],
          groupNodes := [parent]
        }
      (queue.finishGroupSuccess parent).1.cancelledGroups = prior := by
  exact State.finishGroupSuccess_cancelledGroups _ _

/-- Successful removal preserves an uncancelled registration boundary.
Witness: successful group closure and empty-group pruning leave no cancellation ref.
-/
theorem successful_retirement_preserved
    : let parent : GroupNode := { group := ⟨p, none⟩ }
      let initial : State :=
        { registeredGroups := [p.ref], rootGroups := [p.ref], groupNodes := [parent] }
      let closed := (initial.finishGroupSuccess parent).1
      let pruned := (initial.pruneEmptyGroups [p]).1
      (closed.addGroup ⟨c, some p.ref⟩).cancelledGroups = []
      ∧ (closed.addGroup ⟨c, some p.ref⟩).groupNode? c.ref ≠ none
      ∧ (pruned.addGroup ⟨c, some p.ref⟩).cancelledGroups = []
      ∧ (pruned.addGroup ⟨c, some p.ref⟩).groupNode? c.ref ≠ none := by cbv; simp

/-- Failure retirement remembers both existing descendants and the removed ancestor.
Witness: traverse P/C and reject a subsequently arriving grandchild of C.
-/
theorem existing_descendants_retired
    : let initial := (({} : State).addGroups [⟨p, none⟩, ⟨c, some p.ref⟩]).1
      let retired := initial.removeGroup p.ref
      retired.cancelledGroups.contains p.ref = true
      ∧ retired.cancelledGroups.contains c.ref = true
      ∧ (retired.addGroup ⟨grandchild, some c.ref⟩).groupNode? grandchild.ref = none := by
  cbv

private theorem c_known : NodeAt work c .group [p.ref] (some uTask) :=
  ⟨
    [1, 1, 0, 0, 0, 1, 0],
    _,
    _,
    { result := .error 1, cause := some 1 },
    .empty,
    _,
    ⟨c, [p]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- Late registration propagates P's actual failure to C's retained cancellation ref.
Witness: structural parent metadata instantiates the general provenance-preservation proof.
-/
theorem late_child_cancellation_supported
    : let retired : State := { registeredGroups := [p.ref], cancelledGroups := [p.ref] }
      (retired.addGroups [⟨c, some p.ref⟩]).1.CancelledGroupsSupported work [pTask] := by
  apply State.CancelledGroupsSupported.addGroups
  · intro ref member
    have same : ref = p.ref := List.mem_singleton.mp member
    subst ref
    exact .task ⟨none, .object [] (.error 1), p_known⟩ (by simp) (by simp)
  · intro group member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[p.ref], some uTask, c_known, rfl⟩

private def NodesAssigned (assigned : Nat → DeliveryNode) : Execution.Work → Prop
  | .empty => True
  | .combine left right => NodesAssigned assigned left ∧ NodesAssigned assigned right
  | .executionGroup groups _ _ nested =>
      (∀ group ∈ groups, group.node = assigned group.node.ref)
      ∧ NodesAssigned assigned nested
  | .stream .. => False

/-- Structural navigation preserves the node assignment. Witness: navigation induction. -/
private theorem NodesAssigned.located {assigned root address current producer owners}
    (assignment : NodesAssigned assigned root)
    (located : Located root address current producer owners)
    : NodesAssigned assigned current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact assignment
  | left prior ih => exact ih.1
  | right prior ih => exact ih.2
  | executionGroup prior ih => exact ih.2
  | item prior entry ih => exact False.elim ih

/-- Each descriptor agrees with its assigned node. Witness: its located group occurrence. -/
private theorem NodesAssigned.node {assigned work node kind dependencies producer}
    (assignment : NodesAssigned assigned work)
    (known : NodeAt work node kind dependencies producer)
    : node = assigned node.ref := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member => exact (assignment.located located.toCurrent).1 _ member
  | stream located => exact False.elim (assignment.located located.toCurrent)

/-- Repeated group refs have identical full node metadata throughout this generated work.
Witness: a six-node assignment is preserved by structural navigation to every descriptor.
-/
theorem node_refs_coherent : NodeRefCoherent work := by
  let assigned (ref : NodeRef) :=
    if ref = 0 then p else if ref = 1 then q else if ref = 2 then r else
      if ref = 3 then s else if ref = 4 then c else d
  have assignment : NodesAssigned assigned work := by
    simp [NodesAssigned, assigned, work, children, p, q, r, s, c, d]
  intro first firstKind firstDeps firstProducer second secondKind secondDeps secondProducer
    firstKnown secondKnown same
  rw [assignment.node firstKnown, assignment.node secondKnown, same]

/-- The four initial notices are legal, root-produced groups with outstanding work.
Witness: all four own the shared producer, which is not initially accounted for.
-/
theorem initialized
    : let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams := by
  have eligible {node : DeliveryNode} (owner : node.ref ∈ [p.ref, q.ref, r.ref, s.ref])
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩, by simp, by simp⟩
    intro accounted
    rcases accounted uTask _ ⟨_, _, u_known⟩ owner with cancelled | published
    · simp [TaskCancelled] at cancelled
    · simp [Published] at published
  have known {node : DeliveryNode} (member : node ∈ [p, q, r, s])
      : NodeAt work node .group [] none := by
    refine ⟨[1, 1, 0], _, [], { result := .ok (userData, 0) }, children, [], ⟨node, []⟩,
      rfl, ?_, rfl, rfl⟩
    simpa only [List.mem_cons, List.not_mem_nil, or_false, DeferredFragment.mk.injEq,
      and_true] using member
  change Initializes work [p, q, r, s] []
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  refine ⟨[], none, known member, eligible ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> simp

private def source : EventSource (List GraphEvent) :=
  { admissible := fun batches => batches.IsPrefix inputs, finished := fun _ => False }

/-- An opaque prefix source supplies this replay under every existing source law.
Witness: source admission is prefix closure of the checked fixed-outcome input trace.
-/
theorem source_validGraphEvents
    : ∀ batches, source.admissible batches → ValidGraphEvents work batches.flatten := by
  intro batches admitted
  obtain ⟨tail, same⟩ := admitted
  apply source_valid.prefix
  exact ⟨tail.flatten, by rw [← List.flatten_append, ← same]⟩

/-- Every admitted input prefix settles only started tasks before termination.
Witness: evaluate the unchanged start checker at each of the seven source prefixes.
-/
theorem source_respectsStarts
    : ∀ batches, source.admissible batches → inputsStarted work batches = true := by
  intro batches admitted
  change batches.IsPrefix inputs at admitted
  have same := List.prefix_iff_eq_take.mp admitted
  have bound : batches.length ≤ 6 := admitted.length_le
  have lengths : batches.length = 0 ∨ batches.length = 1 ∨ batches.length = 2
      ∨ batches.length = 3 ∨ batches.length = 4 ∨ batches.length = 5
      ∨ batches.length = 6 := by omega
  rcases lengths with length | length | length | length | length | length | length
    <;> rw [same, length] <;> cbv

/-- This source satisfies both graph-event validity and actual-start admission.
Witness: the checked prefixes of its fixed finite input trace.
-/
theorem source_conforms : source.ValidFor work :=
  ⟨
    rfl,
    ⟨inputs, rfl⟩,
    fun _ _ before after => before.trans after,
    fun batches admitted =>
      ⟨source_validGraphEvents batches admitted, source_respectsStarts batches admitted⟩
  ⟩

/-- The corrected implementation no longer emits the rejected completion counts.
Witness: exact replay reports one error for D; the former trace reports two.
-/
theorem runner_avoids_rejected_output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      ≠ rejectedOutputs := by
  rw [output.2.2]
  simp [correctedOutputs, rejectedOutputs]

/-- No batching, matching or failure inventory can justify D's invented aggregate count. -/
theorem output_not_valid : ¬ValidHistory work ⟨[p, q, r, s], [], rejectedOutputs⟩ := by
  have excludes {events matching failures} (explained : Explains work [p, q, r, s] []
      events matching failures) : .groupFailure d 2 ∉ events := by
    intro member
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    have allowed := explained.2.2 index _ selected
    have count := generated.nodeFailureCause_count allowed.2.2.2
    omega
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · exact excludes explained ((batching.control_mem (by simp [IsValue])).mp
      (by simp [rejectedOutputs]))
  · have member := (batching.control_mem (event := .groupFailure d 2) (by simp [IsValue])).mp
      (by simp [rejectedOutputs])
    exact excludes explained (List.mem_append.mp member |>.resolve_right (by simp))

/-- Canonical accounting admits and terminates the actual six-settlement replay. -/
theorem actual_output_admitted
    : AdmissibleRun work
        ((ConformancePlan.initialQueue work).normalizedHistory inputs) := by
  have nonempty : work.size ≠ 0 := by decide
  obtain ⟨w, obligations⟩ := ConformancePlan.replayWitnessExists_holds work inputs
    ⟨nonempty, generated, initialized, source_valid, inputs_started⟩
  have explained := ConformancePlan.explains initialized obligations.announced
    obligations.uncancelled obligations.publications obligations.controls
  exact (ConformancePlan.run_iff_terminated explained obligations.batching
          (fun ended =>
            ConformancePlan.terminal (obligations.tasks ended)
              (obligations.nodes ended) (obligations.reported ended))).mpr
    (by cbv)

#print axioms actual_output_admitted
#print axioms output_not_valid

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerLateFailedParent
