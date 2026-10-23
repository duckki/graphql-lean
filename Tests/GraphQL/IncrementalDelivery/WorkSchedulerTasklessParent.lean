import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TerminalReporting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupInvalidation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyCounterReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupSupportReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GeneratedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformanceFailureHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureLicensing
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeferGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducerSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorCertificates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplayClosure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeferFailureWitness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality
import Tests.GraphQL.IncrementalDelivery.Execution
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Taskless-parent cancellation: corrected replay and rejection of the former error count. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerTasklessParent
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
private def e : DeliveryNode := ⟨4, [.field "user"], some (.string "E")⟩
private def c : DeliveryNode := ⟨5, [.field "user"], some (.string "C")⟩
private def d : DeliveryNode := ⟨6, [.field "user"], some (.string "D")⟩
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
      (.declareGroups [⟨e, [p]⟩, ⟨c, [e, p]⟩, ⟨d, [q]⟩]
        (.combine
          (.executionGroup [⟨c, [e, p]⟩, ⟨d, [q]⟩, ⟨r, []⟩] [.field "user"]
            ({ result := .error 1, cause := some 1 }) .empty)
          (.combine
            (.executionGroup [⟨d, [q]⟩, ⟨s, []⟩] [.field "user"]
              ({ result := .error 1, cause := some 1 }) .empty)
            .empty))))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.declareGroups [⟨p, []⟩, ⟨q, []⟩, ⟨r, []⟩, ⟨s, []⟩]
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
              .empty)))))

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

private def notice : GraphEvent := .groupFailure ⟨d, 2⟩

private def inputs : List (List GraphEvent) :=
  [[killP], [expand], [killY], [killR], [killX], [finish, notice]]

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
      .groupFailure d 3,
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
      .groupFailure d 2,
      .workQueueTermination
    ]
  ]

/-- Pure query execution generates every task and ancestor in this fixture.
Witness: shared user selections create C/D/R and D/S tasks; R also owns a two-error task.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required" [] [] (some "pBad"),
      field "user" [defer [defer [field "required" [] [] (some "x")]
        (some "C")] (some "E")]] (some "P"),
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
  have five : ValidGraphEvents work [killP, expand, killY, killR, killX, finish] :=
    .append four ⟨_, _, q_known, rfl, rfl⟩
    (by simp [GraphEvent.Fresh, GraphEvent.identities, killP, expand, killY, killR, killX,
      finish, pTask, uTask, yTask, rTask, xTask, qTask])
    ⟨_, _, _, q_known, by intro source impossible; cases impossible⟩
  exact .append five
    ⟨
      ⟨
        [q.ref],
        some uTask,
        NodeAt.group
          (address := [1, 1, 0, 0, 0, 1, 1, 0]) (group := ⟨d, [q]⟩)
          (by rfl) (by simp)
      ⟩,
      by decide
    ⟩
    (by simp [notice, killP, expand, killY, killR, killX, finish,
      GraphEvent.Fresh, GraphEvent.identities]) trivial

/-- The actual start checker accepts all six settlements, including the late failure.
Witness: executable initialization and replay; X was started through R before R failed.
-/
theorem inputs_started : inputsStarted work inputs = true := by cbv

/-- Expansion registers the shared child and later cleanup never erases its descriptor.
Witness: inverse object-child registration from the present producer after P fails,
followed by permanent registry persistence through all remaining settlements.
-/
theorem object_child_registration_boundary
    : xTask ∉ (State.initialize (Work.fromExecution work)).tasks.map Task.occurrence
      ∧ ∃ task ∈
          ((State.initialize (Work.fromExecution work)).replayGraphEvents
            inputs.flatten).tasks,
          task.occurrence = xTask
          ∧ task.groups.map DeliveryNode.ref = [c.ref, d.ref, r.ref] := by
  refine ⟨?_, ?_⟩
  · change xTask ∉ [pTask, uTask, qTask, rTask]
    simp [xTask, pTask, uTask, qTask, rTask]
  have matching : expand.MatchesWork work := ⟨_, _, u_known, rfl, rfl⟩
  exact TaskAt.executionGroup_registered_after_object x_known matching
    (before := [killP]) ⟨[killY, killR, killX, finish, notice], rfl⟩
    (node := { task := ⟨uTask, [p, q, r, s]⟩ }) (by cbv)

/-- Late child integration records every parent even after ancestor cancellation.
Witness: apply the general generated-replay theorem immediately after expansion, before
the later closures can remove all live records and make the assertion vacuous.
-/
theorem expanded_parents_registered
    : let queue :=
        ((State.initialize (Work.fromExecution work)).runNormalized [[killP], [expand]]).1
      ∀ node ∈ queue.groupNodes,
        ∀ parent, node.group.parent = some parent → parent ∈ queue.registeredGroups :=
  generated.runNormalized_parentsRegistered
    (source_valid.prefix ⟨[killY, killR, killX, finish, notice], rfl⟩)

/-- Complete source replay preserves parent edges and every registration descriptor.
Witness: generated ancestry and valid input matching discharge the general replay theorem.
-/
theorem replay_record_metadata
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ State.ChildLinksCanonical
            ((State.initialize (Work.fromExecution work)).runNormalized inputs).1 parents
        ∧ State.GroupNodesMatchWork
            ((State.initialize (Work.fromExecution work)).runNormalized inputs).1 work :=
  generated.runNormalized_groupMetadata source_valid

/-- Generated ancestor records share complete descriptors with any actual contributor.
Witness: the pure execution allocation certificate, including paths and optional labels.
-/
theorem record_contributor_descriptor {record dependencies node nodeDependencies producer}
    (recordAt : GroupRecordAt work record dependencies)
    (nodeAt : NodeAt work node .group nodeDependencies producer)
    (same : record.ref = node.ref)
    : record = node :=
  generated.record_eq_node recordAt nodeAt same

/-- Node coherence follows from execution itself, independently of the fixture inventory.
Witness: the general complete-descriptor assignment theorem for generated work.
-/
theorem generated_node_refs_coherent : NodeRefCoherent work := generated.nodeRefCoherent

/-- Full replay's cancellation registry is supported by exactly its accepted failures.
Witness: source validity and executable start discipline instantiate the replay invariant,
with no assumed output explanation or contributor-only registration invariant.
-/
theorem replay_cancellations_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).runNormalized inputs).1 work
        (GraphEvent.failureSettlements inputs.flatten) :=
  generated.runNormalized_cancelledRecordsSupported inputs source_valid inputs_started

/-- Full corrected replay retains exact healthy counters and safe all-group bounds.
Witness: generated work, source validity, and start discipline instantiate the rebuilt
joint counter theorem even when ancestor-only registrations are cancelled.
-/
theorem replay_healthy_counters
    : ∃ parents,
        State.HealthyCounterAccounting
          ((State.initialize (Work.fromExecution work)).runNormalized inputs).1
          work parents inputs.flatten (GraphEvent.failureSettlements inputs.flatten) :=
  generated.runNormalized_healthyCounterLedger inputs source_valid inputs_started

/-- Late registration and redundant rejections retain healthy registered ownership.
Witness: the general started replay theorem discharges object and stream contributor
availability internally. Its failure ledger includes every received source failure.
-/
theorem replay_owner_accounting
    : ∃ parents,
        State.OwnerAccounting
          ((State.initialize (Work.fromExecution work)).runNormalized inputs).1
          work parents inputs.flatten := by
  obtain ⟨parents, _, accounting⟩ :=
    generated.runNormalized_ownerAccounting_of_started inputs source_valid inputs_started
  exact ⟨parents, accounting⟩

/-- Initial populated groups and active roots are real contributors, not ancestor shells.
Witness: the general pruning/activation theorem applied to the generated regression work.
-/
theorem initial_group_refs_contribute
    : (State.initialize (Work.fromExecution work)).GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
  createWorkQueue_fromSpec_groupRefSupport work

/-- Full corrected replay retains contributor support for populated records and roots.
Witness: fixed source matching instantiates the general joint state/output support theorem.
-/
theorem replay_group_refs_contribute
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
  createWorkQueue_runNormalized_groupRefSupport source_valid

/-- Every group closure in any matching replay has its exact contributing descriptor.
Witness: generated allocation upgrades registration records and contributor refs to
structural nodes, without treating taskless ancestors as contributors.
-/
theorem replay_group_closures_located {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        GroupClosureLocated work event :=
  createWorkQueue_runNormalized_groupClosuresLocated generated valid

/-- No matching source replay can emit a completion for the taskless wrapper E.
Witness: every emitted closure ref has a real contributor, whereas the structural node
inventory contains no E ref. This covers arbitrary batching, not just the example trace.
-/
theorem wrapper_never_completes {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    : ∀ event ∈
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten,
        GroupClosureRefSupported (fun ref => ref ≠ e.ref) event := by
  intro event member
  have known := createWorkQueue_runNormalized_groupClosureRefs valid event member
  cases event <;> try trivial
  all_goals
    intro sameRef
    obtain ⟨dependencies, node, producer, located, equal⟩ := known
    have token := located.observationToken
    rw [equal, sameRef] at token
    simp [observationTokens, work, children, p, q, r, s, e, c, d] at token

-----------------------------------------------------------------------------------------
-- Cancellation records do not invent task ownership for the taskless wrapper
-----------------------------------------------------------------------------------------

/-- E is a registration record even though it has no directly contributing task.
Witness: its full parent suffix is present in X's C contributor descriptor.
-/
private theorem e_record : GroupRecordAt work e [p.ref] := by
  exact ⟨
    ⟨e, [p]⟩,
    by simp [GroupMetadata.fragments, work, children],
    [p],
    List.suffix_rfl,
    rfl
  ⟩

/-- The ancestor-only wrapper cannot be used as a contributing structural node.
Witness: the generated work's finite node inventory contains no E descriptor. This
excludes the old producer-support conclusion for arbitrary registration candidates.
-/
theorem wrapper_not_node {dependencies producer}
    : ¬NodeAt work e .group dependencies producer := by
  intro known
  have token := known.observationToken
  simp [observationTokens, work, children, p, q, r, s, e, c, d] at token

/-- C's child task really has producer support despite the intermediate taskless E.
Witness: the matched lowering contains X with C as a contributor; the corrected
general theorem supplies the producer's supporting owner and the full ancestor list.
-/
theorem contributing_child_producer_support
    : ∃ dependencies,
        NodeAt work c .group dependencies (some uTask)
        ∧ ∃ owner ∈ [p.ref, q.ref, r.ref, s.ref],
            owner = c.ref ∨ owner ∈ dependencies := by
  let result : TaskResult :=
    ⟨{ path := [], data := userData, deliveryGroups := [p, q, r, s] },
      Work.fromExecution children [1, 1, 0, 0]⟩
  have matching : (GraphEvent.taskSuccess uTask result).MatchesWork work :=
    ⟨_, _, u_known, rfl, rfl⟩
  have candidate : (⟨c, some e.ref⟩ : Group) ∈ result.work.groups := by
    simp [result, children, Work.fromExecution, Work.fromExecution.lowerGroup,
      ReferenceWorkQueue.Work.combine]
  have contributing
      : ∃ task ∈ result.work.tasks, c.ref ∈ task.groups.map DeliveryNode.ref := by
    refine ⟨⟨xTask, [c, d, r]⟩, ?_, List.mem_cons_self⟩
    exact List.mem_cons_self
  exact matching.childGroup_producer_support generated candidate contributing

/-- Retirement evidence for taskless E is not vacuous: its contributing ancestor P
must already be retired. Witness: E's record ancestry and P's genuine task descriptor.
-/
theorem wrapper_retirement_requires_parent {queue : State}
    (protectedWrapper : queue.AncestorsRetired work e.ref)
    : queue.RetiredGroup p.ref :=
  protectedWrapper e [p.ref] e_record rfl p.ref List.mem_cons_self pTask [p.ref]
    ⟨_, _, p_known⟩ List.mem_cons_self

/-- Retiring taskless E carries P's retirement certificate onward to contributing C.
Witness: the general record-chain theorem, without inventing an E task or producer.
-/
theorem child_retirement_through_wrapper {queue : State}
    (protectedWrapper : queue.AncestorsRetired work e.ref)
    (retired : queue.RetiredGroup e.ref)
    : queue.AncestorsRetired work c.ref := by
  have childRecord : GroupRecordAt work c [e.ref, p.ref] :=
    ⟨⟨c, [e, p]⟩, by simp [GroupMetadata.fragments, work, children],
      [e, p], List.suffix_rfl, rfl⟩
  exact .child generated childRecord e_record rfl protectedWrapper retired

/-- P's settled failure justifies E's cancellation without fabricating an E task.
Witness: one real task-failure leaf followed by the record-ancestry rule.
-/
theorem wrapper_record_invalidated : GroupRecordInvalidated work [pTask] e.ref :=
  .ancestor e_record List.mem_cons_self
    (.task ⟨_, _, p_known⟩ List.mem_cons_self List.mem_cons_self)

/-- The old contributor-only invalidation cannot describe E's cancellation.
Witness: it would imply a contributing E task, absent from the finite node inventory.
-/
theorem wrapper_not_groupInvalidated : ¬GroupInvalidated work [pTask] e.ref := by
  intro failure
  obtain ⟨occurrence, owners, ⟨producer, payload, task⟩, owner⟩ := failure.hasContributor
  obtain ⟨node, kind, dependencies, birth, known, same⟩ := task.owner_known owner
  have token := known.observationToken
  rw [same] at token
  simp [observationTokens, work, children, p, q, r, s, e, c, d] at token

/-- On the actual C contributor, record invalidation keeps the original causal meaning.
Witness: the generated-work equivalence applied to C's structural node descriptor.
-/
theorem child_record_invalidation_agrees
    : GroupRecordInvalidated work [pTask] c.ref
      ↔ GroupInvalidated work [pTask] c.ref := by
  apply generated.groupRecordInvalidated_iff_groupInvalidated
    (dependencies := [e.ref, p.ref]) (producer := some uTask)
  exact ⟨[1, 1, 0, 0, 0, 1, 0], _, _, _, _, _, ⟨c, [e, p]⟩,
    rfl, List.mem_cons_self, rfl, rfl⟩

/-- The concrete late-registration prefix has record-supported cancellations P/E/C.
Witness: exact replay refs plus P's direct cause and the two record-ancestry steps.
-/
theorem late_registration_records_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).runNormalized [[killP], [expand]]).1
        work [pTask] := by
  have cancelled
      : (((State.initialize (Work.fromExecution work)).runNormalized [[killP], [expand]]).1
          ).cancelledGroups = [p.ref, e.ref, c.ref] := by cbv
  have child : GroupRecordAt work c [e.ref, p.ref] :=
    ⟨⟨c, [e, p]⟩, by simp [GroupMetadata.fragments, work, children],
      [e, p], List.suffix_rfl, rfl⟩
  intro ref member
  rw [cancelled] at member
  rcases List.mem_cons.mp member with rfl | more
  · exact .task ⟨_, _, p_known⟩ List.mem_cons_self List.mem_cons_self
  · rcases List.mem_cons.mp more with rfl | last
    · exact wrapper_record_invalidated
    · obtain rfl := List.mem_singleton.mp last
      exact .ancestor child List.mem_cons_self wrapper_record_invalidated

/-- Removing already integrated P/E/C records has the same supported cancellation refs.
Witness: reverse the two input batches, then reduce the collector's retained history.
This exercises recursive removal through a live taskless wrapper, not refused insertion.
-/
theorem early_removal_records_supported
    : State.CancelledRecordsSupported
        ((State.initialize (Work.fromExecution work)).runNormalized [[expand], [killP]]).1
        work [pTask] := by
  have supported := late_registration_records_supported
  have early
      : (((State.initialize (Work.fromExecution work)).runNormalized [[expand], [killP]]).1
          ).cancelledGroups
        = [c.ref, e.ref, p.ref] := by cbv
  have late
      : (((State.initialize (Work.fromExecution work)).runNormalized [[killP], [expand]]).1
          ).cancelledGroups = [p.ref, e.ref, c.ref] := by cbv
  intro ref member
  apply supported ref
  rw [late]
  rw [early] at member
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_comm, or_left_comm, or_assoc]
    using member

-----------------------------------------------------------------------------------------
-- Exact completion counts determine the required failure ordering
-----------------------------------------------------------------------------------------

/-- These six occurrences exhaust the tasks. Witness: the finite observation inventory. -/
private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = pTask
      ∨ occurrence = uTask
      ∨ occurrence = xTask
      ∨ occurrence = yTask
      ∨ occurrence = qTask
      ∨ occurrence = rTask := by
  have member := known.observationToken
  simpa [observationTokens, work, children, pTask, uTask, xTask, yTask, qTask, rTask]
    using member

private theorem c_known : NodeAt work c .group [e.ref, p.ref] (some uTask) :=
  ⟨
    [1, 1, 0, 0, 0, 1, 0],
    _,
    _,
    { result := .error 1, cause := some 1 },
    .empty,
    _,
    ⟨c, [e, p]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

-----------------------------------------------------------------------------------------
-- Taskless-parent registration now retains inherited cancellation
-----------------------------------------------------------------------------------------

private def beforeX : State :=
  ((State.initialize (Work.fromExecution work)).runNormalized
    [[killP], [expand], [killY], [killR]]).1

/-- E is registered and cancelled before C, retaining the failed ancestor's effect.
Witness: evaluate full-chain lowering and the actual queue before X settles.
-/
theorem taskless_parent_retained
    : e.ref
        ∈ (Work.fromExecution children [1, 1, 0, 0]).groups.map
            (fun group => group.node.ref)
      ∧ beforeX.groupNode? e.ref = none
      ∧ e.ref ∈ beforeX.registeredGroups
      ∧ e.ref ∈ beforeX.cancelledGroups
      ∧ p.ref ∈ beforeX.cancelledGroups := by
  have registered : beforeX.registeredGroups = [0, 1, 2, 3, 4, 5, 6] := by cbv
  have cancelled : beforeX.cancelledGroups = [0, 4, 5, 3, 2] := by cbv
  exact ⟨
    by decide,
    by cbv,
    by simp [registered, e],
    by simp [cancelled, e],
    by simp [cancelled, p]
  ⟩

/-- C's registration cancellation agrees with its generated causal invalidation.
Witness: executable reduction and inherited failure from P's actual accepted task.
-/
theorem guard_rejects_invalidated
    : beforeX.cancelledGroups.contains c.ref = true
      ∧ GroupInvalidated work [rTask, yTask, pTask] c.ref := by
  refine ⟨by cbv, ?_⟩
  exact .groupDependency ⟨c, some uTask, c_known, rfl⟩ (by simp)
    (.task ⟨none, _, p_known⟩ List.mem_cons_self (by simp))

/-- C is retired rather than left behind an absent, uncancelled intermediate parent.
Witness: parent-first registration propagates the cancellation registry through E.
-/
theorem late_child_retired
    : beforeX.groupNode? c.ref = none ∧ c.ref ∈ beforeX.cancelledGroups := by
  have cancelled : beforeX.cancelledGroups = [0, 4, 5, 3, 2] := by cbv
  exact ⟨by cbv, by simp [cancelled, c]⟩

-----------------------------------------------------------------------------------------
-- No alternate failure evidence can explain the emitted error totals
-----------------------------------------------------------------------------------------

private def NodesAssigned (assigned : Nat → DeliveryNode) : Execution.Work → Prop
  | .empty => True
  | .declareGroups _ tasks => NodesAssigned assigned tasks
  | .combine left right => NodesAssigned assigned left ∧ NodesAssigned assigned right
  | .executionGroup groups _ _ nested =>
      (∀ group ∈ groups, group.node = assigned group.node.ref)
      ∧ NodesAssigned assigned nested
  | .stream .. => False

private theorem NodesAssigned.withoutDeclarations {assigned work}
    (assignment : NodesAssigned assigned work)
    : NodesAssigned assigned work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      exact NodesAssigned.withoutDeclarations (work := tasks) assignment
  | empty | combine | executionGroup | stream => exact assignment
termination_by sizeOf work

/-- Structural navigation preserves the node assignment. Witness: navigation induction. -/
private theorem NodesAssigned.located {assigned root address current producer owners}
    (assignment : NodesAssigned assigned root)
    (located : Located root address current producer owners)
    : NodesAssigned assigned current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact assignment.withoutDeclarations
  | left prior ih => exact ih.1.withoutDeclarations
  | right prior ih => exact ih.2.withoutDeclarations
  | executionGroup prior ih => exact ih.2.withoutDeclarations
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
Witness: a six contributing-node assignment is preserved by structural navigation to
every descriptor.
-/
theorem node_refs_coherent : NodeRefCoherent work := by
  let assigned (ref : NodeRef) :=
    if ref = 0 then p else if ref = 1 then q else if ref = 2 then r else
      if ref = 3 then s else if ref = 5 then c else d
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
  EventSource.ValidFor.of_asynchronous
    ⟨
      rfl,
      ⟨inputs, rfl⟩,
      fun _ _ before after => before.trans after,
      fun batches admitted =>
        ⟨source_validGraphEvents batches admitted, source_respectsStarts batches admitted⟩
    ⟩

/-- The corrected runner ignores X and reports only Y's retained error for D.
Witness: reduce initialization, every handler, and publisher normalization.
-/
theorem output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      = correctedOutputs := by
  cbv

/-- The corrected replay no longer emits the independently rejected trace.
Witness: its exact output reports D1, whereas the former output reported D2.
-/
theorem runner_avoids_rejected_output
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).2
      ≠ rejectedOutputs := by
  rw [output]
  simp [correctedOutputs, rejectedOutputs]

-----------------------------------------------------------------------------------------
-- A child failure can settle while its successful producer is still buffered
-----------------------------------------------------------------------------------------

private def sourceCuts : FailureCuts :=
  let queue := State.initialize (Work.fromExecution work)
  sourceObjectFailureCuts 0
    (queue.sourceRunBlocks { active := queue.initialGroups ++ queue.initialStreams }
      inputs).2.2

/-- Actual accepted source cuts retain Y's failure before the shared value is flushed.
Witness: the labelled replay retains X's source cut separately from selected licensing.
-/
theorem accepted_source_cuts
    : sourceCuts = [(0, pTask), (1, yTask), (2, rTask), (3, xTask)] := by
  cbv

/-- Only P's failure has been observed when Y settles.
Witness: evaluate the canonical nonterminal history at Y's actual source cut.
-/
theorem child_failure_prefix
    : ((State.initialize (Work.fromExecution work)).nonterminalAtoms inputs).take 1
      = [.groupFailure p 1] := by
  cbv

/-- No matching can make the buffered producer published before Y settles.
Witness: the prefix contains a failure notice and no successful value atom.
-/
theorem buffered_producer_unpublished (matching : PublicationMatching)
    : ¬Published matching
        (((State.initialize (Work.fromExecution work)).nonterminalAtoms inputs).take 1)
        uTask := by
  rw [child_failure_prefix]
  rintro ⟨index, event, selected, value, _⟩
  cases index with
  | zero =>
      have same : event = .groupFailure p 1 := (Option.some.inj selected).symm
      subst event
      cases value
  | succ index => simp at selected

/-- Requiring every settling child's producer to have published is too strong.
Witness: the generated, valid, started replay's actual Y cut, for every matching.
This rejects a proof-only strategy, not the public conformance statement.
-/
theorem producer_publication_requirement_refuted (matching : PublicationMatching)
    : ¬(∀ before cut occurrence after,
          sourceCuts = before ++ (cut, occurrence) :: after
          → ∀ producer,
              TaskHasProducer work occurrence (some producer)
              → Published matching
                  (((State.initialize (Work.fromExecution work)).nonterminalAtoms
                      inputs).take
                    cut)
                  producer) := by
  intro ready
  exact buffered_producer_unpublished matching
    (ready [(0, pTask)] 1 yTask [(2, rTask), (3, xTask)] accepted_source_cuts uTask
      ⟨_, _, y_known⟩)

/-- P's failure cannot invalidate the independent root owner Q.
Witness: generated root-group failure decomposition and P's unique owner descriptor.
-/
private theorem q_healthy_at_child_cut (matching : PublicationMatching)
    : ¬NodeFailed work matching [.groupFailure p 1] [(0, pTask)] q.ref := by
  have root : NodeAt work q .group [] none :=
    ⟨[1, 1, 0], _, [], { result := .ok (userData, 0) }, children, [], ⟨q, []⟩,
      rfl, by simp, rfl, rfl⟩
  intro failed
  rcases generated.groupFailure_withRootProducer root failed with direct | ancestor
  · obtain ⟨occurrence, owners, ⟨producer, payload, known⟩, owner, failed⟩ := direct
    have same : occurrence = pTask := by simpa [failedBefore] using failed
    subst occurrence
    rw [(known.unique p_known).1] at owner
    simp [p, q] at owner
  · obtain ⟨_, impossible, _⟩ := ancestor
    cases impossible

/-- The buffered producer nevertheless satisfies the needed historical safety.
Witness: Q remains healthy, and this successful producer is a reachable root task.
No output explanation, producer publication, or admitted-history premise is assumed.
-/
theorem buffered_producer_uncancelled (matching : PublicationMatching)
    : ¬TaskCancelled work matching
        (((State.initialize (Work.fromExecution work)).nonterminalAtoms inputs).take 1)
        [(0, pTask)] uTask := by
  rw [child_failure_prefix]
  apply task_uncancelled_of_producerSafety (ref := q.ref) ?_
    (.root ⟨_, _, u_known⟩) u_known (by simp) (q_healthy_at_child_cut matching)
  · intro producer impossible
    cases impossible
  · intro cut occurrence member
    obtain same := List.mem_singleton.mp member
    cases same
    exact ⟨_, _, _, p_known, rfl⟩

-----------------------------------------------------------------------------------------
-- Exact ancestry includes a taskless parent without inventing a contributor
-----------------------------------------------------------------------------------------

/-- C's ancestry decomposes through taskless E using registration metadata alone.
Witness: the general generated-record chain theorem, not a fabricated E task descriptor.
The earlier wrapper counterexample separately proves E has no contributing task.
-/
theorem taskless_parent_chain
    : ∃ childDependencies parentDependencies,
        GroupRecordAt work c childDependencies
        ∧ GroupRecordAt work e parentDependencies
        ∧ childDependencies = e.ref :: parentDependencies := by
  have child : GroupRecordAt work c [e.ref, p.ref] :=
    ⟨⟨c, [e, p]⟩, by simp [GroupMetadata.fragments, work, children],
      [e, p], List.suffix_rfl, rfl⟩
  exact ⟨_, _, child, e_record, generated.groupRecordAncestryChain child e_record rfl⟩

-----------------------------------------------------------------------------------------
-- Child-owner health protects the buffered producer throughout the defer-only fragment
-----------------------------------------------------------------------------------------

/-- This generated shared-task fixture has no stream nodes anywhere in its work tree.
Witness: structural navigation retains the fixture's group-only node assignment.
-/
theorem defer_only : Correctness.DeferOnly work := by
  let assigned (ref : NodeRef) :=
    if ref = 0 then p else if ref = 1 then q else if ref = 2 then r else
      if ref = 3 then s else if ref = 5 then c else d
  have assignment : NodesAssigned assigned work := by
    simp [NodesAssigned, assigned, work, children, p, q, r, s, c, d]
  intro node kind dependencies producer known
  cases StructuralEquivalence.nodeAt_of_current known with
  | group => rfl
  | stream located => exact False.elim (assignment.located located.toCurrent)

/-- Y's contributing owner S remains healthy at its cut, despite P's earlier failure.
Witness: S has a root descriptor, no dependencies, and no contribution from P's task.
-/
private theorem s_healthy_at_child_cut (matching : PublicationMatching)
    : ¬NodeFailed work matching [.groupFailure p 1] [(0, pTask)] s.ref := by
  have root : NodeAt work s .group [] none :=
    ⟨[1, 1, 0], _, [], { result := .ok (userData, 0) }, children, [], ⟨s, []⟩,
      rfl, by simp, rfl, rfl⟩
  intro failed
  rcases generated.groupFailure_withRootProducer root failed with direct | ancestor
  · obtain ⟨occurrence, owners, ⟨producer, payload, known⟩, owner, failed⟩ := direct
    have same : occurrence = pTask := by simpa [failedBefore] using failed
    subst occurrence
    rw [(known.unique p_known).1] at owner
    simp [p, s] at owner
  · obtain ⟨_, impossible, _⟩ := ancestor
    cases impossible

/-- The child's owner health alone protects both Y and its still-buffered producer U.
Witness: the general generated defer-only theorems propagate either cancellation to S.
This uses neither a prior publication of U nor a separately assumed producer-safety fact.
-/
theorem buffered_failure_safe_from_child_owner (matching : PublicationMatching)
    : ¬TaskCancelled work matching
        (((State.initialize (Work.fromExecution work)).nonterminalAtoms inputs).take 1)
        [(0, pTask)] yTask
      ∧ ¬TaskCancelled work matching
          (((State.initialize (Work.fromExecution work)).nonterminalAtoms inputs).take 1)
          [(0, pTask)] uTask := by
  rw [child_failure_prefix]
  have owner : s.ref ∈ [d.ref, s.ref] := by simp
  exact ⟨
    fun cancelled => s_healthy_at_child_cut matching
      (generated.defer_cancelled_owner_failed defer_only y_known owner cancelled),
    fun cancelled => s_healthy_at_child_cut matching
      (generated.defer_cancelled_producer_fails_owner defer_only y_known owner cancelled)
  ⟩

/-- Cleanup invalidates taskless E without inventing an observable failure for it, while
the real descendant C fails. Witness: the general historical equivalence and C's explicit
P ancestry. The conclusion holds for arbitrary observations and publication matching.
-/
theorem taskless_cleanup_not_semantic_failure (matching : PublicationMatching)
    (events : List WorkQueueEvent)
    : ¬NodeFailed work matching events [(0, pTask)] e.ref
      ∧ NodeFailed work matching events [(0, pTask)] c.ref := by
  have inventory : failedBefore [(0, pTask)] events.length = [pTask] := by
    simp [failedBefore]
  rw [generated.defer_nodeFailed_iff_invalidated defer_only,
    generated.defer_nodeFailed_iff_invalidated defer_only, inventory]
  have parent : GroupInvalidated work [pTask] p.ref :=
    .task ⟨none, _, p_known⟩ (by simp) (by simp)
  exact ⟨
    wrapper_not_groupInvalidated,
    .groupDependency ⟨c, some uTask, c_known, rfl⟩ (by simp) parent
  ⟩

-----------------------------------------------------------------------------------------
-- Received failures and causal group health
-----------------------------------------------------------------------------------------

/-- The task-presence projection retains every received object failure.
Witness: actual started replay, including X's causally redundant rejection.
-/
theorem distinct_failure_inventories
    : GraphEvent.failureSettlements inputs.flatten = [xTask, rTask, yTask, pTask]
      ∧ (State.initialize (Work.fromExecution work)).objectFailureContributions
          inputs.flatten
        = [xTask, rTask, yTask, pTask] := by cbv

/-- Source and present-task failure inventories agree on contributor and record invalidation.
Witness: general started-replay equivalence, including the record-ancestry transport.
-/
theorem equivalent_failure_closures (ref : NodeRef)
    : (GroupInvalidated work (GraphEvent.failureSettlements inputs.flatten) ref
        ↔ GroupInvalidated work
            ((State.initialize
                (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
              inputs)
            ref)
      ∧ (GroupRecordInvalidated work (GraphEvent.failureSettlements inputs.flatten) ref
          ↔ GroupRecordInvalidated work
              ((State.initialize
                  (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
                inputs)
              ref) := by
  have same := generated.runNormalized_failureInventories_groupInvalidated_iff
    inputs source_valid inputs_started
  exact ⟨same ref, groupRecordInvalidated_congr same ref⟩

/-- Accepted failures suffice for owner accounting and exact healthy pending counts.
Witness: transfer the source ledger along the proved closure equivalence, without assuming
missing-parent health or equality of failure tokens.
-/
theorem accepted_owner_accounting
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized inputs).1
      let settled := GraphEvent.taskSettlements inputs.flatten
      let failed :=
        (State.initialize
          (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
          inputs
      queue.HealthyRegisteredTaskAccounting work settled failed
      ∧ queue.HealthyPendingTracks work settled failed :=
  generated.runNormalized_acceptedOwnerAccounting inputs source_valid inputs_started

/-- Every prefix of the shared-task, taskless-ancestor regression has justified health
boundaries. Witness: general health replay, including late registration and the redundant
rejection X; the proof does not enumerate intermediate states or assume guard soundness.
-/
theorem every_prefix_retired_health (received : List GraphEvent)
    (earlier : received.IsPrefix inputs.flatten)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents received
      let failed :=
        (State.initialize (Work.fromExecution work)).objectFailureContributions received
      queue.UncancelledRetiredHealthy work failed
      ∧ queue.RootAncestorsHealthy work failed
      ∧ queue.MissingParentAncestorsHealthy work failed := by
  have valid := source_valid.prefix earlier
  have accepted : State.eventsStarted [] (State.initialize (Work.fromExecution work))
      inputs.flatten = true := by cbv
  obtain ⟨after, same⟩ := earlier
  rw [← same] at accepted
  exact generated.replayGraphEvents_retiredHealth received valid
    (State.eventsStarted_prefix accepted)

/-- A selected sublist of received failures is licensed on the exact output history.
Witness: general defer-only licensing selects informative cuts from the actual source
blocks. Y is safe even while its producer's success is still buffered.
-/
theorem accepted_failures_licensed (matching : PublicationMatching)
    : ∃ cuts,
        cuts.Sublist
          ( let queue := State.initialize (Work.fromExecution work)
            availableObjectFailureCuts work 0
              (queue.sourceRunBlocks
                { active := queue.initialGroups ++ queue.initialStreams } inputs).2.2)
        ∧ FailureWitness work (ConformancePlan.initialRefs work) matching
            ((State.initialize (Work.fromExecution work)).nonterminalAtoms inputs)
            cuts := by
  let queue := State.initialize (Work.fromExecution work)
  let blocks :=
    (queue.sourceRunBlocks { active := queue.initialGroups ++ queue.initialStreams } inputs).2.2
  refine ⟨informativeObjectFailureCuts work blocks,
    informativeObjectFailureCuts_sublist work blocks, ?_⟩
  exact ConformancePlan.failureWitness_of_defer generated defer_only source_valid
    inputs_started matching

/-- D's complete contributor inventory contains two distinct failed task causes. -/
private theorem child_reporting_bound {reported errors}
    (cause : NodeFailureCauses work reported d.ref errors)
    : errors ≤ 2 := by
  apply generated.nodeFailureCauses_count_le [xTask, yTask] ?_ cause
  intro occurrence owners producer payload known owner failed
  have token := known.observationToken
  simp [work, children, observationTokens] at token
  rcases token with rfl | rfl | rfl | rfl | rfl | rfl
  · have same := (known.unique p_known).1
    rw [same] at owner
    simp [d, p] at owner
  · have same := (known.unique u_known).2.2
    rw [same] at failed
    cases failed
  · simp [xTask]
  · simp [yTask]
  · have same := (known.unique q_known).2.2
    rw [same] at failed
    cases failed
  · have same := (known.unique r_known).1
    rw [same] at owner
    simp [d, r] at owner

/-- No value grouping can inflate D beyond its two distinct available task causes. -/
theorem output_not_valid : ¬ValidHistory work ⟨[p, q, r, s], [], rejectedOutputs⟩ := by
  have excludes {events matching failures} (explained : Explains work [p, q, r, s] []
      events matching failures) : .groupFailure d 3 ∉ events := by
    intro member
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨reported, _, _, allowed⟩ := explained.2.2
    have count := child_reporting_bound (allowed index _ selected).2.2.2
    omega
  rintro (⟨events, matching, failures, explained, batching⟩ |
    ⟨events, matching, failures, explained, _, batching⟩)
  · exact excludes explained ((batching.control_mem (by simp [IsValue])).mp
      (by simp [rejectedOutputs]))
  · have member := (batching.control_mem (event := .groupFailure d 3) (by simp [IsValue])).mp
      (by simp [rejectedOutputs])
    exact excludes explained (List.mem_append.mp member |>.resolve_right (by simp))

/-- Canonical terminal accounting covers the generated taskless-parent replay. -/
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

#print axioms accepted_failures_licensed
#print axioms actual_output_admitted
#print axioms output_not_valid

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerTasklessParent
