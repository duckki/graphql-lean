import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureSettlementPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTaskAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAnnouncementCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AcceptedFailureHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.FiniteHistories
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Accepted shared failures retain settlement order across delayed completion notices. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerLatentFailureOrder
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def root : DeliveryNode := { ref := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { ref := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { ref := 2, path := [], label := some (.string "C") }
private def other : DeliveryNode := { ref := 3, path := [], label := some (.string "D") }
private def rootTask : Occurrence := .executionGroup [1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def firstTask : Occurrence := .executionGroup [1, 1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨root, []⟩] [] ({ result := .error 1, cause := some 1 }) .empty)
      (.combine
        (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] []
          ({ result := .error 2, cause := some 1 }) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] ({ result := .ok (data, 0) })
            (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨child, [parent]⟩, ⟨other, []⟩] []
              ({ result := .error 1, cause := some 1 }) .empty)
            .empty))))

private def killRoot : GraphEvent := .taskFailure rootTask 1
private def first : GraphEvent := .taskFailure firstTask 1
private def shared : GraphEvent := .taskFailure sharedTask 1

private def finish : GraphEvent :=
  .taskSuccess parentTask
    {
      value := { deliveryGroups := [parent], path := [], data }
      work := Work.fromExecution (.combine .empty .empty) [1, 1, 1, 0, 0]
    }

private def inputs : List (List GraphEvent) := [[killRoot], [first], [shared], [finish]]

private def outputs : List (List Execution.WorkQueueEvent) :=
  [
    [.groupFailure root 1],
    [.groupFailure other 1],
    [
      .groupValues parent
        [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
      .groupSuccess parent [child] [],
      .groupFailure child 1,
      .workQueueTermination
    ]
  ]

/-- Execution generates R-only, R/C, and C/D failures under a healthy parent P.
Witness: two aliased required fields contribute two errors to R/C, distinguishing its
collected diagnostics from the selected unit causes of all three failed partitions.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 30, "Query", .object "Query" 0,
    [defer [field "required", field "required" [] [] (some "rc1"),
      field "required" [] [] (some "rc2")] (some "R"),
      defer [field "a", defer [field "required" [] [] (some "rc1"),
        field "required" [] [] (some "rc2"), field "required" [] [] (some "cd")]
        (some "C")] (some "P"),
      defer [field "required" [] [] (some "cd")] (some "D")], ?_⟩
  cbv

private theorem root_known
    : TaskAt work rootTask [root.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem first_known
    : TaskAt work firstTask [root.ref, child.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 2, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem shared_known
    : TaskAt work sharedTask [child.ref, other.ref] none (.object [] (.error 1)) :=
  ⟨_, [], { result := .error 1, cause := some 1 }, .empty, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.ref] none (.object [] (.ok (data, 0))) :=
  ⟨_, [], { result := .ok (data, 0) }, .combine .empty .empty, [], rfl, rfl, rfl⟩

/-- All three failures and the parent success satisfy source and actual start checks.
Witness: fixed outcomes, fresh identities, root producer readiness, and executable starts.
-/
theorem source_valid
    : ValidGraphEvents work inputs.flatten ∧ inputsStarted work inputs = true := by
  have zero : ValidGraphEvents work [killRoot] :=
    .append .nil ⟨_, _, _, root_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, killRoot])
      ⟨_, _, _, root_known, by intro source impossible; cases impossible⟩
  have one : ValidGraphEvents work [killRoot, first] :=
    .append zero ⟨_, _, _, first_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, killRoot, firstTask, rootTask])
      ⟨_, _, _, first_known, by intro source impossible; cases impossible⟩
  have two : ValidGraphEvents work [killRoot, first, shared] :=
    .append one ⟨_, _, _, shared_known⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, shared, killRoot,
        firstTask, sharedTask, rootTask])
      ⟨_, _, _, shared_known, by intro source impossible; cases impossible⟩
  exact ⟨
    .append two ⟨_, _, parent_known, rfl, rfl⟩
      (by simp [GraphEvent.Fresh, GraphEvent.identities, first, shared, finish, killRoot,
        firstTask, sharedTask, parentTask, rootTask])
      ⟨_, _, _, parent_known, by intro source impossible; cases impossible⟩,
    by cbv
  ⟩

/-- The real queue reports R then D, then announces C and reports both retained failures.
Witness: exact initialized queue/publisher replay; C is absent from the initial notices.
-/
theorem output
    : let queue := State.initialize (Work.fromExecution work)
      queue.initialGroups = [root, parent, other]
      ∧ queue.initialStreams = []
      ∧ (queue.runNormalized inputs).2 = outputs := by cbv

-----------------------------------------------------------------------------------------
-- Generated work metadata and initial notices
-----------------------------------------------------------------------------------------

private theorem task_cases {occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : occurrence = firstTask
      ∨ occurrence = sharedTask
      ∨ occurrence = parentTask
      ∨ occurrence = rootTask := by
  have member := known.observationToken
  simpa [observationTokens, work, firstTask, sharedTask, parentTask, rootTask, or_comm,
    or_left_comm, or_assoc] using member

/-- Every descriptor is one of the four named groups, including repeated shared owners.
Witness: group-only roles and the finite task locations recover each original defer map.
-/
private theorem node_metadata {node kind dependencies producer}
    (known : NodeAt work node kind dependencies producer)
    : kind = .group
      ∧ producer = none
      ∧ ((node = root ∧ dependencies = [])
          ∨ (node = child ∧ dependencies = [parent.ref])
          ∨ (node = parent ∧ dependencies = [])
          ∨ (node = other ∧ dependencies = [])) := by
  have roles : Semantics.RefRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.RefRoles.WorkRoles, work]
  have groupKind : kind = .group := by
    have role := Correctness.node_ref_role roles known
    cases kind with
    | group => rfl
    | stream => change false = true at role; cases role
  subst kind
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, rfl, rfl⟩ := known
  have task : TaskAt work (.executionGroup address)
      (groups.map (fun group => group.node.ref)) producer (.object path result.deliveryResult) :=
    ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩
  rcases task_cases task with same | same | same | same
  all_goals
    have addressEq := Occurrence.executionGroup.inj same
    subst address
    have shape := located.symm
    simp [work, locateWork, locateWork.go, WorkLocation.child?] at shape
    rw [shape.1.1] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp_all

/-- Forget dependency metadata when only the finite descriptor inventory is needed. -/
private theorem node_cases {node kind dependencies producer}
    (known : NodeAt work node kind dependencies producer)
    : node = root ∨ node = child ∨ node = parent ∨ node = other := by
  rcases (node_metadata known).2.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  all_goals simp

/-- The generated fixture also satisfies the public ref-coherence premise.
Witness: repeated refs refer to the same one of four descriptors with distinct refs.
-/
theorem coherent : NodeRefCoherent work := by
  intro left leftKind leftDependencies leftProducer right rightKind rightDependencies
    rightProducer leftKnown rightKnown sameRef
  rcases node_cases leftKnown with rfl | rfl | rfl | rfl
    <;> rcases node_cases rightKnown with rfl | rfl | rfl | rfl
    <;> simp_all [root, child, parent, other]

/-- The actual R/P/D initialization satisfies the independent notice contract.
Witness: distinct root groups with unpublished outstanding tasks; C correctly waits for P.
-/
theorem initialized
    : let queue := State.initialize (Work.fromExecution work)
      Initializes work queue.initialGroups queue.initialStreams := by
  have eligible {node occurrence owners payload}
      (known : TaskAt work occurrence owners none payload) (owner : node.ref ∈ owners)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedRefs, pendingRefs],
      Or.inl ⟨by simp [NodeFailed], Or.inr ?_⟩, by simp, by simp⟩
    intro accounted
    rcases accounted occurrence owners ⟨_, _, known⟩ owner with cancelled | published
    · simp [TaskCancelled] at cancelled
    · simp [Published] at published
  change Initializes work [root, parent, other] []
  refine ⟨⟨by decide, ?_, by simp⟩, by simp⟩
  intro node member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨[], none,
      ⟨[1, 0], _, [], { result := .error 1, cause := some 1 }, .empty, [], ⟨root, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible root_known (by simp)⟩
  · exact ⟨[], none,
      ⟨[1, 1, 1, 0], _, [], { result := .ok (data, 0) }, .combine .empty .empty, [],
        ⟨parent, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible parent_known (by simp)⟩
  · exact ⟨[], none,
      ⟨[1, 1, 1, 1, 0], _, [], { result := .error 1, cause := some 1 }, .empty, [], ⟨other, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible shared_known (by simp)⟩

-----------------------------------------------------------------------------------------
-- Accepted settlements retain their order across delayed notification
-----------------------------------------------------------------------------------------

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, rootTask), (1, firstTask), (1, sharedTask)]
private def initial : NodeRefs := [root.ref, parent.ref, other.ref]
private def atoms : List Execution.WorkQueueEvent := outputs.flatten.take 5

/-- Actual present-task source blocks produce the received R, R/C, C/D cut order.
Witness: evaluate the proof annotation over the same queue and publisher execution.
-/
theorem eligible_source_cuts
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      sourceObjectFailureCuts 0
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
      = failures := by cbv

/-- R/C's pre-handler ledger contains only R's earlier failure, despite sharing cut one
with C/D. Witness: the general actual-replay split theorem at the first equal-cut entry.
-/
theorem first_cut_prefix
    : let queue := State.initialize (Work.fromExecution work)
      ∃ before errors node,
        (before ++ [GraphEvent.taskFailure firstTask errors]).IsPrefix inputs.flatten
        ∧ (queue.replayGraphEvents before).taskNode? firstTask = some node
        ∧ queue.objectFailureContributions before = [rootTask] := by
  have split :
      let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      sourceObjectFailureCuts 0
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
        = [(0, rootTask)] ++ (1, firstTask) :: [(1, sharedTask)] := by
    dsimp only
    rw [eligible_source_cuts]
    rfl
  obtain ⟨earlier, _, errors, _, node, _, _, _, source, _, _, _, ledger, found⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_split source_valid.1 source_valid.2 split
  exact ⟨earlier.filterMap Prod.fst, errors, node, source, found, ledger.symm⟩

/-- C/D's pre-handler ledger also contains the earlier R/C settlement at that same cut.
Witness: split at the next entry, preserving the reverse-order contribution convention.
-/
theorem shared_cut_prefix
    : let queue := State.initialize (Work.fromExecution work)
      ∃ before errors node,
        (before ++ [GraphEvent.taskFailure sharedTask errors]).IsPrefix inputs.flatten
        ∧ (queue.replayGraphEvents before).taskNode? sharedTask = some node
        ∧ queue.objectFailureContributions before = [firstTask, rootTask] := by
  have split :
      let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      sourceObjectFailureCuts 0
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher inputs).2.2)
        = [(0, rootTask), (1, firstTask)] ++ (1, sharedTask) :: [] := by
    dsimp only
    rw [eligible_source_cuts]
    rfl
  obtain ⟨earlier, _, errors, _, node, _, _, _, source, _, _, _, ledger, found⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_split source_valid.1 source_valid.2 split
  exact ⟨earlier.filterMap Prod.fst, errors, node, source, found, ledger.symm⟩

/-- Closing R does not erase the start justification of the surviving R/C task.
Witness: general initialization and failure preservation, not a recomputed owner choice.
-/
theorem closed_owner_start_witness
    : let queue := State.initialize (Work.fromExecution work)
      let before := (queue.taskFailure rootTask 1).1
      before.StartedTasksAnnounced (queue.initialGroups.map DeliveryNode.ref)
      ∧ (before.taskNode? firstTask).isSome = true
      ∧ root.ref ∉ before.rootGroups := by
  refine ⟨(createWorkQueue_startedTasksAnnounced work).taskFailure rootTask 1, by cbv, ?_⟩
  cbv
  change ¬(0 : Nat) ∈ [1, 3]
  decide

/-- The silent R/C settlement has an announced structural owner at its actual cut one.
Witness: the general cut theorem, using the original source order after R has closed.
-/
theorem silent_cut_announced_owner
    : let queue := State.initialize (Work.fromExecution work)
      ∃ owners owner,
        TaskHasOwners work firstTask owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedRefs
              ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.ref)
              (((queue.runNormalized inputs).2.flatten.flatMap publicationAtoms).take
                1) := by
  apply createWorkQueue_eligibleObjectFailureCuts_announcedOwner source_valid.1 source_valid.2
    (before := [(0, rootTask)]) (after := [(1, sharedTask)])
  dsimp only
  rw [eligible_source_cuts]
  rfl

/-- The later C/D settlement must use D to escape earlier direct failures, including
R/C at the same cut. Witness: the general healthy-owner theorem and fixed contributor
lists; no assumption about abstract output admission or cancellation is supplied.
-/
theorem shared_cut_direct_healthy_owner
    : ∃ owner,
        owner = other.ref
        ∧ ∀ prior priorOwners,
            prior ∈ [rootTask, firstTask]
            → TaskHasOwners work prior priorOwners
            → owner ∉ priorOwners := by
  refine ⟨other.ref, rfl, ?_⟩
  intro occurrence owners earlier ⟨producer, payload, known⟩
  rcases List.mem_cons.mp earlier with rfl | last
  · rw [(known.unique root_known).1]
    simp [other, root]
  · obtain rfl := List.mem_singleton.mp last
    rw [(known.unique first_known).1]
    simp [other, root, child]

private theorem root_node : NodeAt work root .group [] none :=
  ⟨
    [1, 0],
    _,
    [],
    { result := .error 1, cause := some 1 },
    .empty,
    [],
    ⟨root, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- The latent child avoids direct/ancestor invalidation after R closes; its parent is live.
Witness: actual prefix replay supplies all accounting; every stored parent lookup succeeds,
so semantic ancestor health requires no assumed output explanation.
-/
theorem latent_child_guard_health : ¬GroupInvalidated work [rootTask] child.ref := by
  have childKnown : NodeAt work child .group [parent.ref] none :=
    ⟨[1, 1, 0], [⟨root, []⟩, ⟨child, [parent]⟩], [],
      { result := .error 2, cause := some 1 }, .empty, [], ⟨child, [parent]⟩,
      rfl, by simp, rfl, rfl⟩
  intro invalid
  obtain ⟨occurrence, owners, owner, ⟨producer, payload, task⟩, member, contributes, ancestor⟩ :=
    (generated.groupInvalidated_iff childKnown).mp invalid
  obtain rfl := List.mem_singleton.mp member
  rw [(task.unique root_known).1] at contributes
  obtain rfl := List.mem_singleton.mp contributes
  simp [root, child, parent] at ancestor

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨
    [1, 1, 1, 0],
    _,
    [],
    { result := .ok (data, 0) },
    .combine .empty .empty,
    [],
    ⟨parent, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem child_node : NodeAt work child .group [parent.ref] none :=
  ⟨
    [1, 1, 0],
    _,
    [],
    { result := .error 2, cause := some 1 },
    .empty,
    [],
    ⟨child, [parent]⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem other_node : NodeAt work other .group [] none :=
  ⟨
    [1, 1, 1, 1, 0],
    _,
    [],
    { result := .error 1, cause := some 1 },
    .empty,
    [],
    ⟨other, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

/-- A healthy root ref has no failed contributor or dependency.
Witness: the fixture's descriptors exclude streams and generated producers.
-/
private theorem root_healthy {failed : List Occurrence} {published : Occurrence → Prop}
    {node : DeliveryNode} (known : NodeAt work node .group [] none)
    (notChild : node.ref ≠ child.ref)
    (noFailure
      : ∀ occurrence ∈ failed,
          ∀ owners, TaskHasOwners work occurrence owners → node.ref ∉ owners)
    : ¬Causality.NodeFailed work failed published node.ref := by
  intro cause
  cases cause with
  | task task owner member => exact noFailure _ member _ task owner
  | groupDependency metadata member _ =>
      obtain ⟨descriptor, birth, located, same⟩ := metadata
      rcases (node_metadata located).2.2 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simp_all
  | streamDependencies metadata _ _ =>
      obtain ⟨descriptor, birth, located, _⟩ := metadata
      cases (node_metadata located).1
  | producers _ noRoot _ _ => exact noRoot ⟨node, .group, [], known, rfl⟩

/-- None of the three failed tasks owns independent P, at any publication snapshot.
Witness: fixed task descriptors and P's root metadata.
-/
private theorem parent_snapshot {failed : List Occurrence} {published : Occurrence → Prop}
    (subset : failed.Subset [rootTask, firstTask, sharedTask])
    : ¬Causality.NodeFailed work failed published parent.ref := by
  apply root_healthy parent_node (by decide)
  intro occurrence member owners ⟨producer, payload, known⟩
  rcases List.mem_cons.mp (subset member) with rfl | member
  · obtain ⟨rfl, _, _⟩ := known.unique root_known
    decide
  rcases List.mem_cons.mp member with rfl | member
  · obtain ⟨rfl, _, _⟩ := known.unique first_known
    decide
  have same := List.mem_singleton.mp member
  subst occurrence
  obtain ⟨rfl, _, _⟩ := known.unique shared_known
  decide

/-- After R closes, C still keeps R/C live until its own settlement.
Witness: R's failure does not contribute to C, and C's only dependency P is healthy.
-/
private theorem child_snapshot {published : Occurrence → Prop}
    : ¬Causality.NodeFailed work [rootTask] published child.ref := by
  intro cause
  cases cause with
  | task known owner member =>
      have same := List.mem_singleton.mp member
      subst_vars
      obtain ⟨producer, payload, known⟩ := known
      obtain ⟨rfl, _, _⟩ := known.unique root_known
      simp [root, child] at owner
  | groupDependency metadata member failed =>
      obtain ⟨descriptor, birth, located, same⟩ := metadata
      rcases (node_metadata located).2.2 with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals simp only [List.mem_singleton, List.not_mem_nil] at member
      all_goals try contradiction
      subst_vars
      exact parent_snapshot (by simp [List.Subset]) failed
  | streamDependencies metadata _ _ =>
      obtain ⟨descriptor, birth, located, _⟩ := metadata
      cases (node_metadata located).1
  | producers _ noRoot _ _ => exact noRoot ⟨child, .group, [parent.ref], child_node, rfl⟩

/-- Before C/D settles, D remains healthy despite the earlier accepted R/C failure.
Witness: neither earlier failed task contributes to independent D.
-/
private theorem other_snapshot {failed : List Occurrence} {published : Occurrence → Prop}
    (subset : failed.Subset [rootTask, firstTask])
    : ¬Causality.NodeFailed work failed published other.ref := by
  apply root_healthy other_node (by decide)
  intro occurrence member owners ⟨producer, payload, known⟩
  rcases List.mem_cons.mp (subset member) with rfl | member
  · obtain ⟨rfl, _, _⟩ := known.unique root_known
    decide
  have same := List.mem_singleton.mp member
  subst occurrence
  obtain ⟨rfl, _, _⟩ := known.unique first_known
  decide

/-- A root task with a healthy contributing owner is uncancelled at the snapshot.
Witness: that owner blocks owner cancellation, and the task has no producer.
-/
private theorem root_uncancelled {failed : List Occurrence}
    {published : Occurrence → Prop} {occurrence owners payload ref}
    (known : TaskAt work occurrence owners none payload) (owner : ref ∈ owners)
    (healthy : ¬Causality.NodeFailed work failed published ref)
    : ¬Causality.TaskCancelled work failed published occurrence := by
  intro cancelled
  cases cancelled with
  | owners task _ _ failed =>
      obtain ⟨producer, otherPayload, task⟩ := task
      obtain ⟨rfl, _, _⟩ := known.unique task
      exact healthy (failed ref owner)
  | producerFailed task _ _ | producerCancelled task _ _ =>
      obtain ⟨owners, payload, task⟩ := task
      cases (known.unique task).2.1

/-- The previously impossible witness records R/C after R closes but before C/D settles.
Witness: previously announced R licenses R/C, while healthy C prevents cancellation.
-/
theorem failure_licensed : FailureWitness work initial matching atoms failures := by
  intro before cut occurrence after equal
  match before with
  | [] =>
      simp only [failures, List.nil_append, List.cons.injEq, Prod.mk.injEq] at equal
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
      exact ⟨
        by decide,
        by simp,
        ⟨
          _,
          _,
          _,
          root_known,
          rfl,
          .root ⟨_, _, root_known⟩,
          root.ref,
          by simp,
          by decide
        ⟩,
        by simp [TaskCancelled]
      ⟩
  | [one] =>
      simp only [failures, List.cons_append, List.nil_append, List.cons.injEq,
        Prod.mk.injEq] at equal
      obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := equal
      refine ⟨
        by decide,
        by simp,
        ⟨
          _,
          _,
          _,
          first_known,
          rfl,
          .root ⟨_, _, first_known⟩,
          root.ref,
          by simp,
          by decide
        ⟩,
        ?_
      ⟩
      rintro ⟨boundary, member, _, cause⟩
      have zero : boundary = 0 := by simpa using member
      subst boundary
      exact root_uncancelled first_known (ref := child.ref) (by simp) child_snapshot cause
  | [one, two] =>
      simp only [failures, List.cons_append, List.nil_append, List.cons.injEq,
        Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl, ⟨rfl, rfl⟩, rfl⟩ := equal
      refine ⟨
        by decide,
        by simp,
        ⟨
          _,
          _,
          _,
          shared_known,
          rfl,
          .root ⟨_, _, shared_known⟩,
          other.ref,
          by simp,
          by decide
        ⟩,
        ?_
      ⟩
      rintro ⟨boundary, member, _, cause⟩
      have cases : boundary = 0 ∨ boundary = 1 := by simpa using member
      rcases cases with rfl | rfl
      all_goals
        exact root_uncancelled shared_known (ref := other.ref) (by simp)
          (other_snapshot (by simp [failedBefore, List.Subset])) cause
  | _ :: _ :: _ :: _ =>
      have lengths := congrArg List.length equal
      simp [failures] at lengths

/-- The dormant owner retains both rejected computations in registration order. -/
theorem retained_rejections
    : let queue :=
        (State.initialize (Work.fromExecution work)).replayGraphEvents
          [killRoot, first, shared]
      (queue.groupNode? child.ref).map (fun node => (node.tasks, node.pending))
        = some ([firstTask, sharedTask], 2)
      ∧ (queue.taskNode? firstTask).map TaskNode.rejection = some (some 1)
      ∧ (queue.taskNode? sharedTask).map TaskNode.rejection = some (some 1) := by cbv

/-- Each supported selected task explains the unit completion, without adding its
collected diagnostics to another task's rejection. -/
theorem child_selected_cause
    : NodeFailureCause work [firstTask, sharedTask] child.ref 1 :=
  ⟨firstTask, by simp, _, _, _, first_known, by simp, rfl, by decide⟩

/-- The complete canonical proof licenses the same actual equal-cut source ordering. -/
theorem actual_output_admitted
    : AdmissibleRun work
        ((ConformancePlan.initialQueue work).normalizedHistory inputs) := by
  have nonempty : work.size ≠ 0 := by decide
  have starts := generated.initializes nonempty
  obtain ⟨w, obligations⟩ := ConformancePlan.replayWitnessExists_holds work inputs
    ⟨nonempty, generated, starts, source_valid.1, source_valid.2⟩
  have explained := ConformancePlan.explains starts obligations.announced
    obligations.uncancelled obligations.publications obligations.controls
  exact (ConformancePlan.run_iff_terminated explained obligations.batching
          (fun ended =>
            ConformancePlan.terminal (obligations.tasks ended)
              (obligations.nodes ended) (obligations.reported ended))).mpr
    (by cbv)

#print axioms failure_licensed
#print axioms actual_output_admitted

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerLatentFailureOrder
