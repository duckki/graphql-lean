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

private def root : DeliveryNode := { key := 0, path := [], label := some (.string "R") }
private def parent : DeliveryNode := { key := 1, path := [], label := some (.string "P") }
private def child : DeliveryNode := { key := 2, path := [], label := some (.string "C") }
private def other : DeliveryNode := { key := 3, path := [], label := some (.string "D") }
private def rootTask : Occurrence := .executionGroup [1, 0]
private def parentTask : Occurrence := .executionGroup [1, 1, 1, 0]
private def firstTask : Occurrence := .executionGroup [1, 1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 1, 1, 0]
private def data : List (Name × ResponseValue) := [("a", .scalar "a")]

private def work : Execution.Work :=
  .combine .empty
    (.combine (.executionGroup [⟨root, []⟩] [] (.error 1) .empty)
      (.combine (.executionGroup [⟨root, []⟩, ⟨child, [parent]⟩] [] (.error 2) .empty)
        (.combine
          (.executionGroup [⟨parent, []⟩] [] (.ok (data, 0)) (.combine .empty .empty))
          (.combine
            (.executionGroup [⟨child, [parent]⟩, ⟨other, []⟩] [] (.error 1) .empty)
            .empty))))

private def killRoot : GraphEvent := .taskFailure rootTask 1
private def first : GraphEvent := .taskFailure firstTask 2
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
      .groupFailure child 3,
      .workQueueTermination
    ]
  ]

/-- Execution generates R-only, R/C, and C/D failures under a healthy parent P.
Witness: two aliased required fields contribute two errors to R/C, distinguishing its
retained contribution from the one-error R-only and C/D failures.
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
    : TaskAt work rootTask [root.key] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem first_known
    : TaskAt work firstTask [root.key, child.key] none (.object [] (.error 2)) :=
  ⟨_, [], .error 2, .empty, [], rfl, rfl, rfl⟩

private theorem shared_known
    : TaskAt work sharedTask [child.key, other.key] none (.object [] (.error 1)) :=
  ⟨_, [], .error 1, .empty, [], rfl, rfl, rfl⟩

private theorem parent_known
    : TaskAt work parentTask [parent.key] none (.object [] (.ok (data, 0))) :=
  ⟨_, [], .ok (data, 0), .combine .empty .empty, [], rfl, rfl, rfl⟩

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
          ∨ (node = child ∧ dependencies = [parent.key])
          ∨ (node = parent ∧ dependencies = [])
          ∨ (node = other ∧ dependencies = [])) := by
  have roles : Semantics.KeyRoles.WorkRoles (fun _ => false) work := by
    simp [Semantics.KeyRoles.WorkRoles, work]
  have groupKind : kind = .group := by
    have role := Correctness.node_key_role roles known
    cases kind with
    | group => rfl
    | stream => change false = true at role; cases role
  subst kind
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, rfl, rfl⟩ := known
  have task : TaskAt work (.executionGroup address)
      (groups.map (fun group => group.node.key)) producer (.object path result) :=
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

/-- The generated fixture also satisfies the public key-coherence premise.
Witness: repeated keys refer to the same one of four descriptors with distinct keys.
-/
theorem coherent : NodeKeyCoherent work := by
  intro left leftKind leftDependencies leftProducer right rightKind rightDependencies
    rightProducer leftKnown rightKnown sameKey
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
      (known : TaskAt work occurrence owners none payload) (owner : node.key ∈ owners)
      : CanAnnounce work [] (fun _ => .executionGroup []) [] [] node .group [] none := by
    refine ⟨by simp [announcedKeys, pendingKeys],
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
      ⟨[1, 0], _, [], .error 1, .empty, [], ⟨root, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible root_known (by simp)⟩
  · exact ⟨[], none,
      ⟨[1, 1, 1, 0], _, [], .ok (data, 0), .combine .empty .empty, [],
        ⟨parent, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible parent_known (by simp)⟩
  · exact ⟨[], none,
      ⟨[1, 1, 1, 1, 0], _, [], .error 1, .empty, [], ⟨other, []⟩, rfl, by simp, rfl, rfl⟩,
      eligible shared_known (by simp)⟩

-----------------------------------------------------------------------------------------
-- Accepted settlements retain their order across delayed notification
-----------------------------------------------------------------------------------------

private def matching : PublicationMatching := fun _ => parentTask
private def failures : FailureCuts := [(0, rootTask), (1, firstTask), (1, sharedTask)]
private def initial : Keys := [root.key, parent.key, other.key]
private def atoms : List Execution.WorkQueueEvent := outputs.flatten.take 5

/-- Actual guard-selected source blocks produce the accepted R, R/C, C/D cut order.
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
        ∧ (queue.replayGraphEvents before).taskHasHealthyOwner node.task = true
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
  obtain ⟨earlier, _, errors, _, node, _, _, _, source, _, _, _, ledger, found, healthy⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_split source_valid.1 source_valid.2 split
  exact ⟨earlier.filterMap Prod.fst, errors, node, source, found, healthy, ledger.symm⟩

/-- C/D's pre-handler ledger also contains the earlier R/C settlement at that same cut.
Witness: split at the next entry, preserving the reverse-order contribution convention.
-/
theorem shared_cut_prefix
    : let queue := State.initialize (Work.fromExecution work)
      ∃ before errors node,
        (before ++ [GraphEvent.taskFailure sharedTask errors]).IsPrefix inputs.flatten
        ∧ (queue.replayGraphEvents before).taskNode? sharedTask = some node
        ∧ (queue.replayGraphEvents before).taskHasHealthyOwner node.task = true
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
  obtain ⟨earlier, _, errors, _, node, _, _, _, source, _, _, _, ledger, found, healthy⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_split source_valid.1 source_valid.2 split
  exact ⟨earlier.filterMap Prod.fst, errors, node, source, found, healthy, ledger.symm⟩

/-- Closing R does not erase the start justification of the surviving R/C task.
Witness: general initialization and failure preservation, not a recomputed owner choice.
-/
theorem closed_owner_start_witness
    : let queue := State.initialize (Work.fromExecution work)
      let before := (queue.taskFailure rootTask 1).1
      before.StartedTasksAnnounced (queue.initialGroups.map DeliveryNode.key)
      ∧ (before.taskNode? firstTask).isSome = true
      ∧ root.key ∉ before.rootGroups := by
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
          ∈ announcedKeys
              ((queue.initialGroups ++ queue.initialStreams).map DeliveryNode.key)
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
        owner = other.key
        ∧ ∀ prior priorOwners,
            prior ∈ [rootTask, firstTask]
            → TaskHasOwners work prior priorOwners
            → owner ∉ priorOwners := by
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
  obtain ⟨owners, owner, ⟨producer, payload, known⟩, contributes, safe⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_directHealthyOwner generated
      source_valid.1 source_valid.2 split
  have ownersEq := (known.unique shared_known).1
  have member : owner ∈ [child.key, other.key] := ownersEq ▸ contributes
  have notChild : owner ∉ [root.key, child.key] :=
    safe firstTask _ (by simp) ⟨_, _, first_known⟩
  refine ⟨owner, ?_, safe⟩
  rcases List.mem_cons.mp member with same | same
  · exact False.elim (notChild (by simp [same]))
  · exact List.mem_singleton.mp same

private theorem root_node : NodeAt work root .group [] none :=
  ⟨[1, 0], _, [], .error 1, .empty, [], ⟨root, []⟩, rfl, by simp, rfl, rfl⟩

/-- The latent child avoids direct/ancestor invalidation after R closes; its parent is live.
Witness: actual prefix replay supplies all accounting; every stored parent lookup succeeds,
so the general ancestor-guard bridge requires no assumed output explanation.
-/
theorem latent_child_guard_health : ¬GroupInvalidated work [rootTask] child.key := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents [killRoot]
  have valid : ValidGraphEvents work [killRoot] := source_valid.1.prefix
    ⟨[first, shared, finish], rfl⟩
  have parents : queue.groupNodes.map (fun node => node.group.parent)
      = [none, some parent.key, none] := by
    simp only [queue]
    cbv
  have parentLive : (queue.groupNode? parent.key).isSome = true := by
    simp only [queue]
    cbv
  have missing : queue.MissingParentAncestorsHealthy work
      ((State.initialize (Work.fromExecution work)).objectFailureContributions [killRoot]) := by
    apply State.MissingParentAncestorsHealthy.of_presentParents
    intro node member key same
    have listed : some key ∈ queue.groupNodes.map (fun node => node.group.parent) :=
      List.mem_map.mpr ⟨node, member, same⟩
    have keyEq : key = parent.key := by simpa [parents] using listed
    simpa only [keyEq] using parentLive
  exact createWorkQueue_replayGraphEvents_groupIsHealthy_uninvalidated generated valid
    (by cbv) missing (by cbv)

private theorem parent_node : NodeAt work parent .group [] none :=
  ⟨
    [1, 1, 1, 0],
    _,
    [],
    .ok (data, 0),
    .combine .empty .empty,
    [],
    ⟨parent, []⟩,
    rfl,
    by simp,
    rfl,
    rfl
  ⟩

private theorem child_node : NodeAt work child .group [parent.key] none :=
  ⟨[1, 1, 0], _, [], .error 2, .empty, [], ⟨child, [parent]⟩, rfl, by simp, rfl, rfl⟩

private theorem other_node : NodeAt work other .group [] none :=
  ⟨[1, 1, 1, 1, 0], _, [], .error 1, .empty, [], ⟨other, []⟩, rfl, by simp, rfl, rfl⟩

/-- A healthy root key has no failed contributor or dependency.
Witness: the fixture's descriptors exclude streams and generated producers.
-/
private theorem root_healthy {failed : List Occurrence} {published : Occurrence → Prop}
    {node : DeliveryNode} (known : NodeAt work node .group [] none)
    (notChild : node.key ≠ child.key)
    (noFailure
      : ∀ occurrence ∈ failed,
          ∀ owners, TaskHasOwners work occurrence owners → node.key ∉ owners)
    : ¬Causality.NodeFailed work failed published node.key := by
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
    : ¬Causality.NodeFailed work failed published parent.key := by
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
    : ¬Causality.NodeFailed work [rootTask] published child.key := by
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
  | producers _ noRoot _ _ => exact noRoot ⟨child, .group, [parent.key], child_node, rfl⟩

/-- Before C/D settles, D remains healthy despite the earlier accepted R/C failure.
Witness: neither earlier failed task contributes to independent D.
-/
private theorem other_snapshot {failed : List Occurrence} {published : Occurrence → Prop}
    (subset : failed.Subset [rootTask, firstTask])
    : ¬Causality.NodeFailed work failed published other.key := by
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
    {published : Occurrence → Prop} {occurrence owners payload key}
    (known : TaskAt work occurrence owners none payload) (owner : key ∈ owners)
    (healthy : ¬Causality.NodeFailed work failed published key)
    : ¬Causality.TaskCancelled work failed published occurrence := by
  intro cancelled
  cases cancelled with
  | owners task _ _ failed =>
      obtain ⟨producer, otherPayload, task⟩ := task
      obtain ⟨rfl, _, _⟩ := known.unique task
      exact healthy (failed key owner)
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
          root.key,
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
          root.key,
          by simp,
          by decide
        ⟩,
        ?_
      ⟩
      rintro ⟨boundary, member, _, cause⟩
      have zero : boundary = 0 := by simpa using member
      subst boundary
      exact root_uncancelled first_known (key := child.key) (by simp) child_snapshot cause
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
          other.key,
          by simp,
          by decide
        ⟩,
        ?_
      ⟩
      rintro ⟨boundary, member, _, cause⟩
      have cases : boundary = 0 ∨ boundary = 1 := by simpa using member
      rcases cases with rfl | rfl
      all_goals
        exact root_uncancelled shared_known (key := other.key) (by simp)
          (other_snapshot (by simp [failedBefore, List.Subset])) cause
  | _ :: _ :: _ :: _ =>
      have lengths := congrArg List.length equal
      simp [failures] at lengths

/-- Every visible failure belongs to the three accepted settlements, at any cut. -/
private theorem visible_subset (cut : Nat)
    : (failedBefore failures cut).Subset [rootTask, firstTask, sharedTask] := by
  intro occurrence member
  obtain ⟨entry, member, same⟩ := List.mem_map.mp member
  have all : occurrence ∈ failures.map Prod.snd :=
    List.mem_map.mpr ⟨entry, (List.mem_filter.mp member).1, same⟩
  exact all

/-- Independent P stays healthy and uncancelled throughout the actual history.
Witness: no accepted failure contributes to P at any reached snapshot.
-/
private theorem parent_healthy (observed : List Execution.WorkQueueEvent)
    : ¬NodeFailed work matching observed failures parent.key := by
  rintro ⟨cut, _, _, cause⟩
  exact parent_snapshot (visible_subset cut) cause

private theorem parent_uncancelled (observed : List Execution.WorkQueueEvent)
    : ¬TaskCancelled work matching observed failures parentTask := by
  rintro ⟨cut, _, _, cause⟩
  exact root_uncancelled parent_known (by simp)
    (parent_snapshot (visible_subset cut)) cause

private def contribution (key : Nat) (task : Occurrence) : Nat :=
  if task = rootTask then
    if key = root.key then 1 else 0
  else if task = firstTask then
    if key = root.key ∨ key = child.key then 2 else 0
  else if key = child.key ∨ key = other.key then
    1
  else
    0

/-- Each accepted settlement contributes its fixed payload count to exactly its owners.
Witness: the three structural task descriptors; no notification reorders this inventory.
-/
private theorem errors_counted (selected : List Occurrence)
    (subset : selected.Subset [rootTask, firstTask, sharedTask]) (key : Nat)
    : NodeErrors work selected key (selected.map (contribution key)).sum := by
  refine ⟨contribution key, ?_, rfl⟩
  intro occurrence member
  have cases := subset member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl
  · exact ⟨_, _, _, root_known, by simp [contribution, Payload.failure]⟩
  · exact ⟨_, _, _, first_known, by
      simp [contribution, firstTask, rootTask, Payload.failure]⟩
  · exact ⟨_, _, _, shared_known, by
      simp [contribution, sharedTask, firstTask, rootTask, Payload.failure]⟩

private theorem root_failure_allowed
    : EventAllowed work initial matching [] failures (.groupFailure root 1) := by
  refine ⟨⟨[], none, root_node⟩, by unfold Open; decide, ?_, ?_⟩
  · exact NodeFailed.task root_known (by simp) (by simp [failedBefore, failures])
  · exact errors_counted [rootTask] (by simp [List.Subset]) root.key

private theorem other_failure_allowed
    : EventAllowed work initial matching [.groupFailure root 1] failures
        (.groupFailure other 1) := by
  refine ⟨⟨[], none, other_node⟩, by unfold Open; decide, ?_, ?_⟩
  · exact NodeFailed.task shared_known (by simp) (by simp [failedBefore, failures])
  · exact errors_counted [rootTask, firstTask, sharedTask] (by simp [List.Subset]) other.key

private theorem parent_value_allowed
    : EventAllowed work initial matching
        [.groupFailure root 1, .groupFailure other 1] failures
        (.groupValues parent
          [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }]) := by
  refine ⟨[parent.key], none, { path := [], data, deliveryGroups := [parent] },
    rfl, parent_known, ?_, ?_⟩
  · refine ⟨?_, ?_, by simp, trivial⟩
    · rintro ⟨index, event, selected, value, _⟩
      match index with
      | 0 | 1 => cases selected; exact value
      | index + 2 => simp at selected
    · exact parent_uncancelled _
  · have opened : OpenOwner work initial [.groupFailure root 1, .groupFailure other 1]
        [parent.key] parent :=
      ⟨⟨.group, [], none, parent_node⟩, by simp, by unfold Open; decide⟩
    refine ⟨opened, ⟨parent, opened, parent_healthy _⟩, ?_⟩
    intro node available
    obtain ⟨kind, dependencies, producer, known⟩ := available.1
    rcases node_cases known with rfl | rfl | rfl | rfl <;> decide

private def beforeNotice : List Execution.WorkQueueEvent := atoms.take 3

private theorem parent_published : Published matching beforeNotice parentTask :=
  ⟨
    2,
    .groupValues parent
      [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
    rfl,
    trivial,
    rfl
  ⟩

/-- P's completion releases the latent failed C, after both of C's failures have settled.
Witness: healthy P is accounted for, and the retained failure licenses C's notice.
-/
theorem notice_allowed
    : EventAllowed work initial matching beforeNotice failures
        (.groupSuccess parent [child] []) := by
  refine ⟨⟨[], none, parent_node⟩, by unfold Open; decide, ?_, ?_, ?_⟩
  · exact parent_healthy _
  · rintro occurrence owners ⟨producer, payload, known⟩ owner
    rcases task_cases known with rfl | rfl | rfl | rfl
    · obtain ⟨rfl, _, _⟩ := known.unique first_known
      simp [parent, root, child] at owner
    · obtain ⟨rfl, _, _⟩ := known.unique shared_known
      simp [parent, child, other] at owner
    · exact Or.inr parent_published
    · obtain ⟨rfl, _, _⟩ := known.unique root_known
      simp [parent, root] at owner
  · refine ⟨by decide, ?_, by simp⟩
    intro node member
    have same := List.mem_singleton.mp member
    subst node
    refine ⟨[parent.key], none, child_node, by decide, Or.inr ?_, by simp, ?_⟩
    · exact ⟨rfl, firstTask, [root.key, child.key],
        by simp [failedBefore, failures, beforeNotice, atoms, outputs],
        ⟨_, _, first_known⟩, by simp⟩
    · intro key member
      have same := List.mem_singleton.mp member
      subst key
      exact ⟨parent_healthy _, Or.inr (Or.inl (by decide))⟩

private theorem child_failure_allowed
    : EventAllowed work initial matching
        (beforeNotice ++ [.groupSuccess parent [child] []]) failures
        (.groupFailure child 3) := by
  refine ⟨⟨[parent.key], none, child_node⟩, by unfold Open; decide, ?_, ?_⟩
  · exact NodeFailed.task first_known (by simp)
      (by simp [failedBefore, failures, beforeNotice, atoms, outputs])
  · exact errors_counted [rootTask, firstTask, sharedTask] (by simp [List.Subset]) child.key

/-- All actual atoms share one publication matching and the accepted settlement order.
Witness: R-only at cut zero, then R/C before C/D at cut one, followed by P and C notices.
-/
theorem atomic_explanation
    : Explains work [root, parent, other] [] atoms matching failures := by
  refine ⟨initialized, failure_licensed, ?_⟩
  intro index event selected
  match index with
  | 0 => cases selected; exact root_failure_allowed
  | 1 => cases selected; exact other_failure_allowed
  | 2 => cases selected; exact parent_value_allowed
  | 3 => cases selected; exact notice_allowed
  | 4 => cases selected; exact child_failure_allowed
  | index + 5 => simp [atoms, outputs] at selected

/-- Every failed task is cancelled and P is published; all four owners close.
Witness: the coherent explanation protects P and accounts for each recorded failure.
-/
private theorem terminal : Terminal work initial matching atoms failures := by
  constructor
  · intro occurrence owners producer payload known
    have recorded (task : Occurrence) (member : task ∈ [rootTask, firstTask, sharedTask])
        : task ∈ failedBefore failures atoms.length := by
      simpa [failedBefore, failures, atoms, outputs] using member
    rcases task_cases known with rfl | rfl | rfl | rfl
    · exact Or.inl (TaskCancelled.of_recorded first_known (by decide)
        (atomic_explanation.failed_unpublished (recorded _ (by simp))) (recorded _ (by simp)))
    · exact Or.inl (TaskCancelled.of_recorded shared_known (by decide)
        (atomic_explanation.failed_unpublished (recorded _ (by simp))) (recorded _ (by simp)))
    · exact Or.inr ⟨2, .groupValues parent [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }], rfl, trivial, rfl⟩
    · exact Or.inl (TaskCancelled.of_recorded root_known (by decide)
        (atomic_explanation.failed_unpublished (recorded _ (by simp))) (recorded _ (by simp)))
  · intro node kind dependencies producer known
    apply Or.inl
    rcases node_cases known with rfl | rfl | rfl | rfl <;> decide

/-- The formerly rejected implementation output is an admitted complete run.
Witness: the accepted failure order, terminal accounting, and the runner's actual batches.
-/
theorem output_admitted : AdmissibleRun work ⟨[root, parent, other], [], outputs⟩ := by
  refine ⟨atoms, matching, failures, atomic_explanation, terminal, ?_⟩
  exact .cons (batch := [.groupFailure root 1]) (by simp) (.separate _ .nil)
    (.cons (batch := [.groupFailure other 1]) (by simp) (.separate _ .nil)
      (.cons
        (batch :=
          [
            .groupValues parent
              [{ path := [], data := data, errors := 0, deliveryGroups := [parent] }],
            .groupSuccess parent [child] [],
            .groupFailure child 3,
            .workQueueTermination
          ])
        (by simp) (.separate _ (.separate _ (.separate _ (.separate _ .nil)))) .nil))

/-- Exact queue replay, not an alternate serialization, satisfies the revised contract.
Witness: transport the admitted output through the executable replay equality.
-/
theorem actual_output_admitted
    : let queue := State.initialize (Work.fromExecution work)
      AdmissibleRun work
        ⟨queue.initialGroups, queue.initialStreams, (queue.runNormalized inputs).2⟩ := by
  simpa only [output.1, output.2.1, output.2.2] using output_admitted

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerLatentFailureOrder
