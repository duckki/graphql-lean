import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping

/-! Exact task-store effect of the actual affected-membership fold. No all-task scan is
added to execution: the global filter below is a proof projection of that literal fold.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (Task TaskNode GroupNode)

private instance : LawfulBEq Occurrence where
  eq_of_beq := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
  rfl := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mpr rfl

-----------------------------------------------------------------------------------------
-- The reference retention predicate is the negation of the actual last-owner guard
-----------------------------------------------------------------------------------------

/-- The literal task-node predicate used by reference failed-group removal. -/
def removalTaskLive (queue : ReferenceWorkQueue.State) (task : Task) : Bool :=
  task.groups.any
    (fun group => queue.groupNodes.any (fun owner => owner.group.node.ref == group.ref))

theorem removalTaskLive_ownerless (queue : ReferenceWorkQueue.State) (task : Task)
    : task.groups.all (fun owner => (queue.groupNode? owner.ref).isNone)
      = !removalTaskLive queue task := by
  simp only [← Option.not_isSome, ReferenceWorkQueue.State.groupNode?, List.isSome_find?,
    List.all_eq_not_any_not, Bool.not_not, removalTaskLive]

private theorem matchedNode_task_eq {queue : ReferenceWorkQueue.State} {work : Work}
    (matching : queue.RegisteredTasksMatch work)
    (registered : queue.StartedTasksRegistered) {node : TaskNode}
    (member : node ∈ queue.taskNodes) {task : Task} (known : task ∈ queue.tasks)
    (same : node.task.occurrence = task.occurrence)
    : node.task = task :=
  matchedTasks_eq_of_occurrence_eq (matching node.task (registered node member))
    (matching task known) same

/-- Task disposal preserves exact structural registration of every remaining record. -/
theorem fusedRemovalTaskStep_startedTasksRegistered (acc : State × List CleanupTarget)
    (registered : acc.1.queue.StartedTasksRegistered) (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.queue.StartedTasksRegistered := by
  unfold fusedRemovalTaskStep
  split
  · exact registered
  · split
    · exact registered.removeTask occurrence
    · exact registered

/-- One actual task step filters only its selected occurrence when it has no live owner.
Matched catalogue provenance supplies the exact descriptor; no catalogue uniqueness premise
or desired final task-store premise is required.
-/
theorem fusedRemovalTaskStep_taskNodes {work : Work} (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (registered : acc.1.queue.StartedTasksRegistered) (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.queue.taskNodes
      = acc.1.queue.taskNodes.filter
          (fun node =>
            removalTaskLive acc.1.queue node.task
            || node.task.occurrence != occurrence) := by
  unfold fusedRemovalTaskStep
  cases found : acc.1.queue.task? occurrence with
  | none =>
      simp only
      symm
      apply List.filter_eq_self.mpr
      intro node member
      have different : node.task.occurrence ≠ occurrence := by
        intro same
        have lookup := registeredTask_lookup matching (registered node member)
        rw [same, found] at lookup
        cases lookup
      have excluded : (node.task.occurrence == occurrence) = false :=
        Bool.eq_false_iff.mpr (fun eq => different ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp eq))
      simp only [bne, excluded, Bool.not_false, Bool.or_true]
  | some task =>
      have known := List.mem_of_find?_eq_some found
      have taskKey := (ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp
        (List.find?_some (p := fun candidate : Task => candidate.occurrence == occurrence) found)
      simp only
      split
      · rename_i ownerless
        change acc.1.queue.taskNodes.filter _ = _
        apply List.filter_congr
        intro node member
        by_cases same : node.task.occurrence = occurrence
        · have identical := matchedNode_task_eq matching registered member known (same.trans taskKey.symm)
          have dead : removalTaskLive acc.1.queue node.task = false := by
            rw [removalTaskLive_ownerless] at ownerless
            rw [identical]
            simpa only [Bool.not_eq_true'] using ownerless
          simp only [dead, Bool.false_or]
        · have excluded : (node.task.occurrence == occurrence) = false :=
            Bool.eq_false_iff.mpr (fun eq => same ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp eq))
          simp only [bne, excluded, Bool.not_false, Bool.or_true]
      · rename_i supported
        symm
        apply List.filter_eq_self.mpr
        intro node member
        by_cases same : node.task.occurrence = occurrence
        · have identical := matchedNode_task_eq matching registered member known (same.trans taskKey.symm)
          have live : removalTaskLive acc.1.queue node.task = true := by
            rw [removalTaskLive_ownerless] at supported
            rw [identical]
            cases live : removalTaskLive acc.1.queue task with
            | false => exact (supported (by simp [live])).elim
            | true => rfl
          simp only [live, Bool.true_or]
        · have excluded : (node.task.occurrence == occurrence) = false :=
            Bool.eq_false_iff.mpr (fun eq => same ((ReferenceWorkQueue.occurrence_beq_iff_eq _ _).mp eq))
          simp only [bne, excluded, Bool.not_false, Bool.or_true]

-----------------------------------------------------------------------------------------
-- Whole affected-task fold as a proof-only retention filter
-----------------------------------------------------------------------------------------

/-- Exact task-store projection of any affected-membership prefix. Live groups remain
unchanged by last-owner disposal; earlier filters compose in the original storage order.
Ownerless records not named in this prefix are deliberately retained by this local result.
-/
theorem fusedRemovalTaskFold_taskNodes {work : Work} (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (registered : acc.1.queue.StartedTasksRegistered)
    (sound : acc.1.queue.GroupMembershipSound)
    : (tasks.foldl fusedRemovalTaskStep acc).1.queue.taskNodes
      = acc.1.queue.taskNodes.filter
          (fun node =>
            removalTaskLive acc.1.queue node.task
            || !tasks.contains node.task.occurrence) := by
  induction tasks generalizing acc with
  | nil =>
      simp only [List.foldl_nil, List.contains_nil, Bool.not_false, Bool.or_true]
      exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  | cons occurrence rest ih =>
      rw [List.foldl_cons, ih _
        (fusedRemovalTaskStep_registeredTasksMatch acc matching occurrence)
        (fusedRemovalTaskStep_startedTasksRegistered acc registered occurrence)
        (fusedRemovalTaskStep_groupMembershipSound acc sound occurrence)]
      have groups := fusedRemovalTaskStep_groupNodes acc matching sound occurrence
      have live (task : Task) : removalTaskLive (fusedRemovalTaskStep acc occurrence).1.queue task
          = removalTaskLive acc.1.queue task := by
        unfold removalTaskLive
        rw [groups]
      simp only [live, fusedRemovalTaskStep_taskNodes acc matching registered occurrence,
        List.filter_filter, List.contains_cons, Bool.not_or]
      apply List.filter_congr
      intro node _
      simp only [bne]
      cases removalTaskLive acc.1.queue node.task <;>
        cases node.task.occurrence == occurrence <;> cases rest.contains node.task.occurrence <;> rfl

/-- A complete affected list suffices for the reference global retention filter. The
coverage premise names only initially ownerless records; it will be constructed when a
specific live group is deleted, rather than imposed on source events.
-/
theorem fusedRemovalTaskFold_filterLive {work : Work} (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    (matching : acc.1.queue.RegisteredTasksMatch work)
    (registered : acc.1.queue.StartedTasksRegistered)
    (sound : acc.1.queue.GroupMembershipSound)
    (coverage
      : ∀ node ∈ acc.1.queue.taskNodes,
          removalTaskLive acc.1.queue node.task = false → node.task.occurrence ∈ tasks)
    : (tasks.foldl fusedRemovalTaskStep acc).1.queue.taskNodes
      = acc.1.queue.taskNodes.filter
          (fun node => removalTaskLive acc.1.queue node.task) := by
  rw [fusedRemovalTaskFold_taskNodes tasks acc matching registered sound]
  apply List.filter_congr
  intro node member
  cases live : removalTaskLive acc.1.queue node.task with
  | false =>
      have listed := coverage node member live
      have contained : tasks.contains node.task.occurrence = true :=
        List.contains_iff_mem.mpr listed
      simp only [contained, Bool.not_true, Bool.or_false]
  | true => simp only [Bool.true_or]

/-- Structural registration survives the entire actual task-disposal fold. -/
theorem fusedRemovalTaskFold_startedTasksRegistered (tasks : List Occurrence)
    (acc : State × List CleanupTarget) (registered : acc.1.queue.StartedTasksRegistered)
    : (tasks.foldl fusedRemovalTaskStep acc).1.queue.StartedTasksRegistered := by
  induction tasks generalizing acc with
  | nil => exact registered
  | cons occurrence rest ih =>
      exact ih _ (fusedRemovalTaskStep_startedTasksRegistered acc registered occurrence)

-----------------------------------------------------------------------------------------
-- Existing live task records supply affected-list coverage after one group deletion
-----------------------------------------------------------------------------------------

/-- The task-record frame needed by shrinking removal: exact registration, links to every
surviving contributor, and at least one live contributor. It is independent of cleanup
effects and does not assume a projected endpoint or healthy/active owners.
-/
structure RemovalTaskFrame (queue : ReferenceWorkQueue.State) : Prop where
  registered : queue.StartedTasksRegistered
  linked
    : ∀ node ∈ queue.taskNodes,
        queue.TaskLinkedOn node.task.occurrence
          (node.task.groups.map Execution.DeliveryNode.ref)
  supported : ∀ node ∈ queue.taskNodes, removalTaskLive queue node.task = true

/-- Any record made ownerless by deleting this live group occurs in that group's task
list. All other contributors were already absent, so one prior live owner identifies this
group; membership completeness supplies the occurrence actually visited by the fold.
-/
theorem eraseRemovalGroup_taskCoverage {state : State}
    (frame : RemovalTaskFrame state.queue) {key : Nat} {group : GroupNode}
    (found : state.queue.groupNode? key = some group)
    : ∀ node ∈ (eraseRemovalGroup state key).queue.taskNodes,
        removalTaskLive (eraseRemovalGroup state key).queue node.task = false
        → node.task.occurrence ∈ group.tasks := by
  intro node member dead
  obtain ⟨owner, contributes, present⟩ := List.any_eq_true.mp (frame.supported node member)
  obtain ⟨oldGroup, oldMember, ownerKey⟩ := List.any_eq_true.mp present
  have same : owner.ref = key := by
    by_cases same : owner.ref = key
    · exact same
    · have retained : oldGroup ∈ (eraseRemovalGroup state key).queue.groupNodes :=
        List.mem_filter.mpr ⟨oldMember, by simpa [beq_iff_eq.mp ownerKey] using same⟩
      have stillLive : removalTaskLive (eraseRemovalGroup state key).queue node.task = true :=
        List.any_eq_true.mpr ⟨owner, contributes, List.any_eq_true.mpr ⟨oldGroup, retained, ownerKey⟩⟩
      simp [dead] at stillLive
  apply frame.linked node member group (List.mem_of_find?_eq_some found)
  exact List.mem_map.mpr
    ⟨owner, contributes, same.trans (ReferenceWorkQueue.State.groupNode?_ref found).symm⟩

/-- One actual live-group visit has exactly the globally filtered task-store endpoint and
preserves the same record frame. No already-ownerless record is silently left behind.
-/
theorem fusedRemovalVisit_taskRecords {state : State} {work : Work}
    (matching : state.queue.RegisteredTasksMatch work)
    (sound : state.queue.GroupMembershipSound) (frame : RemovalTaskFrame state.queue)
    {key : Nat} {group : GroupNode} (found : state.queue.groupNode? key = some group)
    (targets : List CleanupTarget)
    : let erased := eraseRemovalGroup state key
      let final := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
      final.1.queue.taskNodes
        = state.queue.taskNodes.filter
            (fun node => removalTaskLive erased.queue node.task)
      ∧ RemovalTaskFrame final.1.queue := by
  let erased := eraseRemovalGroup state key
  let final := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
  have erasedMatch := eraseRemovalGroup_registeredTasksMatch matching key
  have erasedSound := eraseRemovalGroup_groupMembershipSound sound key
  have groups := (fusedRemovalTaskFold_bookkeeping group.tasks (erased, targets)
    erasedMatch erasedSound).1
  have nodes := fusedRemovalTaskFold_filterLive group.tasks (erased, targets)
    erasedMatch frame.registered erasedSound (eraseRemovalGroup_taskCoverage frame found)
  refine ⟨nodes, ?_⟩
  refine ⟨fusedRemovalTaskFold_startedTasksRegistered group.tasks (erased, targets)
    frame.registered, ?_, ?_⟩
  · intro node member owner ownerMember contributor
    rw [nodes] at member
    rw [groups] at ownerMember
    exact frame.linked node (List.mem_filter.mp member).1 owner
      (List.mem_filter.mp ownerMember).1 contributor
  · intro node member
    rw [nodes] at member
    unfold removalTaskLive
    rw [groups]
    exact (List.mem_filter.mp member).2

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
