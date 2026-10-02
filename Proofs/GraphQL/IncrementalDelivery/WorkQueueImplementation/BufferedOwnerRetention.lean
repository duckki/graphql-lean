import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredTaskLinks

/-! Buffered values prevent successful retirement of their still-live contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An empty shell cannot own a value still buffered in the queue
-----------------------------------------------------------------------------------------

/-- Pruning cannot remove a contributor of a buffered task with retained memberships.
Witness: if the selected empty shell had this key, buffered membership would put the
task in its empty task list. Every other pruning step preserves the owner record.
This statement needs no source, health, announcement, or counter premise.
-/
theorem State.pruneEmptyGroups_bufferedOwner_present {queue : State}
    (links : queue.StoredTaskLinks) {task : TaskNode} (member : task ∈ queue.taskNodes)
    (stored : task.value.isSome = true) {key : Nat}
    (contributes : key ∈ task.task.groups.map Execution.DeliveryNode.key)
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.key))
    (groups : List Execution.DeliveryNode)
    : key
      ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
          (fun node => node.group.node.key) := by
  have loop (fuel : Nat) (current : State) (more kept : List Execution.DeliveryNode)
      (links : current.StoredTaskLinks) (member : task ∈ current.taskNodes)
      (present : key ∈ current.groupNodes.map (fun node => node.group.node.key))
      : key ∈ (State.pruneEmptyGroups.go fuel current more kept).1.groupNodes.map
          (fun node => node.group.node.key) := by
    induction fuel generalizing current more kept with
    | zero => exact present
    | succ fuel ih =>
        cases more with
        | nil => exact present
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _ links member present
            · rename_i node found
              split
              · rename_i empty
                have different : key ≠ group.key := by
                  intro same
                  have selected : node.group.node.key = group.key :=
                    beq_iff_eq.mp (List.find?_some
                      (p := fun candidate : GroupNode => candidate.group.node.key == group.key)
                      found)
                  have listed := links task member stored node
                    (List.mem_of_find?_eq_some found) (selected.symm ▸ same ▸ contributes)
                  have noTasks : node.tasks = [] :=
                    List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).1
                  simp only [noTasks, List.not_mem_nil] at listed
                have nextLinks : State.StoredTaskLinks
                    { current with groupNodes :=
                      current.groupNodes.filter (fun entry => entry.group.node.key != group.key) }
                    := by
                  intro buffered old value owner live contributor
                  exact links buffered old value owner (List.mem_filter.mp live).1 contributor
                apply ih _ _ _ nextLinks member
                obtain ⟨owner, live, same⟩ := List.mem_map.mp present
                exact List.mem_map.mpr ⟨owner, List.mem_filter.mpr
                  ⟨live, by simp [same, different]⟩,
                  same⟩
              · exact ih _ _ _ links member present
  exact loop _ queue groups [] links member present

-----------------------------------------------------------------------------------------
-- A successful flush removes a buffered contributor only by selecting that task
-----------------------------------------------------------------------------------------

/-- A retained task after a flush was not among the closing group's memberships.
Witness: every initially findable membership is selected and globally removed. A node
remaining in the final map supplies an initial lookup even if raw descriptors repeat.
-/
theorem State.finishGroupSuccess_retained_unlisted (queue : State) (group : GroupNode)
    {task : TaskNode} (retained : task ∈ (queue.finishGroupSuccess group).1.taskNodes)
    : task ∈ queue.taskNodes ∧ task.task.occurrence ∉ group.tasks := by
  obtain ⟨selected, _, _, _, subset, absent, _, complete, _⟩ :=
    queue.finishGroupSuccess_completeSelection group
  have old := subset retained
  refine ⟨old, ?_⟩
  intro listed
  have existsNode : ∃ node, queue.taskNode? task.task.occurrence = some node := by
    apply Option.ne_none_iff_exists'.mp
    intro missing
    have noMatch := List.find?_eq_none.mp missing task old
    exact noMatch ((occurrence_beq_iff_eq _ _).mpr rfl)
  obtain ⟨node, found⟩ := existsNode
  exact absent node (complete _ listed _ found) task retained
    (State.taskNode?_some found).2.symm

/-- A buffered task surviving a successful flush keeps every earlier live contributor.
Witness: task removal preserves group keys, the closing key cannot own a surviving task,
and empty-shell pruning cannot remove any of its other buffered memberships.
The contributor may be latent or already carry an error; no health premise is needed.
-/
theorem State.finishGroupSuccess_bufferedOwner_present {queue : State}
    (links : queue.StoredTaskLinks) (group : GroupNode) (live : group ∈ queue.groupNodes)
    {task : TaskNode} (retained : task ∈ (queue.finishGroupSuccess group).1.taskNodes)
    (stored : task.value.isSome = true) {key : Nat}
    (contributes : key ∈ task.task.groups.map Execution.DeliveryNode.key)
    (present : key ∈ queue.groupNodes.map (fun node => node.group.node.key))
    : key
      ∈ (queue.finishGroupSuccess group).1.groupNodes.map
          (fun node => node.group.node.key) := by
  obtain ⟨old, unlisted⟩ := queue.finishGroupSuccess_retained_unlisted group retained
  have different : key ≠ group.group.node.key := by
    intro same
    exact unlisted (links task old stored group live (same ▸ contributes))
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  have flushedKeys : flushed.groupNodes.map (fun node => node.group.node.key)
      = queue.groupNodes.map (fun node => node.group.node.key) := by
    have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × Keys)
        : (tasks.foldl flushGroupTask acc).1.groupNodes.map (fun node => node.group.node.key)
          = acc.1.groupNodes.map (fun node => node.group.node.key) := by
      induction tasks generalizing acc with
      | nil => rfl
      | cons occurrence rest ih =>
          rw [List.foldl_cons, ih]
          unfold flushGroupTask
          split
          · rfl
          · simp only [State.removeTask, List.map_map]; rfl
    exact loop group.tasks (queue, [], [])
  have flushedLinks : flushed.StoredTaskLinks := by
    have step (acc : State × List ExecutionGroupValue × Keys) (occurrence : Occurrence)
        (prior : acc.1.StoredTaskLinks)
        : (flushGroupTask acc occurrence).1.StoredTaskLinks := by
      unfold flushGroupTask
      split
      · exact prior
      · exact prior.removeTask occurrence
    have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × Keys)
        (prior : acc.1.StoredTaskLinks)
        : (tasks.foldl flushGroupTask acc).1.StoredTaskLinks := by
      induction tasks generalizing acc with
      | nil => exact prior
      | cons occurrence rest ih => exact ih _ (step _ _ prior)
    exact loop group.tasks (queue, [], []) links
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  have currentLinks : current.StoredTaskLinks := by
    intro node member value owner present contributes
    exact flushedLinks node member value owner (List.mem_filter.mp present).1 contributes
  have currentMember : task ∈ current.taskNodes := by
    have same : (queue.finishGroupSuccess group).1.taskNodes = current.taskNodes :=
      State.pruneEmptyGroups_taskNodes current _
    rwa [same] at retained
  have currentOwner : key ∈ current.groupNodes.map (fun node => node.group.node.key) := by
    rw [← flushedKeys] at present
    obtain ⟨owner, member, same⟩ := List.mem_map.mp present
    exact List.mem_map.mpr ⟨owner, List.mem_filter.mpr
      ⟨member, by simp [same, different]⟩, same⟩
  exact State.pruneEmptyGroups_bufferedOwner_present currentLinks currentMember stored
    contributes currentOwner _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
