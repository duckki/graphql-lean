import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredTaskLinks

/-! Buffered values prevent successful retirement of their still-live contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- An empty shell cannot own a value still buffered in the queue
-----------------------------------------------------------------------------------------

/-- Pruning cannot remove a contributor of a task with retained memberships.
Witness: if the selected empty shell had this ref, its membership would put the
task in its empty task list. Every other pruning step preserves the owner record.
This statement needs no source, health, announcement, or counter premise.
-/
theorem State.pruneEmptyGroups_linkedOwner_present {queue : State} {task : TaskNode}
    (links
      : queue.TaskLinkedOn task.task.occurrence
          (task.task.groups.map Execution.DeliveryNode.ref)) {ref : Nat}
    (contributes : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    (groups : List Execution.DeliveryNode)
    : ref
      ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
          (fun node => node.group.node.ref) := by
  have loop (fuel : Nat) (current : State) (more kept : List Execution.DeliveryNode)
      (links : current.TaskLinkedOn task.task.occurrence
        (task.task.groups.map Execution.DeliveryNode.ref))
      (present : ref ∈ current.groupNodes.map (fun node => node.group.node.ref))
      : ref ∈ (State.pruneEmptyGroups.go fuel current more kept).1.groupNodes.map
          (fun node => node.group.node.ref) := by
    induction fuel generalizing current more kept with
    | zero => exact present
    | succ fuel ih =>
        cases more with
        | nil => exact present
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _ links present
            · rename_i node found
              split
              · rename_i empty
                have different : ref ≠ group.ref := by
                  intro same
                  have selected : node.group.node.ref = group.ref :=
                    beq_iff_eq.mp (List.find?_some
                      (p := fun candidate : GroupNode => candidate.group.node.ref == group.ref)
                      found)
                  have listed := links node
                    (List.mem_of_find?_eq_some found) (selected.symm ▸ same ▸ contributes)
                  have noTasks : node.tasks = [] :=
                    List.isEmpty_iff.mp (Bool.and_eq_true_iff.mp empty).1
                  simp only [noTasks, List.not_mem_nil] at listed
                have nextLinks : State.TaskLinkedOn
                    { current with groupNodes :=
                      current.groupNodes.filter (fun entry => entry.group.node.ref != group.ref) }
                    task.task.occurrence (task.task.groups.map Execution.DeliveryNode.ref) := by
                  intro owner live contributor
                  exact links owner (List.mem_filter.mp live).1 contributor
                apply ih _ _ _ nextLinks
                obtain ⟨owner, live, same⟩ := List.mem_map.mp present
                exact List.mem_map.mpr ⟨owner, List.mem_filter.mpr
                  ⟨live, by simp [same, different]⟩,
                  same⟩
              · exact ih _ _ _ links present
  exact loop _ queue groups [] links present

/-- Buffered-owner specialization of the general membership-based pruning fact. -/
theorem State.pruneEmptyGroups_bufferedOwner_present {queue : State}
    (links : queue.StoredTaskLinks) {task : TaskNode} (member : task ∈ queue.taskNodes)
    (stored : task.value.isSome = true) {ref : Nat}
    (contributes : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    (groups : List Execution.DeliveryNode)
    : ref
      ∈ (queue.pruneEmptyGroups groups).1.groupNodes.map
          (fun node => node.group.node.ref) :=
  State.pruneEmptyGroups_linkedOwner_present (links task member stored) contributes
    present groups

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

/-- A linked task surviving a successful flush keeps every earlier live contributor.
Witness: task removal preserves group refs, the closing ref cannot own a surviving task,
and empty-shell pruning cannot remove any of its other memberships.
The contributor may be latent or already carry an error; no health premise is needed.
-/
theorem State.finishGroupSuccess_linkedOwner_present {queue : State}
    (group : GroupNode) (live : group ∈ queue.groupNodes) {task : TaskNode}
    (links
      : queue.TaskLinkedOn task.task.occurrence
          (task.task.groups.map Execution.DeliveryNode.ref))
    (retained : task ∈ (queue.finishGroupSuccess group).1.taskNodes) {ref : Nat}
    (contributes : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : ref
      ∈ (queue.finishGroupSuccess group).1.groupNodes.map
          (fun node => node.group.node.ref) := by
  obtain ⟨_, unlisted⟩ := queue.finishGroupSuccess_retained_unlisted group retained
  have different : ref ≠ group.group.node.ref := by
    intro same
    exact unlisted (links group live (same ▸ contributes))
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  have flushedRefs : flushed.groupNodes.map (fun node => node.group.node.ref)
      = queue.groupNodes.map (fun node => node.group.node.ref) := by
    have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
        : (tasks.foldl flushGroupTask acc).1.groupNodes.map (fun node => node.group.node.ref)
          = acc.1.groupNodes.map (fun node => node.group.node.ref) := by
      induction tasks generalizing acc with
      | nil => rfl
      | cons occurrence rest ih =>
          rw [List.foldl_cons, ih]
          unfold flushGroupTask
          split
          · rfl
          · simp only [State.removeTask, List.map_map]; rfl
    exact loop group.tasks (queue, [], [])
  have flushedLinks : flushed.TaskLinkedOn task.task.occurrence
      (task.task.groups.map Execution.DeliveryNode.ref) := by
    have loop (tasks : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
        (included : tasks.Subset group.tasks)
        (prior : acc.1.TaskLinkedOn task.task.occurrence
          (task.task.groups.map Execution.DeliveryNode.ref))
        : (tasks.foldl flushGroupTask acc).1.TaskLinkedOn task.task.occurrence
            (task.task.groups.map Execution.DeliveryNode.ref) := by
      induction tasks generalizing acc with
      | nil => exact prior
      | cons occurrence rest ih =>
          simp only [List.foldl_cons, flushGroupTask]
          split
          · exact ih _ (fun _ member => included (List.mem_cons_of_mem _ member)) prior
          · exact ih _ (fun _ member => included (List.mem_cons_of_mem _ member))
              (prior.removeOtherTask occurrence (fun same =>
                unlisted (same ▸ included List.mem_cons_self)))
    exact loop group.tasks (queue, [], []) (List.Subset.refl _) links
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.ref != group.group.node.ref)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  have currentLinks : current.TaskLinkedOn task.task.occurrence
      (task.task.groups.map Execution.DeliveryNode.ref) := by
    intro owner present contributes
    exact flushedLinks owner (List.mem_filter.mp present).1 contributes
  have currentOwner : ref ∈ current.groupNodes.map (fun node => node.group.node.ref) := by
    rw [← flushedRefs] at present
    obtain ⟨owner, member, same⟩ := List.mem_map.mp present
    exact List.mem_map.mpr ⟨owner, List.mem_filter.mpr
      ⟨member, by simp [same, different]⟩, same⟩
  exact State.pruneEmptyGroups_linkedOwner_present currentLinks contributes currentOwner _

/-- Buffered-owner specialization; existing value-conservation proofs retain their API. -/
theorem State.finishGroupSuccess_bufferedOwner_present {queue : State}
    (links : queue.StoredTaskLinks) (group : GroupNode) (live : group ∈ queue.groupNodes)
    {task : TaskNode} (retained : task ∈ (queue.finishGroupSuccess group).1.taskNodes)
    (stored : task.value.isSome = true) {ref : Nat}
    (contributes : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun node => node.group.node.ref))
    : ref
      ∈ (queue.finishGroupSuccess group).1.groupNodes.map
          (fun node => node.group.node.ref) :=
  State.finishGroupSuccess_linkedOwner_present group live
    (links task (queue.finishGroupSuccess_retained_unlisted group retained).1 stored)
    retained contributes present

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
