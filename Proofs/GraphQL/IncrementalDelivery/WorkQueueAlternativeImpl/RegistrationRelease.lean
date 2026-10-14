import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationScopeCompletion

/-! Delayed activation commutes with empty-shell pruning and shared release activation. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Pruning changes group shells, never the deferred computation store
-----------------------------------------------------------------------------------------

/-- The node-list operation underlying proof-facing eager completion. -/
def activateTaskNodes (nodes : List ReferenceWorkQueue.TaskNode)
    (task : ReferenceWorkQueue.Task)
    : List ReferenceWorkQueue.TaskNode :=
  if (nodes.find? (fun node => node.task.occurrence == task.occurrence)).isSome then
    nodes
  else
    nodes ++ [{ task }]

/-- Active completion changes precisely the computation-node field. -/
theorem activateRegisteredTasks_nodes (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task)
    : activateRegisteredTasks queue tasks
      = { queue with taskNodes := tasks.foldl activateTaskNodes queue.taskNodes } := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      change activateRegisteredTasks (activateRegisteredTask queue task) rest = _
      rw [ih]
      unfold activateRegisteredTask activateTaskNodes
      change _ = { queue with taskNodes := (rest.foldl activateTaskNodes
          (if (queue.taskNode? task.occurrence).isSome then _ else _)) }
      split <;> rfl

/-- Empty-shell pruning is independent of the complete computation-node store.
Witness: the executable pruning loop reads and updates group records only.
-/
theorem pruneEmptyGroups_with_taskNodes (queue : ReferenceWorkQueue.State)
    (groups : List Execution.DeliveryNode) (nodes : List ReferenceWorkQueue.TaskNode)
    : ({ queue with taskNodes := nodes } : ReferenceWorkQueue.State).pruneEmptyGroups
        groups
      = (
        { (queue.pruneEmptyGroups groups).1 with taskNodes := nodes },
        (queue.pruneEmptyGroups groups).2
      ) := by
  have loop (fuel : Nat) (current : ReferenceWorkQueue.State)
      (remaining kept : List Execution.DeliveryNode)
      : ReferenceWorkQueue.State.pruneEmptyGroups.go fuel { current with taskNodes := nodes }
          remaining kept
        = ({ (ReferenceWorkQueue.State.pruneEmptyGroups.go fuel current remaining kept).1
              with taskNodes := nodes },
            (ReferenceWorkQueue.State.pruneEmptyGroups.go fuel current remaining kept).2) := by
    induction fuel generalizing current remaining kept with
    | zero => rfl
    | succ fuel ih =>
        cases remaining with
        | nil => rfl
        | cons group rest =>
            simp only [ReferenceWorkQueue.State.pruneEmptyGroups.go]
            change (match current.groupNode? group.ref with
              | none => _
              | some node => _) = _
            cases found : current.groupNode? group.ref with
            | none => exact ih current rest kept
            | some node =>
                simp only
                split
                · exact ih
                    { current with groupNodes := (current.groupNodes.filter
                      (fun entry => entry.group.node.ref != group.ref)) }
                    (node.childGroups.filterMap (fun key =>
                      (current.groupNode? key).map (fun child => child.group.node)) ++ rest) kept
                · exact ih current rest (kept ++ [group])
  exact loop _ queue groups []

/-- Completing active tasks before or after empty-shell pruning has identical results.
Witness: retain the exact node list while applying the group-only pruning operation.
-/
theorem activateRegisteredTasks_pruneEmptyGroups (queue : ReferenceWorkQueue.State)
    (groups : List Execution.DeliveryNode) (tasks : List ReferenceWorkQueue.Task)
    : (
        activateRegisteredTasks (queue.pruneEmptyGroups groups).1 tasks,
        (queue.pruneEmptyGroups groups).2
      )
      = (activateRegisteredTasks queue tasks).pruneEmptyGroups groups := by
  rw [activateRegisteredTasks_nodes (queue.pruneEmptyGroups groups).1 tasks,
    activateRegisteredTasks_nodes queue tasks,
    pruneEmptyGroups_with_taskNodes queue groups (tasks.foldl activateTaskNodes queue.taskNodes),
    ReferenceWorkQueue.State.pruneEmptyGroups_taskNodes queue groups]

-----------------------------------------------------------------------------------------
-- Source-first installation and active-task completion have the shared release result
-----------------------------------------------------------------------------------------

private theorem startTasks_rootGroups (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (roots : WorkQueueSemantics.NodeRefs)
    : tasks.foldl (fun current task => current.startTask task.occurrence)
        { queue with rootGroups := roots }
      = {
        tasks.foldl (fun current task => current.startTask task.occurrence) queue with
          rootGroups := roots
      } := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      have head : ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).startTask
          task.occurrence = { queue.startTask task.occurrence with rootGroups := roots } := by
        unfold ReferenceWorkQueue.State.startTask
        rw [show ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).taskNode?
          task.occurrence = queue.taskNode? task.occurrence from rfl,
          show ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).task?
          task.occurrence = queue.task? task.occurrence from rfl]
        split
        · rfl
        · split <;> rfl
      rw [List.foldl_cons, head, ih, List.foldl_cons]

private theorem startTasks_startStream (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (key : Nat)
    : tasks.foldl (fun current task => current.startTask task.occurrence)
        (queue.startStream key)
      = (tasks.foldl (fun current task => current.startTask task.occurrence)
          queue).startStream
          key := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, startTask_startStream, ih, List.foldl_cons]

private theorem startTasks_startStreams (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task) (streams : List Execution.DeliveryNode)
    : tasks.foldl (fun current task => current.startTask task.occurrence)
        (streams.foldl (fun current stream => current.startStream stream.ref) queue)
      = streams.foldl (fun current stream => current.startStream stream.ref)
          (tasks.foldl (fun current task => current.startTask task.occurrence)
            queue) := by
  induction streams generalizing queue with
  | nil => rfl
  | cons stream rest ih =>
      rw [List.foldl_cons, ih, startTasks_startStream, List.foldl_cons]

/-- The new release operation is the active start fold followed by shared release activation.
Witness: task starts ignore root installation, commute with source installation, and retain
their order before released-group starts. Disposal affects host observations only.
-/
theorem State.startNewWork_queue (state : State) (newWork : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (running : state.stopped = false)
    : (state.startNewWork newWork integrated targets).1.queue
      = (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence)
          state.queue).startNewWork
          newWork := by
  simp only [State.startNewWork, running, Bool.false_eq_true, ↓reduceIte,
    ReferenceWorkQueue.State.startNewWork]
  rw [startTasks_startStreams, startTasks_rootGroups]
  have roots : (integrated.activeTasks.foldl
      (fun current task => current.startTask task.occurrence) state.queue).rootGroups
      = state.queue.rootGroups := by
    have loop (tasks : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
        : (tasks.foldl (fun current task => current.startTask task.occurrence) queue).rootGroups
          = queue.rootGroups := by
      induction tasks generalizing queue with
      | nil => rfl
      | cons task rest ih =>
          rw [List.foldl_cons, ih]
          unfold ReferenceWorkQueue.State.startTask
          split
          · rfl
          · split <;> rfl
    exact loop integrated.activeTasks state.queue
  rw [roots]
  simpa only [List.foldl_map]
    using startGroups_startStreams
      {
        integrated.activeTasks.foldl
            (fun current task => current.startTask task.occurrence) state.queue with
          rootGroups :=
            state.queue.rootGroups ++ newWork.newGroups.map Execution.DeliveryNode.ref
      }
      (newWork.newGroups.map Execution.DeliveryNode.ref) newWork.newStreams

/-- Registration, pruning and actual delayed release activation recover the reference item.
Witness: full scope completion, catalogue coherence, group-only pruning and the common
release operation. No assumption about cleanup targets or rejected-task counts is required.
-/
theorem State.integrateStreamItem_queue {state : State} {work : Work}
    (present : state.queue.RootGroupsPresent)
    (matching : state.queue.RegisteredTasksMatch work)
    (item : ReferenceWorkQueue.StreamItem)
    (known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (targets : List CleanupTarget) (running : state.stopped = false)
    : let registered := state.maybeIntegrateWork item.work
      let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
      let started :=
        ({ registered.1 with queue := pruned.1 }).startNewWork
          { registered.2.newWork with newGroups := pruned.2 } registered.2 targets
      started.1.queue = state.queue.integrateStreamItem item := by
  let registered := state.maybeIntegrateWork item.work
  let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
  have complete := state.maybeIntegrateWork_complete item.work present
  dsimp only at complete
  have prunedComplete := activateRegisteredTasks_pruneEmptyGroups registered.1.queue
    registered.2.newGroups registered.2.activeTasks
  have registeredMatch := state.maybeIntegrateWork_registeredTasksMatch matching item.work known
  have prunedMatch := registeredMatch.pruneEmptyGroups registered.2.newGroups
  have members : registered.2.activeTasks.Subset pruned.1.tasks := by
    intro task member
    change task ∈ (registered.1.queue.pruneEmptyGroups registered.2.newGroups).1.tasks
    rw [ReferenceWorkQueue.State.pruneEmptyGroups_tasks]
    change task ∈ (state.maybeIntegrateWork item.work).1.queue.tasks
    rw [State.maybeIntegrateWork_tasks]
    exact List.mem_append_right _ (state.maybeIntegrateWork_activeTasks item.work none member)
  rw [activateRegisteredTasks_eq_startTasks prunedMatch _ members] at prunedComplete
  have started := State.startNewWork_queue ({ registered.1 with queue := pruned.1 })
    { registered.2.newWork with newGroups := pruned.2 } registered.2 targets
    ((state.maybeIntegrateWork_stopped item.work).trans running)
  dsimp only
  rw [started]
  have same := congrArg Prod.fst prunedComplete
  have roots := congrArg Prod.snd prunedComplete
  dsimp only at same roots
  rw [complete.1] at same roots
  rw [same, roots]
  have groups := congrArg ReferenceWorkQueue.NewWork.newGroups complete.2
  have streams := congrArg ReferenceWorkQueue.NewWork.newStreams complete.2
  simp only [IntegratedWork.newWork] at groups streams
  simp only [IntegratedWork.newWork]
  change _ = state.queue.integrateStreamItem item
  rw [groups, streams]
  rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
