import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.WorkDeclarations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationScopeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedReleaseProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskOwnerHandlers

/-! Delayed activation commutes with empty-shell pruning and shared release activation. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- A fresh child outside the supplied failure snapshot has the ordinary startup record. -/
theorem reference_startTask_eq_of_unavailable (queue : ReferenceWorkQueue.State)
    (occurrence : WorkQueueSemantics.Occurrence)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (absent : occurrence ∉ available.map Prod.fst)
    : queue.startTask occurrence available = queue.startTask occurrence := by
  have missing : available.findSome?
      (fun entry => if entry.1 == occurrence then some entry.2 else none) = none := by
    apply List.findSome?_eq_none_iff.mpr
    intro entry member
    have different : entry.1 ≠ occurrence := fun same =>
      absent (List.mem_map.mpr ⟨entry, member, same⟩)
    simp only [ReferenceWorkQueue.occurrence_beq_iff_eq, different, ↓reduceIte]
  unfold ReferenceWorkQueue.State.startTask
  rw [missing]
  rfl

/-- Starting a child list disjoint from available failures gives its ordinary eager completion. -/
theorem reference_startTasks_eq_of_unavailable (queue : ReferenceWorkQueue.State)
    (tasks : List ReferenceWorkQueue.Task)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (absent : ∀ task ∈ tasks, task.occurrence ∉ available.map Prod.fst)
    : tasks.foldl (fun current task => current.startTask task.occurrence available) queue
      = tasks.foldl (fun current task => current.startTask task.occurrence) queue := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, List.foldl_cons,
        reference_startTask_eq_of_unavailable queue task.occurrence available
          (absent task List.mem_cons_self)]
      exact ih _ (fun child member => absent child (List.mem_cons_of_mem _ member))

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
  have result := loop (queue.groupNodes.length + groups.length + 1) queue groups []
  exact result

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

/-- Delayed activation projects through startup from a valid concrete pre-startup frame.
The live-task and finite-forest premises justify fused removal. They describe the queue
before startup rather than assuming its projected endpoint.
-/
theorem State.startNewWork_queue (state : State) {work : Work}
    {parents : Nat → WorkQueueSemantics.NodeRefs}
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    (frame
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).TaskOwnerFrame
          work)
    (forest
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).RemovalForest
          parents)
    : (state.startNewWork newWork integrated targets available).1.queue
      = ((integrated.activeTasks.foldl
            (fun current task => current.startTask task.occurrence available)
            state.queue).startNewWork
          newWork available).1 :=
  congrArg Prod.fst
    (state.startNewWork_projects newWork integrated targets running available
      frame forest)

/-- Registration, pruning and actual delayed release activation recover the reference item.
Witness: full scope completion, catalogue coherence, group-only pruning and the common
release operation. The concrete delayed pre-startup queue supplies its live-task frame
and finite removal forest; cleanup targets impose no additional projection premise.
-/
theorem State.integrateStreamItem_projects {state : State} {work : Work}
    (present : state.queue.RootGroupsPresent)
    (matching : state.queue.RegisteredTasksMatch work)
    (item : ReferenceWorkQueue.StreamItem)
    (known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (targets : List CleanupTarget) (running : state.stopped = false)
    {parents : Nat → WorkQueueSemantics.NodeRefs}
    (frame
      : let registered := state.maybeIntegrateWork item.work
        let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
        (registered.2.activeTasks.foldl
          (fun current task => current.startTask task.occurrence) pruned.1).TaskOwnerFrame
          work)
    (forest
      : let registered := state.maybeIntegrateWork item.work
        let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
        (registered.2.activeTasks.foldl
          (fun current task => current.startTask task.occurrence) pruned.1).RemovalForest
          parents)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    (unavailable
      : ∀ task ∈ item.work.tasks, task.occurrence ∉ available.map Prod.fst := by
        intro task _ member; cases member)
    : let registered := state.maybeIntegrateWork item.work
      let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
      let started :=
        ({ registered.1 with queue := pruned.1 }).startNewWork
          { registered.2.newWork with newGroups := pruned.2 } registered.2 targets
          available
      (started.1.queue, started.2.2)
      = let reference :=
          ReferenceWorkQueue.streamItemStep (state.queue, [], [], [], []) item available
        (reference.1, reference.2.2.2.2) := by
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
  have startsEq := reference_startTasks_eq_of_unavailable pruned.1 registered.2.activeTasks
    available (fun task member => unavailable task
      (state.maybeIntegrateWork_activeTasks item.work none member))
  have actualFrame : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) pruned.1
      ).TaskOwnerFrame work := by rw [startsEq]; exact frame
  have actualForest : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available) pruned.1
      ).RemovalForest parents := by rw [startsEq]; exact forest
  have started := State.startNewWork_projects ({ registered.1 with queue := pruned.1 })
    { registered.2.newWork with newGroups := pruned.2 } registered.2 targets
    ((state.maybeIntegrateWork_stopped item.work).trans running) available actualFrame actualForest
  dsimp only
  rw [started, startsEq]
  have same := congrArg Prod.fst prunedComplete
  have roots := congrArg Prod.snd prunedComplete
  dsimp only at same roots
  rw [complete.1] at same roots
  rw [same, roots]
  have groups := congrArg ReferenceWorkQueue.NewWork.newGroups complete.2
  have streams := congrArg ReferenceWorkQueue.NewWork.newStreams complete.2
  simp only [IntegratedWork.newWork] at groups streams
  simp only [IntegratedWork.newWork]
  rw [groups, streams]
  rfl

private theorem reference_cacheTaskFailures_rootGroups {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (roots : WorkQueueSemantics.NodeRefs)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).cacheTaskFailures
        available
      = { queue.cacheTaskFailures available with rootGroups := roots } := by
  rw [(show ({ queue with rootGroups := roots } : ReferenceWorkQueue.State).TaskNodeKeysUnique
    from unique).cacheTaskFailures_eq available, unique.cacheTaskFailures_eq available]

private theorem reference_cacheTaskFailures_startStream {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (ref : Nat)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (queue.startStream ref).cacheTaskFailures available
      = (queue.cacheTaskFailures available).startStream ref := by
  have streams := congrArg ReferenceWorkQueue.State.streams
    (queue.cacheTaskFailures_frame available)
  have roots := congrArg ReferenceWorkQueue.State.rootStreams
    (queue.cacheTaskFailures_frame available)
  dsimp only at streams roots
  have lookup : (queue.cacheTaskFailures available).stream? ref = queue.stream? ref := by
    unfold ReferenceWorkQueue.State.stream?
    rw [streams]
  unfold ReferenceWorkQueue.State.startStream
  rw [lookup, roots]
  split
  · rfl
  · rw [(show ({ queue with rootStreams := queue.rootStreams ++ [ref] }
        : ReferenceWorkQueue.State).TaskNodeKeysUnique from unique).cacheTaskFailures_eq available,
      unique.cacheTaskFailures_eq available]

/-- Common cache exposure preserves release startup and its queued failure notices.
Witness: roots install the same metadata, and each group start reads the equal exposed
queue before inspecting errors. Stream activation commutes with cache exposure. With no
released groups the residual queues need only agree after exposure.
-/
theorem reference_startNewWork_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (released : ReferenceWorkQueue.NewWork)
    : (
        (left.startNewWork released available).1.cacheTaskFailures available,
        (left.startNewWork released available).2
      )
      = (
        (right.startNewWork released available).1.cacheTaskFailures available,
        (right.startNewWork released available).2
      ) := by
  have roots : left.rootGroups = right.rootGroups := by
    have equal := congrArg ReferenceWorkQueue.State.rootGroups same
    simpa only [ReferenceWorkQueue.State.cacheTaskFailures_rootGroups] using equal
  let leftInitial : ReferenceWorkQueue.State :=
    { left with rootGroups := left.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref }
  let rightInitial : ReferenceWorkQueue.State :=
    { right with
      rootGroups := right.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref }
  have initial
      : leftInitial.cacheTaskFailures available = rightInitial.cacheTaskFailures available := by
    dsimp only [leftInitial, rightInitial]
    rw [reference_cacheTaskFailures_rootGroups leftUnique,
      reference_cacheTaskFailures_rootGroups rightUnique, same, roots]
  let groupStep := fun (acc : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent)
      (ref : Nat) =>
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have groupFold (refs : List Nat)
      (first second : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent)
      (equal : first.1.cacheTaskFailures available = second.1.cacheTaskFailures available)
      (notices : first.2 = second.2)
      : ((refs.foldl groupStep first).1.cacheTaskFailures available, (refs.foldl groupStep first).2)
        = ((refs.foldl groupStep second).1.cacheTaskFailures available,
          (refs.foldl groupStep second).2) := by
    cases refs with
    | nil => exact Prod.ext equal notices
    | cons ref rest =>
        have step : first.1.startGroup ref available = second.1.startGroup ref available := by
          unfold ReferenceWorkQueue.State.startGroup
          rw [equal]
        have joined : groupStep first ref = groupStep second ref := by
          unfold groupStep
          rw [step, notices]
        simp only [List.foldl_cons, joined]
  have groupKeys (refs : List Nat)
      (acc : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent)
      (unique : acc.1.TaskNodeKeysUnique)
      : (refs.foldl groupStep acc).1.TaskNodeKeysUnique := by
    induction refs generalizing acc with
    | nil => exact unique
    | cons ref rest ih => exact ih _ (unique.startGroup ref available)
  have streamFold (refs : List Nat) (first second : ReferenceWorkQueue.State)
      (firstUnique : first.TaskNodeKeysUnique) (secondUnique : second.TaskNodeKeysUnique)
      (equal : first.cacheTaskFailures available = second.cacheTaskFailures available)
      : (refs.foldl ReferenceWorkQueue.State.startStream first).cacheTaskFailures available
        = (refs.foldl ReferenceWorkQueue.State.startStream second).cacheTaskFailures available := by
    induction refs generalizing first second with
    | nil => exact equal
    | cons ref rest ih =>
        have firstKeys : (first.startStream ref).TaskNodeKeysUnique := by
          unfold ReferenceWorkQueue.State.startStream
          split <;> exact firstUnique
        have secondKeys : (second.startStream ref).TaskNodeKeysUnique := by
          unfold ReferenceWorkQueue.State.startStream
          split <;> exact secondUnique
        apply ih _ _ firstKeys secondKeys
        rw [reference_cacheTaskFailures_startStream firstUnique,
          reference_cacheTaskFailures_startStream secondUnique, equal]
  have afterGroups := groupFold (released.newGroups.map Execution.DeliveryNode.ref)
    (leftInitial, []) (rightInitial, []) initial rfl
  apply Prod.ext
  · exact streamFold _ _ _ (groupKeys _ _ leftUnique) (groupKeys _ _ rightUnique)
      (congrArg Prod.fst afterGroups)
  · change (List.foldl groupStep (leftInitial, [])
        (released.newGroups.map Execution.DeliveryNode.ref)).2
      = (List.foldl groupStep (rightInitial, [])
        (released.newGroups.map Execution.DeliveryNode.ref)).2
    have notices := congrArg Prod.snd afterGroups
    exact notices

/-- Fused delayed startup preserves the exposed registration relation and exact notices.
Witness: concrete pre-startup ownership/forest certificates give the fused projection;
the common exposed queue then determines the reference startup and its failure aggregate.
The supplied relation concerns registration state, not desired output behavior.
-/
theorem State.startNewWork_projects_after_cache (state : State) {work : Work}
    {parents : Nat → WorkQueueSemantics.NodeRefs}
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (unique : state.queue.TaskNodeKeysUnique) (reference : ReferenceWorkQueue.State)
    (referenceUnique : reference.TaskNodeKeysUnique)
    (same
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).cacheTaskFailures
          available
        = reference.cacheTaskFailures available)
    (frame
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).TaskOwnerFrame
          work)
    (forest
      : (integrated.activeTasks.foldl
          (fun current task => current.startTask task.occurrence available)
          state.queue).RemovalForest
          parents)
    : (
        (state.startNewWork newWork integrated targets
          available).1.queue.cacheTaskFailures
          available,
        (state.startNewWork newWork integrated targets available).2.2
      )
      = (
        (reference.startNewWork newWork available).1.cacheTaskFailures available,
        (reference.startNewWork newWork available).2
      ) := by
  have keys (tasks : List ReferenceWorkQueue.Task) (current : ReferenceWorkQueue.State)
      (unique : current.TaskNodeKeysUnique)
      : (tasks.foldl (fun current task => current.startTask task.occurrence available)
          current).TaskNodeKeysUnique := by
    induction tasks generalizing current with
    | nil => exact unique
    | cons task rest ih => exact ih _ (unique.startTask task.occurrence available)
  have projected := state.startNewWork_projects newWork integrated targets running available
    frame forest
  have exposed := congrArg
    (fun pair : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent =>
      (pair.1.cacheTaskFailures available, pair.2)) projected
  exact exposed.trans
    (reference_startNewWork_cache_congr (keys _ _ unique) referenceUnique
      available same newWork)

/-- Empty-shell pruning commutes with exposing the same computation failures.
Witness: pruning reads group records only and preserves the entire task-node store.
-/
theorem reference_cacheTaskFailures_pruneEmptyGroups {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (groups : List Execution.DeliveryNode)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (
        (queue.pruneEmptyGroups groups).1.cacheTaskFailures available,
        (queue.pruneEmptyGroups groups).2
      )
      = (queue.cacheTaskFailures available).pruneEmptyGroups groups := by
  conv =>
    rhs
    rw [unique.cacheTaskFailures_eq available, pruneEmptyGroups_with_taskNodes]
  rw [(unique.pruneEmptyGroups groups).cacheTaskFailures_eq available,
    ReferenceWorkQueue.State.pruneEmptyGroups_taskNodes]

private theorem reference_flushGroupTask_cache {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (values : List Execution.ExecutionGroupValue) (streams : WorkQueueSemantics.NodeRefs)
    (occurrence : WorkQueueSemantics.Occurrence)
    : ReferenceWorkQueue.flushGroupTask
        (queue.cacheTaskFailures available, values, streams) occurrence
      = let next := ReferenceWorkQueue.flushGroupTask (queue, values, streams) occurrence
        (next.1.cacheTaskFailures available, next.2) := by
  unfold ReferenceWorkQueue.flushGroupTask
  rw [unique.cacheTaskFailures_lookup available occurrence]
  cases found : queue.taskNode? occurrence with
  | none => rfl
  | some node =>
      simp only [Option.map_some]
      rw [unique.cacheTaskFailures_removeTask available occurrence]

/-- Successful task flushing preserves values and held-stream refs under cache exposure.
Witness: each lookup keeps value/stream metadata, and removing its task commutes with
cache exposure. Every residual queue retains unique task keys for the next iteration.
-/
theorem reference_flushGroupTasks_cache {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (tasks : List WorkQueueSemantics.Occurrence)
    (values : List Execution.ExecutionGroupValue) (streams : WorkQueueSemantics.NodeRefs)
    : tasks.foldl ReferenceWorkQueue.flushGroupTask
        (queue.cacheTaskFailures available, values, streams)
      = let next := tasks.foldl ReferenceWorkQueue.flushGroupTask (queue, values, streams)
        (next.1.cacheTaskFailures available, next.2) := by
  induction tasks generalizing queue values streams with
  | nil => rfl
  | cons task rest ih =>
      rw [List.foldl_cons, List.foldl_cons, reference_flushGroupTask_cache unique]
      have keys
          : (ReferenceWorkQueue.flushGroupTask
              (queue, values, streams) task).1.TaskNodeKeysUnique := by
        unfold ReferenceWorkQueue.flushGroupTask
        split
        · exact unique
        · exact unique.removeTask task
      exact ih keys _ _

/-- Successful group closure commutes with exposing cached computation failures.
Witness: the task flush retains exact values and held streams, while its metadata-only
closing/pruning tail is independent of the task-node store. This concerns the closure
operation; selecting a ready group remains a separate step of the drain.
-/
theorem reference_cacheTaskFailures_finishGroupSuccess {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (group : ReferenceWorkQueue.GroupNode)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (queue.cacheTaskFailures available).finishGroupSuccess group
      = (
        (queue.finishGroupSuccess group).1.cacheTaskFailures available,
        (queue.finishGroupSuccess group).2
      ) := by
  let finish (acc : ReferenceWorkQueue.State × List Execution.ExecutionGroupValue
      × WorkQueueSemantics.NodeRefs) :=
    let current : ReferenceWorkQueue.State :=
      { acc.1 with
        groupNodes := acc.1.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := acc.1.rootGroups.filter (· != group.group.node.ref) }
    let children := group.childGroups.filterMap
      (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
    let pruned := current.pruneEmptyGroups children
    let streams := acc.2.2.filterMap
      (fun ref => (pruned.1.stream? ref).map ReferenceWorkQueue.Stream.node)
    let events := if acc.2.1.isEmpty then []
      else [Execution.WorkQueueEvent.groupValues group.group.node acc.2.1]
    (pruned.1, events ++ [.groupSuccess group.group.node pruned.2 streams],
      (⟨pruned.2, streams⟩ : ReferenceWorkQueue.NewWork))
  have nodes (acc : ReferenceWorkQueue.State × List Execution.ExecutionGroupValue
      × WorkQueueSemantics.NodeRefs) : (finish acc).1.taskNodes = acc.1.taskNodes := by
    dsimp only [finish]
    rw [ReferenceWorkQueue.State.pruneEmptyGroups_taskNodes]
  have withNodes (acc : ReferenceWorkQueue.State × List Execution.ExecutionGroupValue
      × WorkQueueSemantics.NodeRefs) (tasks : List ReferenceWorkQueue.TaskNode)
      : finish ({ acc.1 with taskNodes := tasks }, acc.2)
        = ({ (finish acc).1 with taskNodes := tasks }, (finish acc).2) := by
    let current : ReferenceWorkQueue.State :=
      { acc.1 with
        groupNodes := acc.1.groupNodes.filter
          (fun node => node.group.node.ref != group.group.node.ref)
        rootGroups := acc.1.rootGroups.filter (· != group.group.node.ref) }
    let children := group.childGroups.filterMap
      (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
    have pruning := pruneEmptyGroups_with_taskNodes current children tasks
    dsimp only [current, children, ReferenceWorkQueue.State.groupNode?] at pruning
    dsimp only [finish, ReferenceWorkQueue.State.groupNode?]
    conv =>
      lhs
      rw [pruning]
    rfl
  have tail (acc : ReferenceWorkQueue.State × List Execution.ExecutionGroupValue
      × WorkQueueSemantics.NodeRefs) (unique : acc.1.TaskNodeKeysUnique)
      : finish (acc.1.cacheTaskFailures available, acc.2)
        = ((finish acc).1.cacheTaskFailures available, (finish acc).2) := by
    have keys : (finish acc).1.TaskNodeKeysUnique := by
      unfold ReferenceWorkQueue.State.TaskNodeKeysUnique
      rw [nodes]
      exact unique
    rw [unique.cacheTaskFailures_eq available, withNodes,
      keys.cacheTaskFailures_eq available, nodes]
  have keys (tasks : List WorkQueueSemantics.Occurrence)
      (acc : ReferenceWorkQueue.State × List Execution.ExecutionGroupValue
        × WorkQueueSemantics.NodeRefs) (unique : acc.1.TaskNodeKeysUnique)
      : (tasks.foldl ReferenceWorkQueue.flushGroupTask acc).1.TaskNodeKeysUnique := by
    induction tasks generalizing acc with
    | nil => exact unique
    | cons task rest ih =>
        apply ih
        unfold ReferenceWorkQueue.flushGroupTask
        split
        · exact unique
        · exact unique.removeTask task
  change finish (group.tasks.foldl ReferenceWorkQueue.flushGroupTask
      (queue.cacheTaskFailures available, [], []))
    = ((finish (group.tasks.foldl ReferenceWorkQueue.flushGroupTask
          (queue, [], []))).1.cacheTaskFailures available,
        (finish (group.tasks.foldl ReferenceWorkQueue.flushGroupTask (queue, [], []))).2)
  rw [reference_flushGroupTasks_cache unique]
  exact tail _ (keys _ _ unique)

/-- Equal exposed queues give equal successful closure output and exposed residual state. -/
theorem reference_finishGroupSuccess_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (group : ReferenceWorkQueue.GroupNode)
    : (
        (left.finishGroupSuccess group).1.cacheTaskFailures available,
        (left.finishGroupSuccess group).2
      )
      = (
        (right.finishGroupSuccess group).1.cacheTaskFailures available,
        (right.finishGroupSuccess group).2
      ) := by
  rw [← reference_cacheTaskFailures_finishGroupSuccess leftUnique,
    ← reference_cacheTaskFailures_finishGroupSuccess rightUnique, same]

/-- Recursive successful draining preserves exposed queues and both output components.
Witness: exposed queues select the same ready group; closure preserves values/release work,
startup preserves queued failures, and each recursive iteration retains the same relation.
The initial finite budgets agree because cache exposure changes no group records.
-/
theorem reference_drainReadyGroups_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    : (
        (left.drainReadyGroups available).1.cacheTaskFailures available,
        (left.drainReadyGroups available).2
      )
      = (
        (right.drainReadyGroups available).1.cacheTaskFailures available,
        (right.drainReadyGroups available).2
      ) := by
  let choose := fun queue : ReferenceWorkQueue.State =>
    queue.rootGroups.findSome? fun ref => do
      let node ← queue.groupNode? ref
      if node.pending == 0 then some node else none
  have metadata {first second : ReferenceWorkQueue.State}
      (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
      : first.groupNodes = second.groupNodes ∧ first.rootGroups = second.rootGroups := by
    have groups := congrArg ReferenceWorkQueue.State.groupNodes same
    have roots := congrArg ReferenceWorkQueue.State.rootGroups same
    exact ⟨by simpa only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] using groups,
      by simpa only [ReferenceWorkQueue.State.cacheTaskFailures_rootGroups] using roots⟩
  have loop (fuel : Nat) {first second : ReferenceWorkQueue.State}
      (firstUnique : first.TaskNodeKeysUnique) (secondUnique : second.TaskNodeKeysUnique)
      (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
      : ((ReferenceWorkQueue.State.drainReadyGroups.go available fuel first).1.cacheTaskFailures
            available,
          (ReferenceWorkQueue.State.drainReadyGroups.go available fuel first).2)
        = ((ReferenceWorkQueue.State.drainReadyGroups.go available fuel second).1.cacheTaskFailures
            available,
          (ReferenceWorkQueue.State.drainReadyGroups.go available fuel second).2) := by
    induction fuel generalizing first second with
    | zero => exact Prod.ext same rfl
    | succ fuel ih =>
        have fields := metadata same
        have selected : choose first = choose second := by
          dsimp only [choose, ReferenceWorkQueue.State.groupNode?]
          rw [fields.1, fields.2]
        cases chosen : choose second with
        | none =>
            have earlier : choose first = none := selected.trans chosen
            dsimp only [choose] at earlier chosen
            simp only [ReferenceWorkQueue.State.drainReadyGroups.go, earlier, chosen]
            exact Prod.ext same rfl
        | some node =>
            have earlier : choose first = some node := selected.trans chosen
            dsimp only [choose] at earlier chosen
            let firstClosed := first.finishGroupSuccess node
            let secondClosed := second.finishGroupSuccess node
            have closed := reference_finishGroupSuccess_cache_congr firstUnique secondUnique
              available same node
            have cached := congrArg Prod.fst closed
            have released := congrArg
              (fun result : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
                  × ReferenceWorkQueue.NewWork => result.2.2) closed
            have values := congrArg
              (fun result : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
                  × ReferenceWorkQueue.NewWork => result.2.1) closed
            have startup := reference_startNewWork_cache_congr
              (firstUnique.finishGroupSuccess node) (secondUnique.finishGroupSuccess node)
              available cached secondClosed.2.2
            have startupQueue := congrArg Prod.fst startup
            have startupNotices := congrArg Prod.snd startup
            have recursive := ih
              ((firstUnique.finishGroupSuccess node).startNewWork secondClosed.2.2 available)
              ((secondUnique.finishGroupSuccess node).startNewWork secondClosed.2.2 available)
              startupQueue
            have finalQueue := congrArg Prod.fst recursive
            have finalValues := congrArg
              (fun result : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
                  × List ReferenceWorkQueue.GroupFailureEvent => result.2.1) recursive
            have finalNotices := congrArg
              (fun result : ReferenceWorkQueue.State × List Execution.WorkQueueEvent
                  × List ReferenceWorkQueue.GroupFailureEvent => result.2.2) recursive
            simp only [ReferenceWorkQueue.State.drainReadyGroups.go, earlier, chosen]
            rw [released]
            apply Prod.ext
            · exact finalQueue
            · apply Prod.ext
              · rw [values, finalValues]
              · rw [startupNotices, finalNotices]
  have length := congrArg List.length (metadata same).1
  unfold ReferenceWorkQueue.State.drainReadyGroups
  rw [length]
  exact loop _ leftUnique rightUnique same

private theorem reference_cacheTaskFailures_putGroupNode
    {queue : ReferenceWorkQueue.State} (unique : queue.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (node : ReferenceWorkQueue.GroupNode)
    : (queue.putGroupNode node).cacheTaskFailures available
      = (queue.cacheTaskFailures available).putGroupNode node := by
  rw [(unique.putGroupNode node).cacheTaskFailures_eq available,
    unique.cacheTaskFailures_eq available]
  rfl

private theorem reference_successGroupStep_cache {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (events : List Execution.WorkQueueEvent) (released : ReferenceWorkQueue.NewWork)
    (group : Execution.DeliveryNode)
    : ReferenceWorkQueue.successGroupStep
        (queue.cacheTaskFailures available, events, released) group
      = let next := ReferenceWorkQueue.successGroupStep (queue, events, released) group
        (next.1.cacheTaskFailures available, next.2) := by
  have lookup : (queue.cacheTaskFailures available).groupNode? group.ref
      = queue.groupNode? group.ref := by
    unfold ReferenceWorkQueue.State.groupNode?
    rw [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes]
  unfold ReferenceWorkQueue.successGroupStep
  dsimp only
  rw [lookup]
  cases found : queue.groupNode? group.ref with
  | none => rfl
  | some node =>
      simp only
      rw [← reference_cacheTaskFailures_putGroupNode unique available]
      simp only [ReferenceWorkQueue.State.cacheTaskFailures_rootGroups]
      split
      · rw [reference_cacheTaskFailures_finishGroupSuccess (unique.putGroupNode _)]
      · rfl

/-- The contributor settlement fold commutes with cache exposure.
Witness: each counter update preserves rejection slots, readiness reads unchanged metadata,
and each selected successful closure preserves output values and release descriptors.
-/
theorem reference_successGroupFold_cache {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (groups : List Execution.DeliveryNode) (events : List Execution.WorkQueueEvent)
    (released : ReferenceWorkQueue.NewWork)
    : groups.foldl ReferenceWorkQueue.successGroupStep
        (queue.cacheTaskFailures available, events, released)
      = let next :=
          groups.foldl ReferenceWorkQueue.successGroupStep (queue, events, released)
        (next.1.cacheTaskFailures available, next.2) := by
  induction groups generalizing queue events released with
  | nil => rfl
  | cons group rest ih =>
      rw [List.foldl_cons, List.foldl_cons, reference_successGroupStep_cache unique]
      have keys
          : (ReferenceWorkQueue.successGroupStep
              (queue, events, released) group).1.TaskNodeKeysUnique := by
        unfold ReferenceWorkQueue.successGroupStep
        dsimp only
        split
        · exact unique
        · split
          · exact (unique.putGroupNode _).finishGroupSuccess _
          · exact unique.putGroupNode _
      exact ih keys _ _

/-- Equal exposed queues retain equal settlement output and release descriptors. -/
theorem reference_successGroupFold_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (groups : List Execution.DeliveryNode) (events : List Execution.WorkQueueEvent)
    (released : ReferenceWorkQueue.NewWork)
    : (
        (groups.foldl ReferenceWorkQueue.successGroupStep
          (left, events, released)).1.cacheTaskFailures
          available,
        (groups.foldl ReferenceWorkQueue.successGroupStep (left, events, released)).2
      )
      = (
        (groups.foldl ReferenceWorkQueue.successGroupStep
          (right, events, released)).1.cacheTaskFailures
          available,
        (groups.foldl ReferenceWorkQueue.successGroupStep (right, events, released)).2
      ) := by
  rw [← reference_successGroupFold_cache leftUnique,
    ← reference_successGroupFold_cache rightUnique, same]

private theorem reference_cacheTaskFailures_tasks {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (tasks : List ReferenceWorkQueue.Task)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : ({ queue with tasks } : ReferenceWorkQueue.State).cacheTaskFailures available
      = { queue.cacheTaskFailures available with tasks } := by
  rw [(show ({ queue with tasks } : ReferenceWorkQueue.State).TaskNodeKeysUnique from unique
      ).cacheTaskFailures_eq available, unique.cacheTaskFailures_eq available]

private theorem reference_registerOwner_keys {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (task : ReferenceWorkQueue.Task)
    (group : Execution.DeliveryNode)
    : (registerOwner task queue group).TaskNodeKeysUnique := by
  unfold registerOwner
  split
  · exact unique
  · split
    · exact unique
    · exact unique.putGroupNode _

private theorem reference_registerOwner_cache_congr
    {left right : ReferenceWorkQueue.State} (leftUnique : left.TaskNodeKeysUnique)
    (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (task : ReferenceWorkQueue.Task) (group : Execution.DeliveryNode)
    : (registerOwner task left group).cacheTaskFailures available
      = (registerOwner task right group).cacheTaskFailures available := by
  have groups := congrArg ReferenceWorkQueue.State.groupNodes same
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at groups
  have lookup : left.groupNode? group.ref = right.groupNode? group.ref := by
    unfold ReferenceWorkQueue.State.groupNode?
    rw [groups]
  unfold registerOwner
  rw [lookup]
  cases found : right.groupNode? group.ref with
  | none => exact same
  | some node =>
      simp only
      split
      · exact same
      · rw [reference_cacheTaskFailures_putGroupNode leftUnique,
          reference_cacheTaskFailures_putGroupNode rightUnique, same]

/-- Reference task registration preserves equality after common cache exposure.
Witness: permanent catalogue and owner updates preserve the relation; the eager-start
branch appends the same fresh task record to both exposed stores. This holds for raw work.
-/
theorem reference_addTask_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (task : ReferenceWorkQueue.Task)
    : (left.addTask task).cacheTaskFailures available
      = (right.addTask task).cacheTaskFailures available := by
  have tasks := congrArg ReferenceWorkQueue.State.tasks same
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_tasks] at tasks
  let firstRegistered : ReferenceWorkQueue.State := { left with tasks := left.tasks ++ [task] }
  let secondRegistered : ReferenceWorkQueue.State := { right with tasks := right.tasks ++ [task] }
  have initial : firstRegistered.cacheTaskFailures available
      = secondRegistered.cacheTaskFailures available := by
    dsimp only [firstRegistered, secondRegistered]
    rw [reference_cacheTaskFailures_tasks leftUnique,
      reference_cacheTaskFailures_tasks rightUnique, same, tasks]
  have fold (groups : List Execution.DeliveryNode) {first second : ReferenceWorkQueue.State}
      (firstUnique : first.TaskNodeKeysUnique) (secondUnique : second.TaskNodeKeysUnique)
      (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
      : (groups.foldl (registerOwner task) first).cacheTaskFailures available
          = (groups.foldl (registerOwner task) second).cacheTaskFailures available
        ∧ (groups.foldl (registerOwner task) first).TaskNodeKeysUnique
        ∧ (groups.foldl (registerOwner task) second).TaskNodeKeysUnique := by
    induction groups generalizing first second with
    | nil => exact ⟨same, firstUnique, secondUnique⟩
    | cons group rest ih =>
        exact ih (reference_registerOwner_keys firstUnique task group)
          (reference_registerOwner_keys secondUnique task group)
          (reference_registerOwner_cache_congr firstUnique secondUnique available same task group)
  let first := task.groups.foldl (registerOwner task) firstRegistered
  let second := task.groups.foldl (registerOwner task) secondRegistered
  have afterGroups := fold task.groups (first := firstRegistered) (second := secondRegistered)
    leftUnique rightUnique initial
  have roots := congrArg ReferenceWorkQueue.State.rootGroups afterGroups.1
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_rootGroups] at roots
  have presence := congrArg
    (fun queue : ReferenceWorkQueue.State =>
      queue.acceptsGraphEvent (.taskFailure task.occurrence 0))
    afterGroups.1
  rw [ReferenceWorkQueue.State.cacheTaskFailures_acceptsGraphEvent,
    ReferenceWorkQueue.State.cacheTaskFailures_acceptsGraphEvent] at presence
  have absent : (first.taskNode? task.occurrence).isNone
      = (second.taskNode? task.occurrence).isNone := by
    change (first.taskNode? task.occurrence).isSome = (second.taskNode? task.occurrence).isSome
      at presence
    cases leftFound : first.taskNode? task.occurrence <;>
      cases rightFound : second.taskNode? task.occurrence <;> simp_all
  have active : task.groups.any (fun group => first.rootGroups.contains group.ref)
      = task.groups.any (fun group => second.rootGroups.contains group.ref) := by rw [roots]
  change (if task.groups.any (fun group => first.rootGroups.contains group.ref)
        && (first.taskNode? task.occurrence).isNone then
      { first with taskNodes := first.taskNodes ++ [{ task }] } else first).cacheTaskFailures
        available
    = (if task.groups.any (fun group => second.rootGroups.contains group.ref)
        && (second.taskNode? task.occurrence).isNone then
      { second with taskNodes := second.taskNodes ++ [{ task }] } else second).cacheTaskFailures
        available
  rw [active, absent]
  split
  · rename_i starts
    have secondAbsent := Option.isNone_iff_eq_none.mp (Bool.and_eq_true_iff.mp starts).2
    have firstAbsent : first.taskNode? task.occurrence = none :=
      Option.isNone_iff_eq_none.mp (by rw [absent]; exact (Bool.and_eq_true_iff.mp starts).2)
    exact afterGroups.2.1.appendTaskNode_cache_congr afterGroups.2.2 available afterGroups.1
      { task } firstAbsent secondAbsent
  · exact afterGroups.1

private theorem reference_addGroups_with_taskNodes (queue : ReferenceWorkQueue.State)
    (groups : List ReferenceWorkQueue.Group) (nodes : List ReferenceWorkQueue.TaskNode)
    : ({ queue with taskNodes := nodes } : ReferenceWorkQueue.State).addGroups groups
      = (
        { (queue.addGroups groups).1 with taskNodes := nodes },
        (queue.addGroups groups).2
      ) := by
  have add (current : ReferenceWorkQueue.State) (group : ReferenceWorkQueue.Group)
      : ({ current with taskNodes := nodes } : ReferenceWorkQueue.State).addGroup group
        = { current.addGroup group with taskNodes := nodes } := by
    have lookup (ref : Nat) :
        ({current with taskNodes := nodes} : ReferenceWorkQueue.State).groupNode? ref
          = current.groupNode? ref := rfl
    by_cases seen : (current.registeredGroups.contains group.node.ref
        || (current.groupNode? group.node.ref).isSome) = true
    · simp only [ReferenceWorkQueue.State.addGroup, lookup, seen, ite_true]
    · cases parentEq : group.parent with
      | none =>
          simp only [ReferenceWorkQueue.State.addGroup, lookup, seen, parentEq, Bool.false_eq_true, ite_false]
      | some parent =>
          cases found : current.groupNode? parent with
          | none =>
              by_cases marked : current.cancelledGroups.contains parent = true <;>
                simp only [ReferenceWorkQueue.State.addGroup, lookup, seen, parentEq, found, marked, Bool.false_eq_true, ite_true, ite_false]
          | some node =>
              simp only [ReferenceWorkQueue.State.addGroup, lookup, seen, parentEq, found,
                ReferenceWorkQueue.State.putGroupNode, Bool.false_eq_true, ite_false]
  let replace (acc : ReferenceWorkQueue.State × List Execution.DeliveryNode × WorkQueueSemantics.NodeRefs) :=
    ({acc.1 with taskNodes := nodes}, acc.2)
  have visit (fuel : Nat)
      (acc : ReferenceWorkQueue.State × List Execution.DeliveryNode × WorkQueueSemantics.NodeRefs)
      (group : ReferenceWorkQueue.Group)
      : ReferenceWorkQueue.State.addGroups.go groups fuel (replace acc) group
        = replace (ReferenceWorkQueue.State.addGroups.go groups fuel acc group) := by
    induction fuel generalizing acc group with
    | zero => rfl
    | succ fuel ih =>
        obtain ⟨current, roots, visited⟩ := acc
        have lookup (ref : Nat) :
            ({current with taskNodes := nodes} : ReferenceWorkQueue.State).groupNode? ref
              = current.groupNode? ref := rfl
        by_cases seen : visited.contains group.node.ref = true
        · simp only [ReferenceWorkQueue.State.addGroups.go, replace, seen, ite_true]
        · by_cases registered : (current.registeredGroups.contains group.node.ref
              || (current.groupNode? group.node.ref).isSome) = true
          · simp only [ReferenceWorkQueue.State.addGroups.go, replace, lookup, seen, registered, Bool.false_eq_true, ite_true, ite_false]
          · cases found
                  : group.parent.bind
                      (fun parent =>
                        groups.find? (fun candidate => candidate.node.ref == parent)) with
            | none =>
                simp only [ReferenceWorkQueue.State.addGroups.go, replace, lookup, seen,
                  registered, found, add, Bool.false_eq_true, ite_false]
            | some parent =>
                simp only [ReferenceWorkQueue.State.addGroups.go, replace, lookup, seen,
                  registered, Bool.false_eq_true, ite_false, found]
                rw [ih (current, roots, visited ++ [group.node.ref]) parent]
                dsimp only [replace]
                rw [add]
  have fold (more : List ReferenceWorkQueue.Group)
      (acc : ReferenceWorkQueue.State × List Execution.DeliveryNode × WorkQueueSemantics.NodeRefs)
      : more.foldl (fun acc group => ReferenceWorkQueue.State.addGroups.go groups
          (groups.length + 1) acc group) (replace acc)
        = replace (more.foldl (fun acc group => ReferenceWorkQueue.State.addGroups.go groups
          (groups.length + 1) acc group) acc) := by
    induction more generalizing acc with
    | nil => rfl
    | cons group rest ih => rw [List.foldl_cons, visit, ih, List.foldl_cons]
  unfold ReferenceWorkQueue.State.addGroups
  change (let next := groups.foldl _ (replace (queue, [], [])); (next.1, next.2.1)) = _
  rw [fold]

/-- Group registration commutes with exposing computation failures.
Witness: registration and parent linking depend on group metadata and retain task nodes.
-/
theorem reference_cacheTaskFailures_addGroups {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (groups : List ReferenceWorkQueue.Group)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : ((queue.addGroups groups).1.cacheTaskFailures available, (queue.addGroups groups).2)
      = (queue.cacheTaskFailures available).addGroups groups := by
  conv =>
    rhs
    rw [unique.cacheTaskFailures_eq available, reference_addGroups_with_taskNodes]
  rw [(unique.addGroups groups).cacheTaskFailures_eq available,
    ReferenceWorkQueue.State.addGroups_taskNodes]

/-- Equal exposed queues register the same groups and return the same root notices. -/
theorem reference_addGroups_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (groups : List ReferenceWorkQueue.Group)
    : ((left.addGroups groups).1.cacheTaskFailures available, (left.addGroups groups).2)
      = (
        (right.addGroups groups).1.cacheTaskFailures available,
        (right.addGroups groups).2
      ) := by
  rw [reference_cacheTaskFailures_addGroups leftUnique,
    reference_cacheTaskFailures_addGroups rightUnique, same]

/-- Stream registration commutes with cache exposure, including producer-held stream refs.
Witness: stream selection ignores task rejection slots; producer lookup preserves all
other node fields, and replacing its held-stream metadata commutes with exposure.
-/
theorem reference_cacheTaskFailures_addStreams {queue : ReferenceWorkQueue.State}
    (unique : queue.TaskNodeKeysUnique) (streams : List ReferenceWorkQueue.Stream)
    (producer : Option WorkQueueSemantics.Occurrence)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (
        (queue.addStreams streams producer).1.cacheTaskFailures available,
        (queue.addStreams streams producer).2
      )
      = (queue.cacheTaskFailures available).addStreams streams producer := by
  have fields := congrArg ReferenceWorkQueue.State.streams (queue.cacheTaskFailures_frame available)
  dsimp only at fields
  have lookup (ref : Nat)
      : (queue.cacheTaskFailures available).stream? ref = queue.stream? ref := by
    unfold ReferenceWorkQueue.State.stream?
    rw [fields]
  let fresh := streams.foldl (fun selected stream =>
    if (queue.stream? stream.node.ref).isSome
        || selected.any (fun known => known.node.ref == stream.node.ref) then selected
    else selected ++ [stream]) []
  let current : ReferenceWorkQueue.State := { queue with streams := queue.streams ++ fresh }
  let finish (current : ReferenceWorkQueue.State) :=
    match producer with
    | none => (current, fresh.map ReferenceWorkQueue.Stream.node)
    | some occurrence =>
        match current.taskNode? occurrence with
        | none => (current, [])
        | some node =>
            (current.putTaskNode
              { node with
                childStreams := node.childStreams ++ fresh.map
                  (fun stream : ReferenceWorkQueue.Stream => stream.node.ref) }, [])
  have currentKeys : current.TaskNodeKeysUnique := unique
  have cached : ({ queue.cacheTaskFailures available with streams := queue.streams ++ fresh }
      : ReferenceWorkQueue.State) = current.cacheTaskFailures available := by
    rw [unique.cacheTaskFailures_eq available, currentKeys.cacheTaskFailures_eq available]
  have ready : (queue.cacheTaskFailures available).addStreams streams producer
      = finish (current.cacheTaskFailures available) := by
    unfold ReferenceWorkQueue.State.addStreams
    simp only [lookup, fields]
    rw [cached]
    rfl
  rw [ready]
  change ((finish current).1.cacheTaskFailures available, (finish current).2)
    = finish (current.cacheTaskFailures available)
  cases selected : producer with
  | none => simp only [finish, selected]
  | some occurrence =>
      simp only [finish, selected]
      rw [currentKeys.cacheTaskFailures_lookup available occurrence]
      cases found : current.taskNode? occurrence with
      | none => rfl
      | some node =>
          simp only [Option.map_some]
          rw [currentKeys.cacheTaskFailures_putTaskNode available]

/-- Equal exposed queues register the same streams and return the same root-stream list. -/
theorem reference_addStreams_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (streams : List ReferenceWorkQueue.Stream)
    (producer : Option WorkQueueSemantics.Occurrence)
    : (
        (left.addStreams streams producer).1.cacheTaskFailures available,
        (left.addStreams streams producer).2
      )
      = (
        (right.addStreams streams producer).1.cacheTaskFailures available,
        (right.addStreams streams producer).2
      ) := by
  rw [reference_cacheTaskFailures_addStreams leftUnique,
    reference_cacheTaskFailures_addStreams rightUnique, same]

/-- Whole reference scope registration preserves exposed queues and release descriptors.
Witness: group registration, each eager task insertion and held-stream registration retain
the common cache relation, with independent unique-key certificates at every stage.
-/
theorem reference_maybeIntegrateWork_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (incoming : ReferenceWorkQueue.Work)
    (producer : Option WorkQueueSemantics.Occurrence := none)
    : (
        (left.maybeIntegrateWork incoming producer).1.cacheTaskFailures available,
        (left.maybeIntegrateWork incoming producer).2
      )
      = (
        (right.maybeIntegrateWork incoming producer).1.cacheTaskFailures available,
        (right.maybeIntegrateWork incoming producer).2
      ) := by
  have grouped := reference_addGroups_cache_congr leftUnique rightUnique available same
    incoming.groups
  have groupedQueue := congrArg Prod.fst grouped
  have groups := congrArg Prod.snd grouped
  have fold (tasks : List ReferenceWorkQueue.Task) {first second : ReferenceWorkQueue.State}
      (firstUnique : first.TaskNodeKeysUnique) (secondUnique : second.TaskNodeKeysUnique)
      (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
      : (tasks.foldl ReferenceWorkQueue.State.addTask first).cacheTaskFailures available
        = (tasks.foldl ReferenceWorkQueue.State.addTask second).cacheTaskFailures available := by
    induction tasks generalizing first second with
    | nil => exact same
    | cons task rest ih =>
        exact ih (firstUnique.addTask task) (secondUnique.addTask task)
          (reference_addTask_cache_congr firstUnique secondUnique available same task)
  have taskKeys (tasks : List ReferenceWorkQueue.Task) (current : ReferenceWorkQueue.State)
      (unique : current.TaskNodeKeysUnique)
      : (tasks.foldl ReferenceWorkQueue.State.addTask current).TaskNodeKeysUnique := by
    induction tasks generalizing current with
    | nil => exact unique
    | cons task rest ih => exact ih _ (unique.addTask task)
  have registered := fold incoming.tasks (leftUnique.addGroups incoming.groups)
    (rightUnique.addGroups incoming.groups) groupedQueue
  have streamed := reference_addStreams_cache_congr
    (taskKeys incoming.tasks _ (leftUnique.addGroups incoming.groups))
    (taskKeys incoming.tasks _ (rightUnique.addGroups incoming.groups))
    available registered incoming.streams producer
  have result := congrArg
    (fun pair : ReferenceWorkQueue.State × List Execution.DeliveryNode =>
      (pair.1, (⟨(left.addGroups incoming.groups).2, pair.2⟩ : ReferenceWorkQueue.NewWork)))
    streamed
  exact result.trans (by rw [groups]; rfl)

/-- Equal exposed queues prune the same shells and return the same released group list. -/
theorem reference_pruneEmptyGroups_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (groups : List Execution.DeliveryNode)
    : (
        (left.pruneEmptyGroups groups).1.cacheTaskFailures available,
        (left.pruneEmptyGroups groups).2
      )
      = (
        (right.pruneEmptyGroups groups).1.cacheTaskFailures available,
        (right.pruneEmptyGroups groups).2
      ) := by
  rw [reference_cacheTaskFailures_pruneEmptyGroups leftUnique,
    reference_cacheTaskFailures_pruneEmptyGroups rightUnique, same]

/-- A reference item step preserves exposed queues and every carrier metadata field.
Witness: registration preserves the complete new-work descriptor, pruning preserves group
notices, and cache-aware startup preserves queued failures before metadata accumulation.
-/
theorem reference_streamItemStep_cache_congr {left right : ReferenceWorkQueue.State}
    (leftUnique : left.TaskNodeKeysUnique) (rightUnique : right.TaskNodeKeysUnique)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : left.cacheTaskFailures available = right.cacheTaskFailures available)
    (item : ReferenceWorkQueue.StreamItem) (groups streams : List Execution.DeliveryNode)
    (values : List Execution.StreamItemValue)
    (failures : List ReferenceWorkQueue.GroupFailureEvent)
    : let first :=
        ReferenceWorkQueue.streamItemStep (left, groups, streams, values, failures)
          item available
      let second :=
        ReferenceWorkQueue.streamItemStep (right, groups, streams, values, failures)
          item available
      (first.1.cacheTaskFailures available, first.2)
      = (second.1.cacheTaskFailures available, second.2) := by
  let firstRegistered := left.maybeIntegrateWork item.work
  let secondRegistered := right.maybeIntegrateWork item.work
  have registered := reference_maybeIntegrateWork_cache_congr leftUnique rightUnique
    available same item.work
  have registeredQueue := congrArg Prod.fst registered
  have registeredWork := congrArg Prod.snd registered
  change firstRegistered.2 = secondRegistered.2 at registeredWork
  have pruned := reference_pruneEmptyGroups_cache_congr
    (leftUnique.maybeIntegrateWork item.work) (rightUnique.maybeIntegrateWork item.work)
    available registeredQueue secondRegistered.2.newGroups
  let firstPruned := firstRegistered.1.pruneEmptyGroups secondRegistered.2.newGroups
  let secondPruned := secondRegistered.1.pruneEmptyGroups secondRegistered.2.newGroups
  have prunedQueue := congrArg Prod.fst pruned
  have prunedGroups := congrArg Prod.snd pruned
  change firstPruned.2 = secondPruned.2 at prunedGroups
  let released : ReferenceWorkQueue.NewWork :=
    { secondRegistered.2 with newGroups := secondPruned.2 }
  have started := reference_startNewWork_cache_congr
    ((leftUnique.maybeIntegrateWork item.work).pruneEmptyGroups secondRegistered.2.newGroups)
    ((rightUnique.maybeIntegrateWork item.work).pruneEmptyGroups secondRegistered.2.newGroups)
    available prunedQueue released
  have accumulated := congrArg
    (fun pair : ReferenceWorkQueue.State × List ReferenceWorkQueue.GroupFailureEvent =>
      (pair.1, groups ++ secondPruned.2, streams ++ secondRegistered.2.newStreams,
        values ++ [item.value], failures ++ pair.2)) started
  dsimp only [ReferenceWorkQueue.streamItemStep]
  rw [registeredWork]
  change (((firstPruned.1.startNewWork
          { secondRegistered.2 with newGroups := firstPruned.2 } available).1).cacheTaskFailures
        available, groups ++ firstPruned.2, streams ++ secondRegistered.2.newStreams,
      values ++ [item.value], failures ++ (firstPruned.1.startNewWork
        { secondRegistered.2 with newGroups := firstPruned.2 } available).2)
    = (((secondPruned.1.startNewWork released available).1).cacheTaskFailures available,
      groups ++ secondPruned.2, streams ++ secondRegistered.2.newStreams,
      values ++ [item.value], failures ++ (secondPruned.1.startNewWork released available).2)
  rw [prunedGroups]
  exact accumulated

/-- One delayed item startup agrees with reference item startup after common exposure.
Witness: exact eager scope completion commutes with pruning; the cache-aware starts share
its exposed queue, and concrete ownership/forest certificates license fused cleanup.
-/
theorem State.integrateStreamItem_cache_projects {state : State} {work : Work}
    (present : state.queue.RootGroupsPresent)
    (matching : state.queue.RegisteredTasksMatch work)
    (unique : state.queue.TaskNodeKeysUnique) (item : ReferenceWorkQueue.StreamItem)
    (known : ∀ task ∈ item.work.tasks, ReferenceWorkQueue.TaskMatches work task)
    (targets : List CleanupTarget) (running : state.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (startupFrames
      : let prepared := state.queue.maybeIntegrateWork item.work
        let pruned := prepared.1.pruneEmptyGroups prepared.2.newGroups
        ∃ parents, pruned.1.TaskOwnerFrame work ∧ pruned.1.RemovalForest parents)
    : let registered := state.maybeIntegrateWork item.work
      let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
      let started :=
        ({ registered.1 with queue := pruned.1 }).startNewWork
          { registered.2.newWork with newGroups := pruned.2 } registered.2 targets
          available
      let reference :=
        ReferenceWorkQueue.streamItemStep (state.queue, [], [], [], []) item available
      (started.1.queue.cacheTaskFailures available, started.2.2)
      = (reference.1.cacheTaskFailures available, reference.2.2.2.2) := by
  let registered := state.maybeIntegrateWork item.work
  let pruned := registered.1.queue.pruneEmptyGroups registered.2.newGroups
  let prepared := state.queue.maybeIntegrateWork item.work
  let reference := prepared.1.pruneEmptyGroups prepared.2.newGroups
  have complete := state.maybeIntegrateWork_complete item.work present
  dsimp only at complete
  have sameGroups := congrArg ReferenceWorkQueue.NewWork.newGroups complete.2
  simp only [IntegratedWork.newWork] at sameGroups
  have pruning : (activateRegisteredTasks pruned.1 registered.2.activeTasks, pruned.2)
      = reference := by
    calc
      _ = (activateRegisteredTasks registered.1.queue
            registered.2.activeTasks).pruneEmptyGroups
            registered.2.newGroups :=
        activateRegisteredTasks_pruneEmptyGroups registered.1.queue registered.2.newGroups
          registered.2.activeTasks
      _ = reference := by rw [complete.1, sameGroups]
  have referenceKeys : reference.1.TaskNodeKeysUnique :=
    (unique.maybeIntegrateWork item.work).pruneEmptyGroups prepared.2.newGroups
  have queue := congrArg Prod.fst pruning
  have groups := congrArg Prod.snd pruning
  dsimp only at queue groups
  have initialKeys : pruned.1.TaskNodeKeysUnique := by
    have activatedKeys := referenceKeys
    rw [← queue] at activatedKeys
    exact activatedKeys.sublist ((activateRegisteredTasks_taskNodes_sublist _ _).map _)
  have prunedMatch := (state.maybeIntegrateWork_registeredTasksMatch matching item.work known
    ).pruneEmptyGroups registered.2.newGroups
  have members : registered.2.activeTasks.Subset pruned.1.tasks := by
    intro task member
    rw [ReferenceWorkQueue.State.pruneEmptyGroups_tasks, State.maybeIntegrateWork_tasks]
    exact List.mem_append_right _ (state.maybeIntegrateWork_activeTasks item.work none member)
  have actualStarts := activateRegisteredTasks_eq_startTasks prunedMatch
    registered.2.activeTasks members
  have exposed := initialKeys.startTasks_cache_congr initialKeys available rfl
    (registered.2.activeTasks.map ReferenceWorkQueue.Task.occurrence)
  simp only [List.foldl_map] at exposed
  rw [← actualStarts, queue] at exposed
  have activatedKeys : (registered.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence available)
      pruned.1).TaskNodeKeysUnique := by
    have cached := referenceKeys.cacheTaskFailures available
    rw [← exposed] at cached
    simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique,
      ReferenceWorkQueue.State.cacheTaskFailures_taskOccurrences] using cached
  obtain ⟨parents, frame, forest⟩ := startupFrames
  have actualFrame := ReferenceWorkQueue.State.TaskOwnerFrame.of_cacheTaskFailures_eq
    activatedKeys available exposed frame
  have fields := congrArg ReferenceWorkQueue.State.groupNodes exposed
  simp only [ReferenceWorkQueue.State.cacheTaskFailures_groupNodes] at fields
  have actualForest := forest.of_subset (by rw [fields]; exact List.Subset.refl _)
  let released : ReferenceWorkQueue.NewWork :=
    { registered.2.newWork with newGroups := pruned.2 }
  let referenceReleased : ReferenceWorkQueue.NewWork :=
    { prepared.2 with newGroups := reference.2 }
  have sameRelease : released = referenceReleased := by
    dsimp only [released, referenceReleased]
    rw [complete.2, groups]
  have started := State.startNewWork_projects_after_cache ({ registered.1 with queue := pruned.1 })
    released registered.2 targets ((state.maybeIntegrateWork_stopped item.work).trans running)
    available initialKeys reference.1 referenceKeys exposed actualFrame actualForest
  change ((({ registered.1 with queue := pruned.1 }).startNewWork
          released registered.2 targets available).1.queue.cacheTaskFailures available,
      (({ registered.1 with queue := pruned.1 }).startNewWork
        released registered.2 targets available).2.2)
    = ((reference.1.startNewWork referenceReleased available).1.cacheTaskFailures available,
      (reference.1.startNewWork referenceReleased available).2)
  rw [sameRelease] at started ⊢
  exact started

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
