import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRegistration

/-! Cancellation history across integration, activation, and successful retirement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A pointwise state invariant extends through a finite fold.
Witness: list induction threads the actual intermediate state. -/
private theorem fold_preserves {α β : Type} (property : β → Prop) (step : β → α → β)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List α) (current : β) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

-----------------------------------------------------------------------------------------
-- Only group registration can add cancellation keys during work integration
-----------------------------------------------------------------------------------------

/-- Task registration leaves cancellation history unchanged.
Witness: membership installation and optional activation update only group/task nodes. -/
theorem State.addTask_cancelledGroups (queue : State) (task : Task)
    : (queue.addTask task).cancelledGroups = queue.cancelledGroups := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.key with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved (current : State) (group : Execution.DeliveryNode)
      (prior : current.cancelledGroups = queue.cancelledGroups)
      : (step current group).cancelledGroups = queue.cancelledGroups := by
    unfold step
    split
    · exact prior
    · split <;> exact prior
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let current := task.groups.foldl step registered
  have same : current.cancelledGroups = queue.cancelledGroups :=
    fold_preserves (fun current : State => current.cancelledGroups = queue.cancelledGroups)
      step preserved task.groups registered rfl
  change (if task.groups.any (fun group => current.rootGroups.contains group.key)
      && (current.taskNode? task.occurrence).isNone then
      { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).cancelledGroups = queue.cancelledGroups
  split <;> exact same

/-- Stream integration does not alter group cancellation history.
Witness: both root and producer-linked registration update only streams and task nodes. -/
theorem State.addStreams_cancelledGroups (queue : State) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.cancelledGroups
      = queue.cancelledGroups := by
  unfold State.addStreams
  split
  · rfl
  · dsimp only
    split <;> rfl

/-- Work integration changes cancellation keys exactly as its group-registration stage.
Witness: task folds and stream registration preserve that stage's resulting history. -/
theorem State.maybeIntegrateWork_cancelledGroups (queue : State) (work : Work)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.cancelledGroups
      = (queue.addGroups work.groups).1.cancelledGroups := by
  let grouped := (queue.addGroups work.groups).1
  have preserved (current : State) (task : Task)
      (prior : current.cancelledGroups = grouped.cancelledGroups)
      : (current.addTask task).cancelledGroups = grouped.cancelledGroups := by
    rw [State.addTask_cancelledGroups, prior]
  have folded := fold_preserves
    (fun current : State => current.cancelledGroups = grouped.cancelledGroups)
    State.addTask preserved work.tasks grouped rfl
  let tasked := work.tasks.foldl State.addTask grouped
  change (tasked.addStreams work.streams parentTask).1.cancelledGroups = grouped.cancelledGroups
  rw [State.addStreams_cancelledGroups]
  exact folded

/-- More failed occurrences retain every existing cancellation witness.
Witness: monotonicity of the independent invalidation relation. -/
theorem State.CancelledGroupsSupported.weaken {queue work before after}
    (supported : State.CancelledGroupsSupported queue work before)
    (included : before.Subset after)
    : queue.CancelledGroupsSupported work after := by
  intro key member
  exact (supported key member).mono included

/-- Integrating a matched work chunk preserves causal cancellation provenance.
Witness: group registration propagates invalidation; later stages do not alter its keys.
-/
theorem State.CancelledGroupsSupported.maybeIntegrateWork {queue work failed}
    (supported : State.CancelledGroupsSupported queue work failed) (newWork : Work)
    (parentTask : Option Occurrence)
    (matching
      : ∀ group ∈ newWork.groups,
          ∃ dependencies producer,
            NodeAt work group.node .group dependencies producer
            ∧ group.parent = dependencies.head?)
    : (queue.maybeIntegrateWork newWork parentTask).1.CancelledGroupsSupported work
        failed := by
  intro key member
  rw [State.maybeIntegrateWork_cancelledGroups queue newWork parentTask] at member
  exact supported.addGroups newWork.groups matching key member

-----------------------------------------------------------------------------------------
-- Successful retirement and activation do not record cancellations
-----------------------------------------------------------------------------------------

/-- Empty-shell pruning preserves cancellation history exactly.
Witness: its recursive traversal filters live nodes but never records failure keys. -/
theorem State.pruneEmptyGroups_cancelledGroups (queue : State)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.cancelledGroups = queue.cancelledGroups := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.cancelledGroups
        = current.cancelledGroups := by
    induction fuel generalizing current remaining kept with
    | zero => rfl
    | succ fuel ih =>
        cases remaining with
        | nil => rfl
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _
            · split <;> exact ih _ _ _
  exact loop _ queue groups []

/-- Task activation cannot add a group cancellation.
Witness: its lookup branches only install task nodes. -/
private theorem State.startTask_cancelledGroups (queue : State) (occurrence : Occurrence)
    : (queue.startTask occurrence).cancelledGroups = queue.cancelledGroups := by
  unfold State.startTask
  split
  · rfl
  · split <;> rfl

/-- Group activation only starts its existing tasks and records no cancellation.
Witness: task-start preservation across the group's membership fold. -/
private theorem State.startGroup_cancelledGroups (queue : State) (key : Nat)
    : (queue.startGroup key).cancelledGroups = queue.cancelledGroups := by
  unfold State.startGroup
  split
  · rfl
  · split
    · rfl
    · exact fold_preserves
        (fun current : State => current.cancelledGroups = queue.cancelledGroups)
        State.startTask (fun current task prior =>
          (current.startTask_cancelledGroups task).trans prior) _ queue rfl

/-- Announcing and starting released work leaves cancellation keys unchanged.
Witness: both activation folds only change roots and task-start bookkeeping. -/
theorem State.startNewWork_cancelledGroups (queue : State) (work : NewWork)
    : (queue.startNewWork work).cancelledGroups = queue.cancelledGroups := by
  let current : State :=
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.key }
  have grouped := fold_preserves
    (fun current : State => current.cancelledGroups = queue.cancelledGroups)
    State.startGroup (fun current group prior =>
      (current.startGroup_cancelledGroups group).trans prior)
    (work.newGroups.map Execution.DeliveryNode.key) current rfl
  apply fold_preserves
    (fun current : State => current.cancelledGroups = queue.cancelledGroups)
    State.startStream ?_ _ _ grouped
  intro current stream prior
  unfold State.startStream
  split <;> exact prior

/-- Successful group closure preserves every earlier cancellation key and adds none.
Witness: flushing task memberships, removing the successful shell, and child pruning
each leave cancellation history unchanged. -/
theorem State.finishGroupSuccess_cancelledGroups (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.cancelledGroups = queue.cancelledGroups := by
  let step (acc : State × List ExecutionGroupValue × Keys) (task : Occurrence) :=
    let (current, values, streams) := acc
    match current.taskNode? task with
    | none => (current, values, streams)
    | some taskNode =>
        let values := match taskNode.value with
          | none => values
          | some value => values ++ [value]
        (current.removeTask task, values, streams ++ taskNode.childStreams)
  have preserved (acc : State × List ExecutionGroupValue × Keys) (task : Occurrence)
      (prior : acc.1.cancelledGroups = queue.cancelledGroups)
      : (step acc task).1.cancelledGroups = queue.cancelledGroups := by
    unfold step
    dsimp only
    split <;> exact prior
  let flushed := (group.tasks.foldl step (queue, [], [])).1
  have same : flushed.cancelledGroups = queue.cancelledGroups :=
    fold_preserves (fun acc : State × List ExecutionGroupValue × Keys =>
      acc.1.cancelledGroups = queue.cancelledGroups)
      step preserved group.tasks (queue, [], []) rfl
  let current : State :=
    { flushed with
      groupNodes := flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key) }
  let children := group.childGroups.filterMap
    (fun key => (current.groupNode? key).map (fun node => node.group.node))
  change (current.pruneEmptyGroups children).1.cancelledGroups = queue.cancelledGroups
  exact (current.pruneEmptyGroups_cancelledGroups children).trans same

-----------------------------------------------------------------------------------------
-- Queue initialization supplies the base case without source assumptions
-----------------------------------------------------------------------------------------

/-- No initial work chunk starts with a group marked cancelled.
Witness: empty-history registration followed only by pruning and activation. -/
theorem createWorkQueue_cancelledGroups_empty (work : Work)
    : (State.initialize work).cancelledGroups = [] := by
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  change (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 }).cancelledGroups = []
  rw [State.startNewWork_cancelledGroups, State.pruneEmptyGroups_cancelledGroups,
    State.maybeIntegrateWork_cancelledGroups, State.addGroups_cancelledGroups_empty rfl]

/-- Initial cancellation provenance is unconditional, even for raw work chunks.
Witness: the cancellation history is empty; no host-source or output premise is used. -/
theorem createWorkQueue_cancelledGroupsSupported (initialWork : Work)
    (work : Execution.Work) (failed : List Occurrence)
    : (State.initialize initialWork).CancelledGroupsSupported work failed := by
  intro key member
  rw [createWorkQueue_cancelledGroups_empty] at member
  cases member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
