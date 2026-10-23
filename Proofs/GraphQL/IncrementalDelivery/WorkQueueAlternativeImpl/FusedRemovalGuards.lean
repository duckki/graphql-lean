import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalInterruption
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! The real fused removal and ready drain never retire or reopen the graph reader. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

def fusedFailureGroupStep (errors : Nat)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : State × List WorkQueueEvent × List CleanupTarget :=
  match acc.1.queue.groupNode? group.ref with
  | none => acc
  | some node =>
      if acc.1.queue.rootGroups.contains group.ref then
        let reduced := acc.1.finishGroupFailure node errors acc.2.2
        (
          reduced.1,
          acc.2.1 ++ [.groupFailure reduced.2.1.group reduced.2.1.errors],
          reduced.2.2
        )
      else
        acc

private theorem fusedFailureGroupStep_stopped (errors : Nat)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : (fusedFailureGroupStep errors acc group).1.stopped = acc.1.stopped := by
  unfold fusedFailureGroupStep
  split
  · rfl
  · split
    · exact acc.1.removeGroup_stopped _ _
    · rfl

theorem State.taskFailure_stopped (state : State) (occurrence : Occurrence) (errors : Nat)
    (targets : List CleanupTarget := [])
    : (state.taskFailure occurrence errors targets).1.stopped = state.stopped := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × List CleanupTarget)
      : (groups.foldl (fusedFailureGroupStep errors) acc).1.stopped = acc.1.stopped := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        exact (ih _).trans (fusedFailureGroupStep_stopped errors acc group)
  unfold State.taskFailure
  split
  · rfl
  · exact loop _ _

/-- Successful draining and cached child startup preserve the reader interruption flag. -/
theorem State.drainReadyGroups_go_stopped (fuel : Nat) (state : State)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat) := [])
    : (State.drainReadyGroups.go available fuel state targets).1.stopped
      = state.stopped := by
  induction fuel generalizing state targets with
  | zero => rfl
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · rfl
      · exact (ih _ _).trans (State.startNewWork_stopped _ _ {} targets available)

/-- Actual ready draining leaves the reader interruption flag unchanged. -/
theorem State.drainReadyGroups_stopped (state : State) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat) := [])
    : (state.drainReadyGroups targets available).1.stopped = state.stopped :=
  State.drainReadyGroups_go_stopped _ state targets available

-----------------------------------------------------------------------------------------
-- Semantic termination is likewise unchanged until the enclosing batch boundary
-----------------------------------------------------------------------------------------

private theorem removalTaskStep_terminated (acc : State × List CleanupTarget)
    (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.queue.terminated
      = acc.1.queue.terminated := by
  unfold fusedRemovalTaskStep
  split
  · rfl
  · split <;> rfl

private theorem removalTaskFold_terminated (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    : (tasks.foldl fusedRemovalTaskStep acc).1.queue.terminated
      = acc.1.queue.terminated := by
  induction tasks generalizing acc with
  | nil => rfl
  | cons occurrence rest ih =>
      exact (ih _).trans (removalTaskStep_terminated acc occurrence)

theorem State.removeGroup_walk_terminated (fuel : Nat) (state : State)
    (pending removed : NodeRefs) (targets : List CleanupTarget)
    : (State.removeGroup.walk fuel state pending removed targets).1.queue.terminated
      = state.queue.terminated := by
  induction fuel generalizing state pending removed targets with
  | zero => simp only [State.removeGroup.walk]
  | succ fuel ih =>
      induction pending generalizing state removed targets with
      | nil => simp only [State.removeGroup.walk]
      | cons key rest tailIH =>
          cases found : state.queue.groupNode? key with
          | none =>
              simpa only [State.removeGroup.walk, found] using tailIH state removed targets
          | some group =>
              rw [State.removeGroup.walk, found]
              let folded := group.tasks.foldl fusedRemovalTaskStep
                (eraseRemovalGroup state key, targets)
              exact (ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2).trans
                (removalTaskFold_terminated group.tasks (eraseRemovalGroup state key, targets))

theorem State.removeGroup_terminated (state : State) (key : Nat)
    (targets : List CleanupTarget)
    : (state.removeGroup key targets).1.queue.terminated = state.queue.terminated :=
  State.removeGroup_walk_terminated _ state [key] [] targets

/-- Cache exposure, private starts and fused startup removal preserve semantic termination. -/
theorem State.startGroup_terminated (state : State) (ref : Nat)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat) := [])
    : (state.startGroup ref targets available).1.queue.terminated
      = state.queue.terminated := by
  have cached := state.queue.cacheTaskFailures_terminated available
  have tasks (more : List Occurrence) (current : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task available)
          current).terminated = current.terminated := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact (tasks _ _).trans cached
    · exact (State.removeGroup_terminated _ _ _).trans cached

/-- Delayed starts preserve termination through their actual source/task/group folds.
The field frame uses neither full queue projection nor a finite removal forest.
-/
theorem State.startNewWork_terminated (state : State) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    (available : List (Occurrence × Nat) := [])
    : (state.startNewWork roots integrated targets available).1.queue.terminated
      = state.queue.terminated := by
  have sources (more : List Execution.DeliveryNode) (current : ReferenceWorkQueue.State)
      : (more.foldl (fun current stream => current.startStream stream.ref)
          current).terminated = current.terminated := by
    induction more generalizing current with
    | nil => rfl
    | cons stream rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startStream
        split <;> rfl
  have tasks (more : List ReferenceWorkQueue.Task) (current : ReferenceWorkQueue.State)
      : (more.foldl (fun current task => current.startTask task.occurrence available)
          current).terminated = current.terminated := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
  have groups (more : NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      : (more.foldl (fun (current, targets, failures) ref =>
          let (next, targets, queued) := current.startGroup ref targets available
          (next, targets, failures ++ queued)) acc).1.queue.terminated
        = acc.1.queue.terminated := by
    induction more generalizing acc with
    | nil => rfl
    | cons ref rest ih => exact (ih _).trans (acc.1.startGroup_terminated ref _ available)
  unfold State.startNewWork
  split
  · rfl
  · exact (groups _ _).trans ((tasks _ _).trans (sources _ _))

private theorem fusedFailureGroupStep_terminated (errors : Nat)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : (fusedFailureGroupStep errors acc group).1.queue.terminated
      = acc.1.queue.terminated := by
  unfold fusedFailureGroupStep
  split
  · rfl
  · split
    · exact acc.1.removeGroup_terminated _ _
    · rfl

theorem State.taskFailure_terminated (state : State) (occurrence : Occurrence)
    (errors : Nat) (targets : List CleanupTarget := [])
    : (state.taskFailure occurrence errors targets).1.queue.terminated
      = state.queue.terminated := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × List CleanupTarget)
      : (groups.foldl (fusedFailureGroupStep errors) acc).1.queue.terminated
        = acc.1.queue.terminated := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        exact (ih _).trans (fusedFailureGroupStep_terminated errors acc group)
  unfold State.taskFailure
  split
  · rfl
  · exact loop _ _

/-- Successful draining and child startup preserve semantic termination at every budget. -/
theorem State.drainReadyGroups_go_terminated (fuel : Nat) (state : State)
    (targets : List CleanupTarget) (available : List (Occurrence × Nat) := [])
    : (State.drainReadyGroups.go available fuel state targets).1.queue.terminated
      = state.queue.terminated := by
  induction fuel generalizing state targets with
  | zero => rfl
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · rfl
      · rename_i node _
        exact (ih _ _).trans ((State.startNewWork_terminated _ _ {} targets available).trans
          (ReferenceWorkQueue.State.finishGroupSuccess_terminated state.queue node))

/-- Actual draining leaves semantic termination for the enclosing batch boundary. -/
theorem State.drainReadyGroups_terminated (state : State) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat) := [])
    : (state.drainReadyGroups targets available).1.queue.terminated
      = state.queue.terminated :=
  State.drainReadyGroups_go_terminated _ state targets available

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
