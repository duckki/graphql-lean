import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! The real fused removal and ready drain never retire or reopen the graph reader. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)

private theorem removalTaskStep_stopped (acc : State × List CleanupTarget)
    (occurrence : Occurrence)
    : (fusedRemovalTaskStep acc occurrence).1.stopped = acc.1.stopped := by
  unfold fusedRemovalTaskStep
  split
  · rfl
  · split <;> rfl

private theorem removalTaskFold_stopped (tasks : List Occurrence)
    (acc : State × List CleanupTarget)
    : (tasks.foldl fusedRemovalTaskStep acc).1.stopped = acc.1.stopped := by
  induction tasks generalizing acc with
  | nil => rfl
  | cons occurrence rest ih =>
      exact (ih _).trans (removalTaskStep_stopped acc occurrence)

theorem State.removeGroup_walk_stopped (fuel : Nat) (state : State)
    (pending removed : NodeRefs) (targets : List CleanupTarget)
    : (State.removeGroup.walk fuel state pending removed targets).1.stopped
      = state.stopped := by
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
                (removalTaskFold_stopped group.tasks (eraseRemovalGroup state key, targets))

theorem State.removeGroup_stopped (state : State) (key : Nat)
    (targets : List CleanupTarget)
    : (state.removeGroup key targets).1.stopped = state.stopped :=
  State.removeGroup_walk_stopped _ state [key] [] targets

theorem State.drainReadyGroups_go_stopped (fuel : Nat) (state : State)
    (targets : List CleanupTarget)
    : (State.drainReadyGroups.go fuel state targets).1.stopped = state.stopped := by
  induction fuel generalizing state targets with
  | zero => rfl
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · rfl
      · rename_i group _
        cases cached : group.failure with
        | some errors =>
            dsimp only
            exact (ih _ _).trans (State.removeGroup_stopped state group.group.node.ref targets)
        | none =>
            dsimp only
            exact (ih _ _).trans (State.startNewWork_stopped _ _ {} targets)

theorem State.drainReadyGroups_stopped (state : State) (targets : List CleanupTarget)
    : (state.drainReadyGroups targets).1.stopped = state.stopped :=
  State.drainReadyGroups_go_stopped _ state targets

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
              let folded := group.tasks.foldl fusedRemovalTaskStep (eraseRemovalGroup state key, targets)
              exact (ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2).trans
                (removalTaskFold_terminated group.tasks (eraseRemovalGroup state key, targets))

theorem State.removeGroup_terminated (state : State) (key : Nat)
    (targets : List CleanupTarget)
    : (state.removeGroup key targets).1.queue.terminated = state.queue.terminated :=
  State.removeGroup_walk_terminated _ state [key] [] targets

/-- Delayed starts change computation records and roots, not semantic termination. -/
theorem State.startNewWork_terminated (state : State) (roots : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.terminated
      = state.queue.terminated := by
  cases running : state.stopped with
  | true => simp only [State.startNewWork, running, ↓reduceIte]
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running, ReferenceWorkQueue.State.startNewWork_terminated]
      have step (queue : ReferenceWorkQueue.State) (task : ReferenceWorkQueue.Task)
          : (queue.startTask task.occurrence).terminated = queue.terminated := by
        unfold ReferenceWorkQueue.State.startTask
        split
        · rfl
        · split <;> rfl
      exact ReferenceWorkQueue.fold_projection ReferenceWorkQueue.State.terminated
        (fun (queue : ReferenceWorkQueue.State) (task : ReferenceWorkQueue.Task) =>
          queue.startTask task.occurrence) step _ _

theorem State.drainReadyGroups_go_terminated (fuel : Nat) (state : State)
    (targets : List CleanupTarget)
    : (State.drainReadyGroups.go fuel state targets).1.queue.terminated
      = state.queue.terminated := by
  induction fuel generalizing state targets with
  | zero => rfl
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · rfl
      · rename_i node _
        cases cached : node.failure with
        | some errors =>
            dsimp only
            exact (ih _ _).trans (state.removeGroup_terminated node.group.node.ref targets)
        | none =>
            dsimp only
            exact (ih _ _).trans ((State.startNewWork_terminated _ _ {} targets).trans
              (ReferenceWorkQueue.State.finishGroupSuccess_terminated state.queue node))

theorem State.drainReadyGroups_terminated (state : State) (targets : List CleanupTarget)
    : (state.drainReadyGroups targets).1.queue.terminated = state.queue.terminated :=
  State.drainReadyGroups_go_terminated _ state targets

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
