import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping

/-! Reader-interruption preservation for fused removal and cache-aware startup. -/

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

/-- Cache-aware group startup never changes the graph-reader interruption guard. -/
theorem State.startGroup_stopped (state : State) (ref : Nat)
    (targets : List CleanupTarget := []) (available : List (Occurrence × Nat) := [])
    : (state.startGroup ref targets available).1.stopped = state.stopped := by
  unfold State.startGroup
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact State.removeGroup_stopped _ _ _

/-- Source installation, disposal and every group startup preserve interruption. -/
theorem State.startNewWork_stopped (state : State) (newWork : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat) := [])
    : (state.startNewWork newWork integrated targets available).1.stopped
      = state.stopped := by
  have groups (more : NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      : (more.foldl (fun (current, targets, failures) ref =>
          let (next, targets, queued) := current.startGroup ref targets available
          (next, targets, failures ++ queued)) acc).1.stopped = acc.1.stopped := by
    induction more generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        exact (ih _).trans (acc.1.startGroup_stopped ref acc.2.1 available)
  unfold State.startNewWork
  split
  · rfl
  · exact groups _ _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
