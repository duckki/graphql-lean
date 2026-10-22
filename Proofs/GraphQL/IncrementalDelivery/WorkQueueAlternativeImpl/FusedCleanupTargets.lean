import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalBookkeeping
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.HostProtocol
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection

/-! Actual removal and mixed draining preserve one ordered, duplicate-free cleanup prefix.
These claims need no generated state, output scan, native inventory or desired endpoint.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

private theorem taskStep_targets (acc : State × List CleanupTarget)
    (occurrence : Occurrence) (unique : acc.2.Nodup)
    : (fusedRemovalTaskStep acc occurrence).2.Nodup
      ∧ acc.2.IsPrefix (fusedRemovalTaskStep acc occurrence).2 := by
  unfold fusedRemovalTaskStep
  split
  · exact ⟨unique, List.prefix_refl _⟩
  · split
    · exact ⟨uniqueCleanupTargets_nodup _, uniqueCleanupTargets_append_prefix _ _ unique⟩
    · exact ⟨unique, List.prefix_refl _⟩

private theorem taskFold_targets (tasks : List Occurrence)
    (acc : State × List CleanupTarget) (unique : acc.2.Nodup)
    : (tasks.foldl fusedRemovalTaskStep acc).2.Nodup
      ∧ acc.2.IsPrefix (tasks.foldl fusedRemovalTaskStep acc).2 := by
  induction tasks generalizing acc with
  | nil => exact ⟨unique, List.prefix_refl _⟩
  | cons occurrence rest ih =>
      have step := taskStep_targets acc occurrence unique
      have next := ih (fusedRemovalTaskStep acc occurrence) step.1
      exact ⟨next.1, step.2.trans next.2⟩

theorem State.removeGroup_walk_targets (fuel : Nat) (state : State)
    (pending removed : NodeRefs) (targets : List CleanupTarget) (unique : targets.Nodup)
    : let final := State.removeGroup.walk fuel state pending removed targets
      final.2.2.Nodup ∧ targets.IsPrefix final.2.2 := by
  induction fuel generalizing state pending removed targets with
  | zero =>
      simp only [State.removeGroup.walk]
      exact ⟨unique, List.prefix_refl _⟩
  | succ fuel ih =>
      induction pending generalizing state removed targets with
      | nil =>
          simp only [State.removeGroup.walk]
          exact ⟨unique, List.prefix_refl _⟩
      | cons key rest tailIH =>
          cases found : state.queue.groupNode? key with
          | none =>
              simpa only [State.removeGroup.walk, found] using tailIH state removed targets unique
          | some group =>
              rw [State.removeGroup.walk, found]
              let folded :=
                group.tasks.foldl fusedRemovalTaskStep (eraseRemovalGroup state key, targets)
              have step :=
                taskFold_targets group.tasks (eraseRemovalGroup state key, targets) unique
              have next := ih folded.1 (group.childGroups ++ rest) (key :: removed) folded.2 step.1
              exact ⟨next.1, step.2.trans next.2⟩

theorem State.removeGroup_targets (state : State) (key : Nat)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    : (state.removeGroup key targets).2.Nodup
      ∧ targets.IsPrefix (state.removeGroup key targets).2 :=
  State.removeGroup_walk_targets _ state [key] [] targets unique

theorem fusedFailureGroupStep_targets (errors : Nat)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode) (unique : acc.2.2.Nodup)
    : (fusedFailureGroupStep errors acc group).2.2.Nodup := by
  unfold fusedFailureGroupStep
  split
  · exact unique
  · split
    · exact (acc.1.removeGroup_targets _ _ unique).1
    · exact unique

/-- Rejection replay retains one unique cleanup prefix across every owner removal. -/
theorem State.taskFailure_targets (state : State) (occurrence : Occurrence) (errors : Nat)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    : (state.taskFailure occurrence errors targets).2.2.Nodup
      ∧ targets.IsPrefix (state.taskFailure occurrence errors targets).2.2 := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
      (prior : acc.2.2.Nodup)
      : (groups.foldl (fusedFailureGroupStep errors) acc).2.2.Nodup
        ∧ acc.2.2.IsPrefix (groups.foldl (fusedFailureGroupStep errors) acc).2.2 := by
    induction groups generalizing acc with
    | nil => exact ⟨prior, List.prefix_refl _⟩
    | cons group rest ih =>
        have step := fusedFailureGroupStep_targets errors acc group prior
        have prefixTargets : acc.2.2.IsPrefix (fusedFailureGroupStep errors acc group).2.2 := by
          unfold fusedFailureGroupStep
          split
          · exact List.prefix_refl _
          · split
            · exact (acc.1.removeGroup_targets _ _ prior).2
            · exact List.prefix_refl _
        have final := ih _ step
        exact ⟨final.1, prefixTargets.trans final.2⟩
  unfold State.taskFailure
  split
  · exact ⟨unique, List.prefix_refl _⟩
  · exact loop _ _ unique

theorem State.drainReadyGroups_go_targets (fuel : Nat) (state : State)
    (targets : List CleanupTarget) (unique : targets.Nodup)
    (available : List (Occurrence × Nat) := [])
    : let final := State.drainReadyGroups.go available fuel state targets
      final.2.2.1.Nodup ∧ targets.IsPrefix final.2.2.1 := by
  induction fuel generalizing state targets with
  | zero => exact ⟨unique, List.prefix_refl _⟩
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact ⟨unique, List.prefix_refl _⟩
      · rename_i node _
        dsimp only
        have step := State.startNewWork_targets_nodup
          { state with queue := (state.queue.finishGroupSuccess node).1 }
          (state.queue.finishGroupSuccess node).2.2 {} targets unique available
        have prefixTargets := State.startNewWork_targets_prefix
          { state with queue := (state.queue.finishGroupSuccess node).1 }
          (state.queue.finishGroupSuccess node).2.2 {} targets unique available
        let started :=
          ({ state with queue := (state.queue.finishGroupSuccess node).1 }).startNewWork
          (state.queue.finishGroupSuccess node).2.2 {} targets available
        have next := ih started.1 started.2.1 step
        exact ⟨next.1, prefixTargets.trans next.2⟩

theorem State.drainReadyGroups_targets (state : State) (targets : List CleanupTarget)
    (unique : targets.Nodup) (available : List (Occurrence × Nat) := [])
    : (state.drainReadyGroups targets available).2.2.1.Nodup
      ∧ targets.IsPrefix (state.drainReadyGroups targets available).2.2.1 :=
  State.drainReadyGroups_go_targets _ state targets unique available

/-- A direct failed task requests each inline task/source cleanup identity at most once
across all its owner cuts. This concerns the actual dispatch trace, not cleanup settlement.
-/
theorem State.taskFailure_cleanupStarts_nodup (state : State) (occurrence : Occurrence)
    (errors : Nat)
    : (((state.taskFailure occurrence errors).2.2.flatMap CleanupTarget.effects).filterMap
        HostEffect.cleanupStart?).Nodup := by
  rw [cleanupEffects_starts]
  exact (state.taskFailure_targets occurrence errors [] List.nodup_nil).1

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
