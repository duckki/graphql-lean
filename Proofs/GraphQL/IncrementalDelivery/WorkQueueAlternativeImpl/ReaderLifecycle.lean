import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationHostEffects
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResponseReplay

/-! Once-only response-finished hook starts for finite reader runs. Not effect quiescence. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

private theorem cleanupBlocks_noFinish (targets : List CleanupTarget)
    : (targets.flatMap
        (fun target =>
          match target with
          | .task occurrence => [HostEffect.abortTask occurrence]
          | .stream key => [.cancelSource key, .abortStreamQueue key])).countP
        HostEffect.isResponseFinished
      = 0 := by
  induction targets with
  | nil => rfl
  | cons target rest ih =>
      cases target <;> simp [List.flatMap_cons, HostEffect.isResponseFinished, ih]

theorem State.cancel_noFinish (state : State)
    : state.cancel.2.countP HostEffect.isResponseFinished = 0 := by
  rw [State.cancel_effects]
  split
  · rfl
  · exact cleanupBlocks_noFinish _

private theorem graphFold_finishCount (batch : List GraphEvent)
    (result : GraphBatchResult)
    : (batch.foldl GraphBatchResult.handleGraphEvent result).effects.countP
        HostEffect.isResponseFinished
      = result.effects.countP HostEffect.isResponseFinished := by
  induction batch generalizing result with
  | nil => rfl
  | cons event rest ih =>
      rw [List.foldl_cons, ih]
      simp only [GraphBatchResult.handleGraphEvent, List.countP_append,
        State.handleGraphEvent_noFinish, Nat.add_zero]

theorem State.handleGraphEvents_noFinish (state : State) (batch : List GraphEvent)
    : (state.handleGraphEvents batch).effects.countP HostEffect.isResponseFinished
      = 0 := by
  have empty := graphFold_finishCount batch ({ state } : GraphBatchResult)
  unfold State.handleGraphEvents
  split
  · rfl
  · dsimp only
    split
    · simp only [List.countP_append, State.cancel_noFinish, Nat.add_zero]
      exact empty
    · exact empty

/-- The hook-start counter and finished flag agree through one step, for arbitrary raw inputs. -/
theorem ResponseStreamCursor.handleBatch_finishCount (cursor : ResponseStreamCursor)
    (batch : List GraphEvent)
    : (cursor.handleBatch batch).2.2.countP HostEffect.isResponseFinished
        + (if cursor.finished then 1 else 0)
      = if (cursor.handleBatch batch).2.1.finished then 1 else 0 := by
  cases running : cursor.finished with
  | true => simp [ResponseStreamCursor.handleBatch, running]
  | false =>
      simp only [ResponseStreamCursor.handleBatch, running, Bool.false_eq_true, ↓reduceIte]
      by_cases silent : (cursor.queue.handleGraphEvents batch).workQueueEvents.isEmpty = true
      · simp [silent, State.handleGraphEvents_noFinish]
      · by_cases continued :
            (cursor.publisher.handleBatch (cursor.queue.handleGraphEvents batch).workQueueEvents).1.hasNext
              = true
        · simp [silent, continued, State.handleGraphEvents_noFinish]
        · simp [silent, continued, State.handleGraphEvents_noFinish,
            HostEffect.isResponseFinished, ResponseStreamCursor.onWorkQueueFinished]

/-- At most one hook start across any finite run; a closed reader cannot start another. -/
theorem ResponseStreamCursor.run_finishCount (cursor : ResponseStreamCursor)
    (inputs : List (List GraphEvent))
    : (cursor.run inputs).2.2.countP HostEffect.isResponseFinished
        + (if cursor.finished then 1 else 0)
      = if (cursor.run inputs).2.1.finished then 1 else 0 := by
  induction inputs generalizing cursor with
  | nil =>
      change (0 : Nat) + (if cursor.finished then 1 else 0) = _
      exact Nat.zero_add _
  | cons batch rest ih =>
      have step := cursor.handleBatch_finishCount batch
      have tail := ih (cursor.handleBatch batch).2.1
      rw [ResponseStreamCursor.run_cons]
      simp only [List.countP_append]
      omega

theorem ResponseStreamCursor.run_finishCount_le_one (cursor : ResponseStreamCursor)
    (inputs : List (List GraphEvent))
    : (cursor.run inputs).2.2.countP HostEffect.isResponseFinished ≤ 1 := by
  have same := cursor.run_finishCount inputs
  split at same <;> split at same <;> omega

/-- Close supplies the hook start only when a previous step has not already supplied it. -/
theorem ResponseStreamCursor.close_finishCount (cursor : ResponseStreamCursor)
    : cursor.close.2.countP HostEffect.isResponseFinished
      = if cursor.finished then 0 else 1 := by
  cases closed : cursor.finished <;>
    simp [ResponseStreamCursor.close, closed, State.cancel_noFinish,
      HostEffect.isResponseFinished]

/-- Draining any prefix then closing starts the hook exactly once for a live reader. -/
theorem ResponseStreamCursor.run_close_finishCount (cursor : ResponseStreamCursor)
    (inputs : List (List GraphEvent))
    : ((cursor.run inputs).2.2 ++ (cursor.run inputs).2.1.close.2).countP
        HostEffect.isResponseFinished
      = if cursor.finished then 0 else 1 := by
  have same := cursor.run_finishCount inputs
  rw [List.countP_append, ResponseStreamCursor.close_finishCount]
  split at same <;> split at same <;> simp_all

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
