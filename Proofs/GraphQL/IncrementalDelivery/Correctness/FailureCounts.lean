import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureReporting

/-! Failure-completion counts survive mapping and both response batching stages. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- Completion notices' error subtotal in one response update. -/
def completionErrors (update : IncrementalStreamUpdateResult) : Nat :=
  (update.completed.map IncrementalCompletionNotice.errors).sum

/-- One event adds exactly its failure-completion count; witness: mapper case analysis. -/
theorem eventLoop_completionErrors (event : WorkEvent)
    (initial update : IncrementalStreamUpdateResult) (ids next : IDState)
    (mapped : (eventLoop event initial).run ids = (.yield update, next))
    : completionErrors update
      = completionErrors initial + WorkScheduler.failureErrors event := by
  cases event <;>
    simp only [eventLoop, getCompletedEntry, StateT.run, StateT.bind,
      StateT.pure, bind, pure] at mapped
  all_goals
    repeat first | split at mapped | cases mapped
    simp [completionErrors, WorkScheduler.failureErrors]

/-- Iteration adds all supplied event failure counts, by event-loop induction. -/
theorem loop_completionErrors (events : List WorkEvent)
    (initial : IncrementalStreamUpdateResult) (ids : IDState)
    : completionErrors ((forIn events initial eventLoop).run ids).1
      = completionErrors initial + (events.map WorkScheduler.failureErrors).sum := by
  induction events generalizing initial ids with
  | nil =>
      simp; rfl
  | cons event rest ih =>
      obtain ⟨middle, state, mapped, _⟩ := eventLoop_spec event initial ids
      have count := eventLoop_completionErrors event initial middle ids state mapped
      have tail := ih middle state
      simp only [StateT.run] at mapped tail
      simp [List.forIn_cons, StateT.run, StateT.bind, bind, mapped, tail, count,
        Nat.add_assoc]

/-- Public work-event batch mapping preserves the failure-completion subtotal. -/
theorem mapWorkEventBatch_completionErrors (events : List WorkEvent) (ids : IDState)
    : completionErrors ((mapWorkEventBatch events).run ids).1
      = (events.map WorkScheduler.failureErrors).sum := by
  rw [mapWorkEventBatch_loop, loop_completionErrors]
  simp [completionErrors]

/-- Finite replay preserves failure errors across all supplied work batches. -/
theorem mappedTrace_completionErrors (batches : List (List WorkEvent)) (ids : IDState)
    : ((mappedTrace batches ids).map completionErrors).sum
      = (batches.flatten.map WorkScheduler.failureErrors).sum := by
  induction batches generalizing ids with
  | nil => rfl
  | cons batch rest ih =>
      have count := mapWorkEventBatch_completionErrors batch ids
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          simp only [mapped] at count
          simp only [mappedTrace, mapped, List.map_cons, List.sum_cons,
            List.flatten_cons, List.map_append, List.sum_append, ih, count]

/-- Response aggregation adds completion-error subtotals, by fold induction. -/
theorem combineFrom_completionErrors (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : completionErrors (combineFrom updates initial)
      = completionErrors initial + (updates.map completionErrors).sum := by
  induction updates generalizing initial with
  | nil => simp [combineFrom]
  | cons update rest ih =>
      simpa [combineFrom, completionErrors, Nat.add_assoc] using ih
        { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
          incremental := initial.incremental ++ update.incremental,
          completed := initial.completed ++ update.completed }

/-- Coalescing a response group retains its entire completion-error subtotal. -/
theorem combineIncrementalResults_completionErrors
    (updates : List IncrementalStreamUpdateResult)
    : completionErrors (combineIncrementalResults updates)
      = (updates.map completionErrors).sum := by
  simpa [combineFrom, combineIncrementalResults, completionErrors]
    using combineFrom_completionErrors updates { hasNext := false }

/-- All response grouping preserves failure errors, by group induction. -/
theorem batched_completionErrors (groups : List (List IncrementalStreamUpdateResult))
    : ((groups.map combineIncrementalResults).map completionErrors).sum
      = (groups.flatten.map completionErrors).sum := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append,
        List.sum_append, combineIncrementalResults_completionErrors, ih]

/-- Completion errors are part of the total observed errors; witness: termwise bounds. -/
theorem completionErrors_le_total (initial : InitialIncrementalStreamResult)
    (updates : List IncrementalStreamUpdateResult)
    : (updates.map completionErrors).sum
      ≤ QueryResult.totalErrors (.incremental initial updates) := by
  have bound : (updates.map completionErrors).sum ≤
      (updates.map (fun update =>
        (update.incremental.map IncrementalResult.errors).sum
          + completionErrors update)).sum := by
    induction updates with
    | nil => exact Nat.le_refl _
    | cons update rest ih =>
        simp only [List.map_cons, List.sum_cons]; omega
  exact Nat.le_trans bound (Nat.le_add_left _ _)

/-- Actual grouped replay cannot hide work failure errors; witness: preserved completion
counts followed by the total-errors bound. No work admissibility is needed for this fold.
-/
theorem replayResponse_failureErrors_le (response : Response)
    (initialGroups initialStreams : List DeliveryNode)
    (groups : List (List (List WorkEvent)))
    : (groups.flatten.flatten.map WorkScheduler.failureErrors).sum
      ≤ (replayResponse response initialGroups initialStreams groups).totalErrors := by
  cases allocated
        : (getPendingEntry (m := StateM IDState) initialGroups initialStreams
            ensureID).run
            {} with
  | mk pending ids =>
      have replayed := replayResponse_groups response initialGroups initialStreams groups
      rw [allocated] at replayed
      obtain ⟨updates, flat, replay⟩ := replayed
      rw [replay]
      have counts := batched_completionErrors updates
      rw [flat, mappedTrace_completionErrors] at counts
      rw [← counts]
      exact completionErrors_le_total _ _

end GraphQL.IncrementalDelivery.Correctness
