import GraphQL.IncrementalDelivery.Correctness

/-! Response coalescing preserves causal ID liveness. Only list-entry concatenation
is used; no timing, batch-width, or hasNext/open-ID assumption is needed.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

def combineFrom (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : IncrementalStreamUpdateResult :=
  updates.foldl
    (fun acc update =>
      {
        hasNext := update.hasNext,
        pending := acc.pending ++ update.pending,
        incremental := acc.incremental ++ update.incremental,
        completed := acc.completed ++ update.completed
      })
    initial

/-- Response aggregation concatenates notice IDs, by fold induction. -/
theorem combineFrom_ids (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : (combineFrom updates initial).pending.map IncrementalPendingNotice.id
        = initial.pending.map IncrementalPendingNotice.id
          ++ DeliveryTrace.pendingIDs updates
      ∧ (combineFrom updates initial).completed.map IncrementalCompletionNotice.id
        = initial.completed.map IncrementalCompletionNotice.id
          ++ DeliveryTrace.completedIDs updates := by
  induction updates generalizing initial with
  | nil => simp [combineFrom, DeliveryTrace.pendingIDs, DeliveryTrace.completedIDs]
  | cons update rest ih =>
      simpa [combineFrom, DeliveryTrace.pendingIDs, DeliveryTrace.completedIDs,
        List.map_append, List.append_assoc] using ih
          { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
            incremental := initial.incremental ++ update.incremental,
            completed := initial.completed ++ update.completed }

/-- Public aggregation concatenates IDs, by its empty-accumulator equation. -/
theorem combineIncrementalResults_ids (updates : List IncrementalStreamUpdateResult)
    : (combineIncrementalResults updates).pending.map IncrementalPendingNotice.id
        = DeliveryTrace.pendingIDs updates
      ∧ (combineIncrementalResults updates).completed.map IncrementalCompletionNotice.id
        = DeliveryTrace.completedIDs updates := by
  simpa only [combineFrom, combineIncrementalResults, List.map_nil, List.nil_append]
    using combineFrom_ids updates { hasNext := false }

/-- Response batching preserves completion occurrences, by batch induction. -/
theorem batched_completedIDs (batches : List (List IncrementalStreamUpdateResult))
    : DeliveryTrace.completedIDs (batches.map combineIncrementalResults)
      = DeliveryTrace.completedIDs batches.flatten := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      change (combineIncrementalResults batch).completed.map IncrementalCompletionNotice.id
          ++ DeliveryTrace.completedIDs (rest.map combineIncrementalResults) = _
      rw [(combineIncrementalResults_ids batch).2, ih]
      simp [DeliveryTrace.completedIDs, List.flatMap_append]

/-- Causal liveness splits into a prefix obligation and a live suffix, by induction. -/
theorem announcements_split {head tail : List IncrementalStreamUpdateResult}
    (h : DeliveryTrace.announcementsEventuallyComplete (head ++ tail))
    : (∀ id ∈ DeliveryTrace.pendingIDs head,
        id ∈ DeliveryTrace.completedIDs (head ++ tail))
      ∧ DeliveryTrace.announcementsEventuallyComplete tail := by
  induction head with
  | nil => exact ⟨by simp [DeliveryTrace.pendingIDs], h⟩
  | cons update rest ih =>
      obtain ⟨hp, ht⟩ := h
      obtain ⟨hr, hf⟩ := ih ht
      refine ⟨?_, hf⟩
      intro id hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hp id hi
      · exact List.mem_append_right _ (hr id hi)

/-- Coalescing responses preserves causal notice completion, by prefix splitting. -/
theorem batched_announcements (batches : List (List IncrementalStreamUpdateResult))
    (h : DeliveryTrace.announcementsEventuallyComplete batches.flatten)
    : DeliveryTrace.announcementsEventuallyComplete
        (batches.map combineIncrementalResults) := by
  induction batches with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨hp, ht⟩ := announcements_split h
      refine ⟨?_, ih ht⟩
      intro id hi
      rw [(combineIncrementalResults_ids batch).1] at hi
      have hm := hp id hi
      change id ∈ DeliveryTrace.completedIDs ((batch :: rest).map combineIncrementalResults)
      rw [batched_completedIDs]
      exact hm

/-- Any response grouping preserves liveness, by flattened occurrence equality. -/
theorem batching_idsEventuallyComplete (initial : InitialIncrementalStreamResult)
    (updates : List IncrementalStreamUpdateResult)
    (batches : List (List IncrementalStreamUpdateResult))
    (flatten : batches.flatten = updates)
    (live : (QueryResult.incremental initial updates).idsEventuallyComplete)
    : (QueryResult.incremental initial
        (batches.map combineIncrementalResults)).idsEventuallyComplete := by
  constructor
  · intro id hi
    rw [batched_completedIDs, flatten]
    exact live.1 id hi
  · exact batched_announcements batches (flatten.symm ▸ live.2)

end GraphQL.IncrementalDelivery.Correctness
