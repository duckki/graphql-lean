import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperOpenReferences
import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseBatchLiveness

/-! Response coalescing concatenates patch entries and preserves causal ID references.
IDs completed within the same batch remain legal there, never in a later batch.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Response folding concatenates patch IDs, by fold induction. -/
theorem combineFrom_patchIDs (updates : List IncrementalStreamUpdateResult)
    (initial : IncrementalStreamUpdateResult)
    : (combineFrom updates initial).incremental.map IncrementalResult.id
      = initial.incremental.map IncrementalResult.id
        ++ updates.flatMap
            (fun update => update.incremental.map IncrementalResult.id) := by
  induction updates generalizing initial with
  | nil => simp [combineFrom]
  | cons update rest ih =>
      simpa [combineFrom, List.map_append, List.append_assoc] using ih
        { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
          incremental := initial.incremental ++ update.incremental,
          completed := initial.completed ++ update.completed }

/-- Public aggregation concatenates patch IDs, by the empty fold equation. -/
theorem combineIncrementalResults_patchIDs (updates : List IncrementalStreamUpdateResult)
    : (combineIncrementalResults updates).incremental.map IncrementalResult.id
      = updates.flatMap (fun update => update.incremental.map IncrementalResult.id) := by
  simpa only [combineFrom, combineIncrementalResults, List.map_nil, List.nil_append]
    using combineFrom_patchIDs updates { hasNext := false }

/-- Aggregated reference membership equals membership in the source responses. -/
theorem combineIncrementalResults_used (updates : List IncrementalStreamUpdateResult)
    (id : String)
    : id ∈ WireReferences.used (combineIncrementalResults updates)
      ↔ id ∈ updates.flatMap WireReferences.used := by
  simp only [WireReferences.used, WireReferences.completed,
    (combineIncrementalResults_ids updates).2, combineIncrementalResults_patchIDs,
    DeliveryTrace.completedIDs, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (⟨update, member, completion⟩ | ⟨update, member, patch⟩)
    · exact ⟨update, member, .inl completion⟩
    · exact ⟨update, member, .inr patch⟩
  · rintro ⟨update, member, completion | patch⟩
    · exact .inl ⟨update, member, completion⟩
    · exact .inr ⟨update, member, patch⟩

/-- Response grouping preserves open references, by history splitting and mapping. -/
theorem batched_references {seen closed : List String}
    {batches : List (List IncrementalStreamUpdateResult)}
    (h : WireReferences.Valid seen closed batches.flatten)
    : WireReferences.Valid seen closed (batches.map combineIncrementalResults) := by
  exact ReferenceHistory.map combineIncrementalResults
    (fun updates => (combineIncrementalResults_ids updates).1)
    (fun updates => (combineIncrementalResults_ids updates).2)
    combineIncrementalResults_used (ReferenceHistory.batches h)

end GraphQL.IncrementalDelivery.Correctness
