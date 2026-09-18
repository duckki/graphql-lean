import Proofs.GraphQL.IncrementalDelivery.Correctness.LifecycleProperties

/-! Response reconstruction preserves fresh object fields and accounts for every reported error. -/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Fresh object fields are appended unchanged; witness: induction preserves key
disjointness.
-/
theorem putFields_eq_append_of_nodup (existing incoming : List (Name × ResponseValue))
    (hnodup : ((existing ++ incoming).map Prod.fst).Nodup)
    : ResponseMerging.putFields existing incoming = existing ++ incoming := by
  induction incoming generalizing existing with
  | nil => simp [ResponseMerging.putFields]
  | cons field rest ih =>
      have hmap : (existing.map Prod.fst ++ (field :: rest).map Prod.fst).Nodup := by
        simpa only [List.map_append] using hnodup
      have hparts := List.nodup_append.mp hmap
      have hfresh : existing.any (fun other => other.1 == field.1) = false := by
        apply List.any_eq_false.mpr
        intro other hm
        intro he
        exact hparts.2.2 other.1 (List.mem_map.mpr ⟨other, hm, rfl⟩) field.1 (by simp)
          (beq_iff_eq.mp he)
      simp only [ResponseMerging.putFields, List.foldl_cons, hfresh, Bool.false_eq_true,
        ↓reduceIte]
      have hi := ih (existing ++ [field]) (by simpa [List.append_assoc] using hnodup)
      simpa [ResponseMerging.putFields, List.append_assoc] using hi

/-- Building a fresh object preserves its field list, by the append lemma with an empty
prefix.
-/
theorem putFields_nil_of_nodup (fields : List (Name × ResponseValue))
    (hnodup : (fields.map Prod.fst).Nodup)
    : ResponseMerging.putFields [] fields = fields :=
  putFields_eq_append_of_nodup [] fields hnodup

/-- Successful reconstruction requires lifecycle validity; witness: the merger's initial
guard.
-/
theorem deliveryComplete_of_mergeQueryResult (result : QueryResult) (response : Response)
    (h : mergeQueryResult result = some response)
    : result.deliveryComplete = true := by
  unfold mergeQueryResult at h
  split at h
  · cases h
  · simpa using ‹¬(!result.deliveryComplete) = true›

/-- A reconstructed response uses the trace's total errors, by its final envelope
constructor.
-/
theorem mergeQueryResult_errors (result : QueryResult) (response : Response)
    (h : mergeQueryResult result = some response)
    : response.errors = result.totalErrors := by
  cases result with
  | single initial =>
      simp [mergeQueryResult, QueryResult.deliveryComplete] at h
      cases h
      rfl
  | incremental initial updates =>
      unfold mergeQueryResult at h
      split at h
      · cases h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨state, _, heq⟩ := h
        cases heq
        rfl

/-- Error-free completed delivery reconstructs with zero errors, by total-error
preservation.
-/
theorem mergeQueryResult_errors_zero (result : QueryResult) (response : Response)
    (hcomplete : result.executionComplete)
    (hmerge : mergeQueryResult result = some response)
    : response.errors = 0 :=
  (mergeQueryResult_errors result response hmerge).trans hcomplete.2

/-- Every successfully reconstructed trace completes its IDs exactly once, via lifecycle
validity.
-/
theorem idsCompleteExactlyOnce_of_mergeQueryResult (result : QueryResult)
    (response : Response) (h : mergeQueryResult result = some response)
    : result.idsCompleteExactlyOnce :=
  idsCompleteExactlyOnce_of_deliveryComplete result
    (deliveryComplete_of_mergeQueryResult result response h)

end GraphQL.IncrementalDelivery.Correctness
