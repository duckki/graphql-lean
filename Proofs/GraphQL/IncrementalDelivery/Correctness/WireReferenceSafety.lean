import Proofs.GraphQL.IncrementalDelivery.Correctness.IDUsageProperties
import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseBatchReferences

/-! Unique histories plus causal, non-closed references imply the public ID-usage
predicate. This separates reference legality from independent identity proofs.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Fresh IDs and legal references satisfy the Boolean checker, by update induction. -/
theorem wireReferences_idUsageValid {seen closed active : List String}
    {updates : List IncrementalStreamUpdateResult}
    (references : WireReferences.Valid seen closed updates)
    (unique : (seen ++ DeliveryTrace.pendingIDs updates).Nodup)
    (completions : (DeliveryTrace.completedIDs updates).Nodup)
    (supported : ∀ id ∈ closed, id ∈ seen)
    (available : ∀ id, id ∈ active ↔ id ∈ seen ∧ id ∉ closed)
    : DeliveryTrace.idUsageValid seen active updates := by
  induction updates generalizing seen closed active with
  | nil => trivial
  | cons update rest ih =>
      apply (idUsageValid_cons_iff _ _ _ _).mpr
      have futureUnique :
          ((seen ++ WireReferences.pending update) ++ DeliveryTrace.pendingIDs rest).Nodup := by
        simpa only [DeliveryTrace.pendingIDs, List.flatMap_cons, List.append_assoc,
          WireReferences.pending]
          using unique
      have headUnique := List.nodup_append.mp (List.nodup_append.mp futureUnique).1
      have completionUnique := List.nodup_append.mp completions
      have fresh : ∀ id ∈ WireReferences.pending update, id ∉ seen := by
        intro id member old
        exact headUnique.2.2 id old id member rfl
      have availableNow (id : String) :
          id ∈ active ++ WireReferences.pending update
          ↔ id ∈ seen ++ WireReferences.pending update ∧ id ∉ closed := by
        constructor
        · intro member
          rcases List.mem_append.mp member with old | new
          · obtain ⟨known, notClosed⟩ := (available id).mp old
            exact ⟨List.mem_append_left _ known, notClosed⟩
          · exact ⟨List.mem_append_right _ new, fun hc => fresh id new (supported id hc)⟩
        · rintro ⟨member, notClosed⟩
          rcases List.mem_append.mp member with old | new
          · exact List.mem_append_left _ ((available id).mpr ⟨old, notClosed⟩)
          · exact List.mem_append_right _ new
      have usedAvailable (id : String) (used : id ∈ WireReferences.used update) :
          id ∈ active ++ WireReferences.pending update :=
        (availableNow id).mpr (references.1 id used)
      refine ⟨fresh, headUnique.2.1, completionUnique.1, ?_, ?_, ?_⟩
      · intro id member
        exact usedAvailable id (List.mem_append_left _ member)
      · intro patch member
        exact usedAvailable patch.id
          (List.mem_append_right _ (List.mem_map.mpr ⟨patch, member, rfl⟩))
      · apply ih references.2 futureUnique completionUnique.2.1
        · intro id member
          rcases List.mem_append.mp member with old | new
          · exact List.mem_append_left _ (supported id old)
          · exact (references.1 id (List.mem_append_left _ new)).1
        · intro id
          simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not]
          change (id ∈ active ++ WireReferences.pending update
              ∧ id ∉ WireReferences.completed update)
            ↔ id ∈ seen ++ WireReferences.pending update
              ∧ id ∉ closed ++ WireReferences.completed update
          rw [availableNow]
          simp only [List.mem_append, not_or, and_assoc]

/-- Initial uniqueness and ordered reference safety imply the public ID checker. -/
theorem incremental_idUsageValid_of_references (initial : InitialIncrementalStreamResult)
    (updates : List IncrementalStreamUpdateResult)
    (references
      : WireReferences.Valid (initial.pending.map IncrementalPendingNotice.id) [] updates)
    (unique : (QueryResult.incremental initial updates).idsUnique)
    (completions : (DeliveryTrace.completedIDs updates).Nodup)
    : (QueryResult.incremental initial updates).idUsageValid := by
  exact ⟨
    (List.nodup_append.mp unique).1,
    wireReferences_idUsageValid references unique completions
      (by simp)
      (by intro id; simp)
  ⟩

end GraphQL.IncrementalDelivery.Correctness
