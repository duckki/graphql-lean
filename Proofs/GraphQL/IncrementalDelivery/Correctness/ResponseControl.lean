import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperControl

/-! Nonempty response aggregation preserves the final continuation flag. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- Finite mapper replay emits one response per supplied work batch, by list induction. -/
theorem mappedTrace_length (batches : List (List WorkEvent)) (ids : IDState)
    : (mappedTrace batches ids).length = batches.length := by
  induction batches generalizing ids with
  | nil => rfl
  | cons batch rest ih =>
      cases mapped : (mapWorkEventBatch batch).run ids
      simp [mappedTrace, mapped, ih]

/-- Nonempty supplied input groups yield nonempty groups of mapped responses, by
induction and preservation of traversal length.
-/
theorem replayGroups_nonempty {groups : List (List (List WorkEvent))}
    (nonempty : ∀ group ∈ groups, group ≠ []) (ids : IDState)
    : ∀ updates ∈ (replayGroups groups ids).1, updates ≠ [] := by
  induction groups generalizing ids with
  | nil => simp [replayGroups]
  | cons group rest ih =>
      cases first : (group.mapM mapWorkEventBatch).run ids with
      | mk updates next =>
          have length := congrArg (fun result => result.1.length) (mapM_workEvents group ids)
          rw [first] at length
          simp only [mappedTrace_length] at length
          intro values member
          simp only [replayGroups, first, List.mem_cons] at member
          rcases member with rfl | later
          · intro empty
            have groupEmpty : group = [] := List.length_eq_zero_iff.mp
              (by simpa [empty] using length.symm)
            exact nonempty group (by simp) groupEmpty
          · exact ih (fun g member => nonempty g (List.mem_cons_of_mem _ member)) next
              values later

/-- A nonempty folded prefix takes the flag dictated by its remaining suffix; witness:
induction on that prefix and inversion of the public continuation checker.
-/
theorem combineFrom_control {updates tail : List IncrementalStreamUpdateResult}
    (nonempty : updates ≠ [])
    (valid : DeliveryTrace.hasNextValid (updates ++ tail) = true)
    (initial : IncrementalStreamUpdateResult)
    : (combineFrom updates initial).hasNext = !tail.isEmpty
      ∧ DeliveryTrace.hasNextValid tail = true := by
  induction updates generalizing initial with
  | nil => exact False.elim (nonempty rfl)
  | cons update rest ih =>
      have parts : (update.hasNext == !(rest ++ tail).isEmpty) = true
          ∧ DeliveryTrace.hasNextValid (rest ++ tail) = true := by
        simpa only [List.cons_append, DeliveryTrace.hasNextValid, Bool.and_eq_true]
          using valid
      have first : update.hasNext = !(rest ++ tail).isEmpty := beq_iff_eq.mp parts.1
      by_cases empty : rest = []
      · subst rest
        exact ⟨by simpa [combineFrom] using first, parts.2⟩
      · have later := ih empty parts.2
          { hasNext := update.hasNext, pending := initial.pending ++ update.pending,
            incremental := initial.incremental ++ update.incremental,
            completed := initial.completed ++ update.completed }
        simpa [combineFrom] using later

/-- A list of nonempty groups is empty exactly when its flattening is empty. -/
theorem nonemptyGroups_isEmpty {groups : List (List α)}
    (nonempty : ∀ group ∈ groups, group ≠ [])
    : groups.flatten.isEmpty = groups.isEmpty := by
  cases groups with
  | nil => rfl
  | cons group rest =>
      have ne := nonempty group (by simp)
      cases group with
      | nil => exact False.elim (ne rfl)
      | cons value tail => rfl

/-- Nonempty response coalescing preserves all continuation flags, by batch induction
and the last flag of each folded prefix.
-/
theorem batched_hasNextValid {groups : List (List IncrementalStreamUpdateResult)}
    (nonempty : ∀ group ∈ groups, group ≠ [])
    (valid : DeliveryTrace.hasNextValid groups.flatten = true)
    : DeliveryTrace.hasNextValid (groups.map combineIncrementalResults) = true := by
  induction groups with
  | nil => rfl
  | cons group rest ih =>
      have restNonempty := fun g member => nonempty g (List.mem_cons_of_mem _ member)
      obtain ⟨flag, tail⟩ := combineFrom_control (nonempty group (by simp)) valid
        { hasNext := false }
      have same := nonemptyGroups_isEmpty restNonempty
      have flag : (combineIncrementalResults group).hasNext = !rest.isEmpty := by
        simpa only [combineFrom, combineIncrementalResults, same] using flag
      simp [DeliveryTrace.hasNextValid, flag, ih restNonempty tail]

end GraphQL.IncrementalDelivery.Correctness
