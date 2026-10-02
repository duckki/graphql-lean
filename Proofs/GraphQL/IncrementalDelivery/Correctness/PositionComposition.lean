import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamPositions

/-! Supplied wire histories decode compositionally, without choosing scheduler outputs. -/

namespace GraphQL.IncrementalDelivery.Execution.DeliveryTrace

/-- Concatenated patches decode sequentially with the residual cursor; witness: list
induction and associativity of Option binds.
-/
theorem decodePatches_append (containers : Bool) (notices : List IncrementalPendingNotice)
    (cursors : ResponsePositions.Cursors) (left right : List IncrementalResult)
    : decodePatches containers notices cursors (left ++ right)
      = (do
          let (head, middle) ← decodePatches containers notices cursors left
          let (tail, final) ← decodePatches containers notices middle right
          return (head ++ tail, final)) := by
  induction left generalizing cursors with
  | nil =>
      cases decoded : decodePatches containers notices cursors right <;>
        simp [decodePatches, decoded]
  | cons patch rest ih =>
      simp [decodePatches, ih, Option.bind_assoc]

/-- Concatenated updates decode sequentially with residual cursors and all earlier
notices; witness: update induction and associative notice/slice concatenation.
-/
theorem decodeUpdates_append (containers : Bool) (notices : List IncrementalPendingNotice)
    (cursors : ResponsePositions.Cursors)
    (left right : List IncrementalStreamUpdateResult)
    : decodeUpdates containers notices cursors (left ++ right)
      = (do
          let (head, middle) ← decodeUpdates containers notices cursors left
          let (tail, final) ←
            decodeUpdates containers (notices ++ left.flatMap (·.pending)) middle right
          return (head ++ tail, final)) := by
  induction left generalizing notices cursors with
  | nil =>
      cases decoded : decodeUpdates containers notices cursors right <;>
        simp [decodeUpdates, decoded]
  | cons update rest ih =>
      simp [decodeUpdates, ih, Option.bind_assoc, List.append_assoc]

/-- Successful concatenated patch decoding exposes the exact prefix and suffix states;
witness: invert the append law's two successful Option binds.
-/
theorem decodePatches_append_iff {containers notices cursors left right slices final}
    : decodePatches containers notices cursors (left ++ right) = some (slices, final)
      ↔ ∃ head middle tail,
          decodePatches containers notices cursors left = some (head, middle)
          ∧ decodePatches containers notices middle right = some (tail, final)
          ∧ slices = head ++ tail := by
  rw [decodePatches_append]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨head, middle⟩, first, ⟨tail, last⟩, later, equal, rfl⟩
    exact ⟨head, middle, tail, first, later, equal.symm⟩
  · rintro ⟨head, middle, tail, first, later, rfl⟩
    exact ⟨(head, middle), first, (tail, final), later, rfl, rfl⟩

/-- Successful concatenated update decoding exposes the causal notice frontier and
residual cursors; witness: invert the append law's two successful Option binds.
-/
theorem decodeUpdates_append_iff {containers notices cursors left right slices final}
    : decodeUpdates containers notices cursors (left ++ right) = some (slices, final)
      ↔ ∃ head middle tail,
          decodeUpdates containers notices cursors left = some (head, middle)
          ∧ decodeUpdates containers (notices ++ left.flatMap (·.pending)) middle right
            = some (tail, final)
          ∧ slices = head ++ tail := by
  rw [decodeUpdates_append]
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨head, middle⟩, first, ⟨tail, last⟩, later, equal, rfl⟩
    exact ⟨head, middle, tail, first, later, equal.symm⟩
  · rintro ⟨head, middle, tail, first, later, rfl⟩
    exact ⟨(head, middle), first, (tail, final), later, rfl, rfl⟩

end GraphQL.IncrementalDelivery.Execution.DeliveryTrace
