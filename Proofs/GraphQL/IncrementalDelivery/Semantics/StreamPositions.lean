import GraphQL.IncrementalDelivery.Correctness

/-! Equations and inversion rules for deterministic wire-position decoding.
The scheduler remains relational; these lemmas replay only supplied response updates.
-/

namespace GraphQL.IncrementalDelivery.Execution

open ResponsePositions

/-- An object payload decodes at its announced owner's path plus subPath, by lookup. -/
theorem DeliveryTrace.decodePatch_object
    {containers notices cursors id data errors subPath notice}
    (owner : notices.find? (fun pending => pending.id == id) = some notice)
    : decodePatch containers notices cursors (.object id data errors subPath)
      = some
          (
            fields containers (notice.path ++ subPath) data,
            fieldCursors (notice.path ++ subPath) data ++ cursors
          ) := by
  simp [decodePatch, IncrementalResult.id, owner]

/-- A streamed payload advances its observed list cursor by its item count, by lookup. -/
theorem DeliveryTrace.decodePatch_list
    {containers notices cursors id data errors notice index}
    (owner : notices.find? (fun pending => pending.id == id) = some notice)
    (cursor : cursorAt cursors notice.path = some index)
    : decodePatch containers notices cursors (.list id data errors)
      = some
          (
            items containers notice.path index data,
            (notice.path, index + data.length) :: itemCursors notice.path index data
            ++ cursors
          ) := by
  simp [decodePatch, IncrementalResult.id, owner, cursor]

/-- Successful patch-list decoding splits at its first patch, by the two Option binds. -/
theorem DeliveryTrace.decodePatches_cons_iff
    {containers notices cursors patch rest slices final}
    : decodePatches containers notices cursors (patch :: rest) = some (slices, final)
      ↔ ∃ head middle tail,
          decodePatch containers notices cursors patch = some (head, middle)
          ∧ decodePatches containers notices middle rest = some (tail, final)
          ∧ slices = head :: tail := by
  constructor
  · intro decoded
    simp only [decodePatches, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨⟨head, middle⟩, first, ⟨tail, last⟩, later, equal, rfl⟩ := decoded
    exact ⟨head, middle, tail, first, later, equal.symm⟩
  · rintro ⟨head, middle, tail, first, later, rfl⟩
    simp [decodePatches, first, later]

/-- Successful update decoding splits at the first response using its current notices,
by the two Option binds; the residual cursor is shared with the remaining responses.
-/
theorem DeliveryTrace.decodeUpdates_cons_iff
    {containers notices cursors update rest slices final}
    : decodeUpdates containers notices cursors (update :: rest) = some (slices, final)
      ↔ ∃ head middle tail,
          decodePatches containers (notices ++ update.pending) cursors update.incremental
            = some (head, middle)
          ∧ decodeUpdates containers (notices ++ update.pending) middle rest
            = some (tail, final)
          ∧ slices = head ++ tail := by
  constructor
  · intro decoded
    simp only [decodeUpdates, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at decoded
    obtain ⟨⟨head, middle⟩, first, ⟨tail, last⟩, later, equal, rfl⟩ := decoded
    exact ⟨head, middle, tail, first, later, equal.symm⟩
  · rintro ⟨head, middle, tail, first, later, rfl⟩
    simp [decodeUpdates, first, later]

/-- Incremental slices consist of initial positions and successfully decoded updates,
by the query decoder's single Option bind.
-/
theorem QueryResult.deliversSlices_incremental_iff {containers initial subsequent slices}
    : (QueryResult.incremental initial subsequent).DeliversSlices containers slices
      ↔ ∃ tail final,
          DeliveryTrace.decodeUpdates containers initial.pending
              (listCursors [] initial.data) subsequent
            = some (tail, final)
          ∧ slices = value containers [] initial.data :: tail := by
  constructor
  · intro decoded
    simp only [DeliversSlices, decodeSlices, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at decoded
    obtain ⟨⟨tail, final⟩, later, equal⟩ := decoded
    exact ⟨tail, final, later, equal.symm⟩
  · rintro ⟨tail, final, later, rfl⟩
    simp [DeliversSlices, decodeSlices, later]

end GraphQL.IncrementalDelivery.Execution

namespace GraphQL.IncrementalDelivery.Semantics.StreamPositions

open GraphQL.IncrementalDelivery.Execution

/-- A fixed observed response has at most one slice list, by Option output equality. -/
theorem deliversSlices_unique {containers : Bool} {result : QueryResult}
    {left right : List (List ResponsePath)}
    (hl : result.DeliversSlices containers left)
    (hr : result.DeliversSlices containers right)
    : left = right :=
  Option.some.inj (hl.symm.trans hr)

end GraphQL.IncrementalDelivery.Semantics.StreamPositions
