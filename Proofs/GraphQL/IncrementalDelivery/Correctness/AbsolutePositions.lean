import Proofs.GraphQL.IncrementalDelivery.Correctness.CursorEquivalence

/-! ID-free position decoding separates absolute data provenance from notice allocation.
Streams use one atom per item; batching can regroup atoms without changing their order.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- An absolute object contribution or one streamed item; control metadata is omitted.
-/
inductive PositionAtom where
  | object (path : ResponsePath) (data : List (Name × ResponseValue))
  | item (path : ResponsePath) (data : ResponseValue)

/-- Decode one absolute atom, using the current cursor only for a streamed item. -/
def PositionAtom.decode (containers : Bool) (cursors : ResponsePositions.Cursors)
    : PositionAtom → Option (List ResponsePath × ResponsePositions.Cursors)
  | .object path data =>
      some
        (
          ResponsePositions.fields containers path data,
          ResponsePositions.fieldCursors path data ++ cursors
        )
  | .item path data => do
      let index ← ResponsePositions.cursorAt cursors path
      return (
        ResponsePositions.value containers (path ++ [.index index]) data,
        (path, index + 1) :: ResponsePositions.listCursors (path ++ [.index index]) data
        ++ cursors
      )

/-- Decode supplied atoms in order, flattening positions but retaining cursor state. -/
def decodeAtoms (containers : Bool) (cursors : ResponsePositions.Cursors)
    : List PositionAtom → Option (List ResponsePath × ResponsePositions.Cursors)
  | [] => some ([], cursors)
  | head :: rest => do
      let (first, middle) ← head.decode containers cursors
      let (tail, final) ← decodeAtoms containers middle rest
      return (first ++ tail, final)

/-- One atom depends only on cursor lookups, not obsolete cursor history. Witness:
object writes prepend identically; item writes first consult equal path lookups.
-/
theorem PositionAtom.decode_equivalent {containers before after atom positions final}
    (same : CursorEquivalent before after)
    (decoded : PositionAtom.decode containers before atom = some (positions, final))
    : ∃ next,
        PositionAtom.decode containers after atom = some (positions, next)
        ∧ CursorEquivalent final next := by
  cases atom with
  | object path data =>
      simp only [PositionAtom.decode, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      exact ⟨_, rfl, same.prepend _⟩
  | item path data =>
      cases cursor : ResponsePositions.cursorAt before path with
      | none => simp [PositionAtom.decode, cursor] at decoded
      | some index =>
          simp [PositionAtom.decode, cursor] at decoded
          obtain ⟨rfl, rfl⟩ := decoded
          refine ⟨(path, index + 1)
            :: ResponsePositions.listCursors (path ++ [.index index]) data ++ after, ?_, ?_⟩
          · simp [PositionAtom.decode, ← same path, cursor]
          · simpa only [List.cons_append] using same.prepend
              ((path, index + 1) :: ResponsePositions.listCursors (path ++ [.index index]) data)

/-- Atom replay preserves positions and equivalent cursor results across equivalent
initial histories. Witness: induction using the single-atom congruence theorem.
-/
theorem decodeAtoms_equivalent {containers before after atoms positions final}
    (same : CursorEquivalent before after)
    (decoded : decodeAtoms containers before atoms = some (positions, final))
    : ∃ next,
        decodeAtoms containers after atoms = some (positions, next)
        ∧ CursorEquivalent final next := by
  induction atoms generalizing before after positions final with
  | nil =>
      simp only [decodeAtoms, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      exact ⟨after, rfl, same⟩
  | cons head rest ih =>
      cases first : head.decode containers before with
      | none => simp [decodeAtoms, first] at decoded
      | some pair =>
          rcases pair with ⟨paths, middle⟩
          cases tail : decodeAtoms containers middle rest with
          | none => simp [decodeAtoms, first, tail] at decoded
          | some pair =>
              rcases pair with ⟨later, last⟩
              simp [decodeAtoms, first, tail] at decoded
              obtain ⟨rfl, rfl⟩ := decoded
              obtain ⟨next, nextDecoded, nextSame⟩ := head.decode_equivalent same first
              obtain ⟨final, restDecoded, finalSame⟩ := ih nextSame tail
              exact ⟨final, by simp [decodeAtoms, nextDecoded, restDecoded], finalSame⟩

/-- Concatenating atom lists composes their finite decoders. Witness: list induction and
associativity of the introduced-position concatenation.
-/
theorem decodeAtoms_append (containers : Bool) (cursors : ResponsePositions.Cursors)
    (left right : List PositionAtom)
    : decodeAtoms containers cursors (left ++ right)
      = do
        let (first, middle) ← decodeAtoms containers cursors left
        let (second, final) ← decodeAtoms containers middle right
        return (first ++ second, final) := by
  induction left generalizing cursors with
  | nil =>
      simp only [List.nil_append, decodeAtoms]
      cases result : decodeAtoms containers cursors right <;> simp [result]
  | cons head rest ih =>
      simp only [List.cons_append, decodeAtoms, ih]
      cases head.decode containers cursors <;> simp
      next pair =>
        cases decodeAtoms containers pair.2 rest <;> simp
        next result =>
          cases decodeAtoms containers result.2 right <;> simp

/-- Expanding a list patch into single-item atoms preserves its positions and all cursor
lookups. Witness: item-index induction, commuting disjoint nested item cursors and
discarding shadowed older enclosing-list writes.
-/
theorem decodeAtoms_items (containers : Bool) (path : ResponsePath)
    (values : List ResponseValue) (cursors : ResponsePositions.Cursors) (index : Nat)
    (cursor : ResponsePositions.cursorAt cursors path = some index)
    : ∃ final,
        decodeAtoms containers cursors (values.map (PositionAtom.item path))
          = some (ResponsePositions.items containers path index values, final)
        ∧ CursorEquivalent final
            ((path, index + values.length)
                :: ResponsePositions.itemCursors path index values
              ++ cursors) := by
  induction values generalizing cursors index with
  | nil =>
      exact ⟨cursors, rfl, (cursorEquivalent_reassert cursor).symm⟩
  | cons head rest ih =>
      let middle := (path, index + 1)
        :: ResponsePositions.listCursors (path ++ [.index index]) head ++ cursors
      have middleCursor : ResponsePositions.cursorAt middle path = some (index + 1) := by
        simp [middle, cursorAt_cons]
      obtain ⟨final, tail, equivalent⟩ := ih middle (index + 1) middleCursor
      refine ⟨final, ?_, ?_⟩
      · simp only [middle, List.cons_append] at tail
        simp [decodeAtoms, PositionAtom.decode, cursor, tail, ResponsePositions.items]
      · have shadow := cursorEquivalent_shadow path (index + 1 + rest.length)
          (index + 1) (ResponsePositions.itemCursors path (index + 1) rest)
          (ResponsePositions.listCursors (path ++ [.index index]) head ++ cursors)
        have commute := CursorEquivalent.prepend
          ((itemCursors_commute path index head rest).symm.append cursors)
          [(path, index + 1 + rest.length)]
        have composed :=
          shadow.trans
            (by
              simpa only [List.singleton_append, List.cons_append, List.nil_append,
                List.append_assoc]
                using commute)
        exact equivalent.trans
          (by
            simpa only [middle, List.cons_append, List.singleton_append, List.nil_append,
              List.append_assoc, ResponsePositions.itemCursors, List.length_cons,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              using composed)

end GraphQL.IncrementalDelivery.Correctness
