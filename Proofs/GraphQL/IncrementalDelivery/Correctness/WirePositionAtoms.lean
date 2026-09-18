import Proofs.GraphQL.IncrementalDelivery.Correctness.AbsolutePositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.PatchPositions

/-! Stable IDs connect absolute atoms to the public, causal wire-position decoder. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- One wire entry encodes absolute atoms under an injective ID allocation and source
path assignment. Stream entries retain the independently derived nonempty-value fact.
-/
inductive EntryPositionAtoms (paths : Nat → ResponsePath) (ids : IDState)
    : IncrementalResult → List PositionAtom → Prop where
  | object {key id data errors subPath} (known : Known ids key id)
    : EntryPositionAtoms paths ids (.object id data errors subPath)
        [.object (paths key ++ subPath) data]
  | list {key id data errors} (known : Known ids key id) (nonempty : data ≠ [])
    : EntryPositionAtoms paths ids (.list id data errors)
        (data.map (PositionAtom.item (paths key)))

/-- Wire entries encode concatenated absolute atoms in the same order. -/
inductive EntriesPositionAtoms (paths : Nat → ResponsePath) (ids : IDState)
    : List IncrementalResult → List PositionAtom → Prop where
  | nil : EntriesPositionAtoms paths ids [] []
  | cons {entry entries head tail}
    (first : EntryPositionAtoms paths ids entry head)
    (rest : EntriesPositionAtoms paths ids entries tail)
    : EntriesPositionAtoms paths ids (entry :: entries) (head ++ tail)

/-- Stable ID allocation preserves a single entry's absolute encoding. -/
theorem EntryPositionAtoms.mono {paths before after entry atoms}
    (encoded : EntryPositionAtoms paths before entry atoms)
    (preserves : Preserves before after)
    : EntryPositionAtoms paths after entry atoms := by
  cases encoded with
  | object known => exact .object (preserves _ _ known)
  | list known nonempty => exact .list (preserves _ _ known) nonempty

/-- Stable allocation preserves the complete ordered entry encoding, by list induction.
-/
theorem EntriesPositionAtoms.mono {paths before after entries atoms}
    (encoded : EntriesPositionAtoms paths before entries atoms)
    (preserves : Preserves before after)
    : EntriesPositionAtoms paths after entries atoms := by
  induction encoded with
  | nil => exact .nil
  | cons first rest ih => exact .cons (first.mono preserves) ih

/-- Concatenating encoded entry lists concatenates their atoms without reordering. -/
theorem EntriesPositionAtoms.append {paths ids left right first second}
    (hl : EntriesPositionAtoms paths ids left first)
    (hr : EntriesPositionAtoms paths ids right second)
    : EntriesPositionAtoms paths ids (left ++ right) (first ++ second) := by
  induction hl with
  | nil => exact hr
  | cons head tail ih =>
      simpa only [List.append_assoc, List.cons_append] using EntriesPositionAtoms.cons head ih

/-- Splitting entries at any response boundary splits their atom sequence at the same
boundary. Witness: induction on the initial entry list, without choosing batch widths.
-/
theorem EntriesPositionAtoms.split {paths ids left right atoms}
    (encoded : EntriesPositionAtoms paths ids (left ++ right) atoms)
    : ∃ first second,
        atoms = first ++ second
        ∧ EntriesPositionAtoms paths ids left first
        ∧ EntriesPositionAtoms paths ids right second := by
  induction left generalizing atoms with
  | nil => exact ⟨[], atoms, rfl, .nil, encoded⟩
  | cons entry rest ih =>
      cases encoded with
      | cons first tail =>
          obtain ⟨before, after, rfl, head, tail⟩ := ih tail
          exact ⟨_, after, (List.append_assoc ..).symm, .cons first head, tail⟩

/-- An encoded wire entry decodes to the same positions as its absolute atoms whenever
its ID is already announced. Witness: stable notice metadata and the list-expansion
theorem; no later notice is used by the public decoder.
-/
theorem EntryPositionAtoms.decode
    {paths ids entry atoms notices containers cursors produced final}
    (encoded : EntryPositionAtoms paths ids entry atoms) (allocated : Allocated ids)
    (metadata : NoticePaths paths ids notices)
    (announced : entry.id ∈ notices.map IncrementalPendingNotice.id)
    (decoded : decodeAtoms containers cursors atoms = some (produced, final))
    : ∃ next,
        DeliveryTrace.decodePatch containers notices cursors entry = some (produced, next)
        ∧ CursorEquivalent final next := by
  obtain ⟨notice, found⟩ := notice_exists announced
  cases encoded with
  | @object key id data errors subPath known =>
      have path := metadata.lookup (node := { key, path := paths key }) allocated known rfl found
      simp [decodeAtoms, PositionAtom.decode] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      refine ⟨_, ?_, fun _ => rfl⟩
      simpa only [path, IncrementalResult.id] using DeliveryTrace.decodePatch_object
        (containers := containers) (cursors := cursors) (data := data)
        (errors := errors) (subPath := subPath) found
  | @list key id data errors known nonempty =>
      have path := metadata.lookup (node := { key, path := paths key }) allocated known rfl found
      cases cursor : ResponsePositions.cursorAt cursors (paths key) with
      | none =>
          cases data with
          | nil => exact False.elim (nonempty rfl)
          | cons head tail => simp [decodeAtoms, PositionAtom.decode, cursor] at decoded
      | some index =>
          obtain ⟨result, same, equivalent⟩ := decodeAtoms_items containers (paths key)
            data cursors index cursor
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (same.symm.trans decoded))
          refine ⟨_, ?_, equivalent⟩
          simpa only [path, IncrementalResult.id]
            using DeliveryTrace.decodePatch_list
              (containers := containers) (cursors := cursors) (data := data)
              (errors := errors) found
              (by simpa only [path] using cursor)

/-- An encoded entry sequence has public position slices with the same flattened atoms.
Witness: entry induction and cursor-equivalent replay across coalesced list patches.
-/
theorem EntriesPositionAtoms.decode
    {paths ids entries atoms notices containers cursors produced final}
    (encoded : EntriesPositionAtoms paths ids entries atoms) (allocated : Allocated ids)
    (metadata : NoticePaths paths ids notices)
    (announced : ∀ entry ∈ entries, entry.id ∈ notices.map IncrementalPendingNotice.id)
    (decoded : decodeAtoms containers cursors atoms = some (produced, final))
    : ∃ slices next,
        DeliveryTrace.decodePatches containers notices cursors entries
          = some (slices, next)
        ∧ slices.flatten = produced
        ∧ CursorEquivalent final next := by
  induction encoded generalizing cursors produced final with
  | nil =>
      simp only [decodeAtoms, Option.some.injEq, Prod.mk.injEq] at decoded
      obtain ⟨rfl, rfl⟩ := decoded
      exact ⟨[], cursors, rfl, rfl, fun _ => rfl⟩
  | @cons entry entries head tail first rest ih =>
      rw [decodeAtoms_append] at decoded
      cases hd : decodeAtoms containers cursors head with
      | none => simp [hd] at decoded
      | some pair =>
          rcases pair with ⟨firstPositions, middle⟩
          cases td : decodeAtoms containers middle tail with
          | none => simp [hd, td] at decoded
          | some pair =>
              rcases pair with ⟨tailPositions, last⟩
              simp [hd, td] at decoded
              obtain ⟨rfl, rfl⟩ := decoded
              obtain ⟨wireMiddle, firstPatch, middleEq⟩ :=
                first.decode allocated metadata (announced entry (by simp)) hd
              obtain ⟨tailFinal, tailDecoded, tailEq⟩ := decodeAtoms_equivalent middleEq td
              obtain ⟨slices, wireFinal, tailPatches, flattened, finalEq⟩ :=
                ih (fun entry member => announced entry (by simp [member])) tailDecoded
              refine ⟨firstPositions :: slices, wireFinal,
                ?_, ?_, tailEq.trans finalEq⟩
              · simp [DeliveryTrace.decodePatches, firstPatch, tailPatches]
              · simp only [List.flatten_cons, flattened]

end GraphQL.IncrementalDelivery.Correctness
