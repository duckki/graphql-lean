import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedCursorMerging

/-! Lookup agreement permits historical wire cursor tables while identifying each
active cursor with the actual list length in the reconstructed response.
-/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)

/-- Permuting a unique cursor table preserves lookup, by permutation induction. -/
theorem cursorAt_perm {left right : Cursors} (hp : left.Perm right)
    (hn : (left.map Prod.fst).Nodup) (path : ResponsePath)
    : cursorAt left path = cursorAt right path := by
  induction hp with
  | nil => rfl
  | cons entry hp ih =>
      have ht := ih (List.nodup_cons.mp hn).2
      simp only [cursorAt, List.find?_cons] at ht ⊢
      split <;> simp_all
  | swap left right rest =>
      have hne : left.1 ≠ right.1 := by
        intro he
        exact (List.nodup_cons.mp hn).1 (List.mem_cons.mpr (.inl he.symm))
      simp only [cursorAt, List.find?_cons]
      by_cases hl : left.1 = path <;> by_cases hr : right.1 = path
      · exact (hne (hl.trans hr.symm)).elim
      · simp only [beq_iff_eq.mpr hl, beq_eq_false_iff_ne.mpr hr]
      · simp only [beq_eq_false_iff_ne.mpr hl, beq_iff_eq.mpr hr]
      · simp only [beq_eq_false_iff_ne.mpr hl, beq_eq_false_iff_ne.mpr hr]
  | trans first second ihfirst ihsecond =>
      exact (ihfirst hn).trans (ihsecond ((first.map Prod.fst).nodup_iff.mp hn))

/-- Cursor lookup checks the head before the tail, by equality case analysis. -/
theorem cursorAt_cons (entry : ResponsePath × Nat) (tail : Cursors) (path : ResponsePath)
    : cursorAt (entry :: tail) path
      = if entry.1 = path then some entry.2 else cursorAt tail path := by
  by_cases h : entry.1 = path
  · simp only [cursorAt, List.find?_cons, h, beq_self_eq_true, ↓reduceIte, Option.map_some]
  · simp only [cursorAt, List.find?_cons, beq_eq_false_iff_ne.mpr h, h, ↓reduceIte]

/-- Cursor lookup prefers the left table, by the appended-list lookup equation. -/
theorem cursorAt_append_eq (left right : Cursors) (path : ResponsePath)
    : cursorAt (left ++ right) path = (cursorAt left path).or (cursorAt right path) := by
  simp only [cursorAt, List.find?_append]
  cases left.find? (fun entry => entry.1 == path) <;> rfl

/-- Historical cursor lookups agree with the current response's actual list lengths. -/
def CursorRepresents (cursors : Cursors) (data : ResponseValue) : Prop :=
  ∀ path, cursorAt cursors path = cursorAt (listCursors [] data) path

/-- Lookup at an existing unique list returns its actual length, by cursor splitting. -/
theorem cursorAt_list_length (base path : ResponsePath) (data : ResponseValue)
    (existing : List ResponseValue) (found : atPath path data = some (.list existing))
    (unique : ((value base data).map Prod.fst).Nodup)
    : cursorAt (listCursors base data) (base ++ path) = some existing.length := by
  obtain ⟨_, outside, _, ho, _⟩ := modifyAtPath_cursor_split base path data
    (.list existing) (.list existing) some found rfl unique
  rw [cursorAt_perm ho ((listCursors_sublist base data).nodup unique)]
  simp [listCursors, cursorAt]

/-- A representing cursor table returns an existing list's length, by lookup agreement. -/
theorem CursorRepresents.list_length {cursors : Cursors} {data : ResponseValue}
    (h : CursorRepresents cursors data) {path : ResponsePath}
    {existing : List ResponseValue} (found : atPath path data = some (.list existing))
    (unique : ((value [] data).map Prod.fst).Nodup)
    : cursorAt cursors path = some existing.length := by
  rw [h path]
  simpa using cursorAt_list_length [] path data existing found unique

/-- A disjoint object patch preserves old cursors and adds its new field cursors,
by typed merging and local cursor splitting. -/
theorem modifyAtPath_object_cursors (path : ResponsePath) (data : ResponseValue)
    (incoming : List (Name × ResponseValue))
    (member : (path, Atom.object) ∈ value [] data)
    (unique : ((value [] data ++ fields path incoming).map Prod.fst).Nodup)
    : ∃ updated,
        ResponseMerging.modifyAtPath path
            (fun data =>
              match data with
              | .object existing =>
                  some (.object (ResponseMerging.putFields existing incoming))
              | _ => none) data
          = some updated
        ∧ (value [] updated).Perm (value [] data ++ fields path incoming)
        ∧ (listCursors [] updated).Perm
            (fieldCursors path incoming ++ listCursors [] data) := by
  have hu : ((value [] data).map Prod.fst).Nodup :=
    (List.nodup_append.mp (by simpa only [List.map_append] using unique)).1
  obtain ⟨old, hf, ha⟩ := atPath_of_entry [] path data .object (by simpa using member) hu
  cases old with
  | null | scalar _ | list _ => simp [rootAtom] at ha
  | object existing =>
      obtain ⟨updated, hm, he⟩ := modifyAtPath_object_entries [] path data incoming
        (by simpa using member) (by simpa using unique)
      have hsub : ((fields path (existing ++ incoming)).map Prod.fst).Nodup := by
        have hs := atPath_entries_sublist [] path data (.object existing) hf
        simpa [value, fields_append] using (List.nodup_cons.mp ((hs.append_right (fields path incoming)).map Prod.fst |>.nodup unique)).2
      have hput := putFields_eq_append_of_nodup existing incoming (fields_keys_nodup path _ hsub)
      obtain ⟨result, outside, hr, ho, hn⟩ := modifyAtPath_cursor_split [] path data
        (.object existing) (.object (existing ++ incoming))
        (fun data => match data with
          | .object existing => some (.object (ResponseMerging.putFields existing incoming))
          | _ => none) hf (by simp [hput]) hu
      have hrEq := Option.some.inj (hr.symm.trans hm)
      subst result
      refine ⟨updated, hm, by simpa using he, ?_⟩
      simp only [List.nil_append, listCursors, fieldCursors_append] at ho hn
      apply hn.trans
      have hp : ((fieldCursors path existing ++ fieldCursors path incoming) ++ outside).Perm
          (fieldCursors path incoming ++ (fieldCursors path existing ++ outside)) := by
        simpa only [List.append_assoc]
          using cursors_swap
            (fieldCursors path existing) (fieldCursors path incoming) outside
      exact hp.trans (ho.symm.append_left _)

/-- Object merging preserves typed entries and cursor agreement, by cursor permutation
and left-biased lookup through the incoming field cursors. -/
theorem merge_object_cursorRepresents (path : ResponsePath) (data : ResponseValue)
    (incoming : List (Name × ResponseValue)) (cursors : Cursors)
    (represents : CursorRepresents cursors data)
    (member : (path, Atom.object) ∈ value [] data)
    (unique : ((value [] data ++ fields path incoming).map Prod.fst).Nodup)
    : ∃ updated,
        ResponseMerging.modifyAtPath path
            (fun data =>
              match data with
              | .object existing =>
                  some (.object (ResponseMerging.putFields existing incoming))
              | _ => none) data
          = some updated
        ∧ (value [] updated).Perm (value [] data ++ fields path incoming)
        ∧ CursorRepresents (fieldCursors path incoming ++ cursors) updated := by
  obtain ⟨updated, hm, he, hc⟩ := modifyAtPath_object_cursors path data incoming member unique
  refine ⟨updated, hm, he, ?_⟩
  have hn := (listCursors_sublist [] updated).nodup ((he.map Prod.fst).nodup_iff.mpr unique)
  intro target
  rw [cursorAt_perm hc hn target, cursorAt_append_eq, cursorAt_append_eq, represents target]

/-- Appending one stream item preserves typed entries and cursor agreement; the
old cursor equals the list length, and the new cursor shadows it by one. -/
theorem merge_stream_cursorRepresents (path : ResponsePath) (index : Nat)
    (data incoming : ResponseValue) (cursors : Cursors)
    (represents : CursorRepresents cursors data)
    (member : (path, Atom.list) ∈ value [] data)
    (cursor : cursorAt cursors path = some index)
    (unique
      : ((value [] data ++ value (path ++ [.index index]) incoming).map Prod.fst).Nodup)
    : ∃ updated,
        ResponseMerging.modifyAtPath path
            (fun data =>
              match data with
              | .list existing => some (.list (existing ++ [incoming]))
              | _ => none) data
          = some updated
        ∧ (value [] updated).Perm
            (value [] data ++ value (path ++ [.index index]) incoming)
        ∧ CursorRepresents
            ((path, index + 1) :: listCursors (path ++ [.index index]) incoming
              ++ cursors) updated := by
  have hu : ((value [] data).map Prod.fst).Nodup :=
    (List.nodup_append.mp (by simpa only [List.map_append] using unique)).1
  obtain ⟨existing, hf⟩ := atPath_list_of_entry [] path data (by simpa using member) hu
  have hi : existing.length = index := Option.some.inj ((represents.list_length hf hu).symm.trans cursor)
  obtain ⟨updated, hm, he⟩ := modifyAtPath_list_entries [] path data existing [incoming] hf hu
  simp only [List.nil_append, items, List.append_nil, hi] at he
  obtain ⟨result, outside, hr, ho, hn⟩ := modifyAtPath_cursor_split [] path data
    (.list existing) (.list (existing ++ [incoming]))
    (fun data => match data with
      | .list existing => some (.list (existing ++ [incoming]))
      | _ => none) hf rfl hu
  have hrEq := Option.some.inj (hr.symm.trans hm)
  subst result
  refine ⟨updated, hm, he, ?_⟩
  simp only [List.nil_append, listCursors, List.length_append, List.length_singleton,
    itemCursors_append, Nat.zero_add, hi, itemCursors, List.append_nil, List.cons_append] at ho hn
  have hnew : (listCursors [] updated).Perm
      ((path, index + 1) :: (listCursors (path ++ [.index index]) incoming ++
        (itemCursors path 0 existing ++ outside))) := by
    apply hn.trans
    simpa only [List.append_assoc]
      using (cursors_swap (itemCursors path 0 existing)
              (listCursors (path ++ [.index index]) incoming) outside).cons
        (path, index + 1)
  have huOld := (listCursors_sublist [] data).nodup hu
  have huNew := (listCursors_sublist [] updated).nodup ((he.map Prod.fst).nodup_iff.mpr unique)
  intro target
  rw [cursorAt_perm hnew huNew target]
  simp only [List.cons_append, cursorAt_cons]
  by_cases ht : path = target
  · simp [ht]
  · simp only [ht, ↓reduceIte, cursorAt_append_eq]
    rw [represents target, cursorAt_perm ho huOld target]
    simp only [cursorAt_cons, ht, ↓reduceIte, cursorAt_append_eq]

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
