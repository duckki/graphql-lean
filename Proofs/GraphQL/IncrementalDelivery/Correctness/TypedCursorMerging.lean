import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedListMerging
import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedCursorSeeds

/-! The client cursor table is the list-length projection of its current data.
Historical overwritten entries are compared by lookup, not table equality.
-/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ResponsePositions (Cursors cursorAt listCursors fieldCursors itemCursors)

/-- Swapping two cursor prefixes preserves their permutation, by list append laws. -/
theorem cursors_swap (a b c : Cursors) : (a ++ (b ++ c)).Perm (b ++ (a ++ c)) := by
  simpa only [List.append_assoc]
    using (List.perm_append_comm (l₁ := a) (l₂ := b)).append_right c

mutual
  /-- List cursor paths occur among typed value paths, by mutual value induction. -/
  theorem listCursors_sublist (path : ResponsePath) (data : ResponseValue)
      : ((listCursors path data).map Prod.fst).Sublist
          ((value path data).map Prod.fst) := by
    cases data with
    | null | scalar _ => exact List.nil_sublist _
    | object data => exact (fieldCursors_sublist path data).cons _
    | list data => exact (itemCursors_sublist path 0 data).cons_cons _

  /-- Field cursor paths occur among typed field paths, by mutual list induction. -/
  theorem fieldCursors_sublist (path : ResponsePath) (data : List (Name × ResponseValue))
      : ((fieldCursors path data).map Prod.fst).Sublist
          ((fields path data).map Prod.fst) := by
    cases data with
    | nil => exact .refl _
    | cons head tail =>
        simpa only [fieldCursors, fields, List.map_append]
          using (listCursors_sublist (path ++ [.field head.1]) head.2).append
            (fieldCursors_sublist path tail)

  /-- Item cursor paths occur among typed item paths, by mutual list induction. -/
  theorem itemCursors_sublist (path : ResponsePath) (index : Nat)
      (data : List ResponseValue)
      : ((itemCursors path index data).map Prod.fst).Sublist
          ((items path index data).map Prod.fst) := by
    cases data with
    | nil => exact .refl _
    | cons head tail =>
        simpa only [itemCursors, items, List.map_append]
          using (listCursors_sublist (path ++ [.index index]) head).append
            (itemCursors_sublist path (index + 1) tail)
end

/-- Field cursor extraction distributes over append, by list induction. -/
theorem fieldCursors_append (path : ResponsePath)
    (left right : List (Name × ResponseValue))
    : fieldCursors path (left ++ right)
      = fieldCursors path left ++ fieldCursors path right := by
  induction left with
  | nil => rfl
  | cons head tail ih => simp [fieldCursors, ih, List.append_assoc]

/-- Item cursor extraction distributes over append with the shifted index,
by list induction. -/
theorem itemCursors_append (path : ResponsePath) (index : Nat)
    (left right : List ResponseValue)
    : itemCursors path index (left ++ right)
      = itemCursors path index left ++ itemCursors path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [itemCursors]
  | cons head tail ih =>
      simp [itemCursors, ih, List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

/-- Replacing a unique field separates its cursors from unchanged outside cursors,
by induction through the surrounding fields. -/
theorem fieldCursors_replace_split (base : ResponsePath) (name : Name)
    (old updated : ResponseValue) (data : List (Name × ResponseValue))
    (hn : (data.map Prod.fst).Nodup) (hm : (name, old) ∈ data)
    : ∃ outside,
        (fieldCursors base data).Perm (listCursors (base ++ [.field name]) old ++ outside)
        ∧ (fieldCursors base
            (data.map
              (fun field => if field.1 == name then (name, updated) else field))).Perm
            (listCursors (base ++ [.field name]) updated ++ outside) := by
  induction data with
  | nil => simp at hm
  | cons field rest ih =>
      have hnd := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with rfl | hm
      · refine ⟨fieldCursors base rest, .refl _, ?_⟩
        simp only [List.map_cons, beq_self_eq_true, ↓reduceIte,
          fields_map_absent name updated rest hnd.1, fieldCursors]
        exact .refl _
      · have hne : field.1 ≠ name := by
          intro he
          exact hnd.1 (List.mem_map.mpr ⟨(name, old), hm, he.symm⟩)
        obtain ⟨outside, ho, hu⟩ := ih hnd.2 hm
        refine ⟨listCursors (base ++ [.field field.1]) field.2 ++ outside, ?_, ?_⟩
        · exact (ho.append_left _).trans (cursors_swap _ _ _)
        · simp only [List.map_cons, beq_eq_false_iff_ne.mpr hne, Bool.false_eq_true,
            ↓reduceIte, fieldCursors]
          exact (hu.append_left _).trans (cursors_swap _ _ _)

/-- Replacing one indexed item separates its cursors from unchanged outside cursors,
by induction on the item index. -/
theorem itemCursors_set_split (base : ResponsePath) (start index : Nat)
    (old updated : ResponseValue) (data : List ResponseValue)
    (hm : data[index]? = some old)
    : ∃ outside,
        (itemCursors base start data).Perm
          (listCursors (base ++ [.index (start + index)]) old ++ outside)
        ∧ (itemCursors base start (data.set index updated)).Perm
            (listCursors (base ++ [.index (start + index)]) updated ++ outside) := by
  induction data generalizing start index with
  | nil => simp at hm
  | cons head rest ih =>
      cases index with
      | zero =>
          simp at hm
          subst head
          exact ⟨
            itemCursors base (start + 1) rest,
            by simp [itemCursors],
            by simp [itemCursors]
          ⟩
      | succ index =>
          obtain ⟨outside, ho, hu⟩ := ih (start + 1) index (by simpa using hm)
          refine ⟨listCursors (base ++ [.index start]) head ++ outside, ?_, ?_⟩
          · simpa only [itemCursors, Nat.add_assoc, Nat.add_comm 1]
              using (ho.append_left _).trans (cursors_swap _ _ _)
          · simpa only [List.set_cons_succ, itemCursors, Nat.add_assoc, Nat.add_comm 1]
              using (hu.append_left _).trans (cursors_swap _ _ _)

/-- A local modification replaces only the target subtree's cursors, by path
induction and the field/item cursor splitting lemmas. -/
theorem modifyAtPath_cursor_split (base path : ResponsePath)
    (data old updated : ResponseValue) (modify : ResponseValue → Option ResponseValue)
    (found : atPath path data = some old) (changed : modify old = some updated)
    (unique : ((value base data).map Prod.fst).Nodup)
    : ∃ result outside,
        ResponseMerging.modifyAtPath path modify data = some result
        ∧ (listCursors base data).Perm (listCursors (base ++ path) old ++ outside)
        ∧ (listCursors base result).Perm
            (listCursors (base ++ path) updated ++ outside) := by
  induction path generalizing base data with
  | nil =>
      have he : data = old := Option.some.inj found
      subst data
      exact ⟨updated, [], changed, by simp, by simp⟩
  | cons segment rest ih =>
      cases segment with
      | field name =>
          cases data with
          | null | scalar _ | list _ => simp [atPath] at found
          | object data =>
              cases hf : data.find? (fun field => field.1 == name) with
              | none => simp [atPath, hf] at found
              | some field =>
                  have hm := List.mem_of_find?_eq_some hf
                  have hk : field.1 = name := by simpa using List.find?_some hf
                  rcases field with ⟨fname, child⟩
                  dsimp only at hk
                  subst fname
                  have hu := (List.nodup_cons.mp unique).2
                  have hkeys := fields_keys_nodup base data hu
                  have hc := ((value_sublist_fields base name child data hm).map Prod.fst).nodup hu
                  obtain ⟨result, inside, hr, ho, hn⟩ := ih (base ++ [.field name]) child
                    (by simpa only [atPath, hf, Option.bind_some] using found) hc
                  obtain ⟨outside, hfo, hfn⟩ := fieldCursors_replace_split base name child result data hkeys hm
                  refine ⟨
                    .object
                      (data.map
                        (fun field => if field.1 == name then (name, result) else field)),
                    inside ++ outside,
                    ?_,
                    ?_,
                    ?_
                  ⟩
                  · simp only [ResponseMerging.modifyAtPath, hf, Option.bind_eq_bind,
                      Option.bind_some, hr, Option.pure_def]
                  · simpa only [listCursors, List.append_assoc, List.singleton_append]
                      using hfo.trans (ho.append_right outside)
                  · simpa only [listCursors, List.append_assoc, List.singleton_append]
                      using hfn.trans (hn.append_right outside)
      | index index =>
          cases data with
          | null | scalar _ | object _ => simp [atPath] at found
          | list data =>
              cases hf : data[index]? with
              | none => simp [atPath, hf] at found
              | some child =>
                  have hu := (List.nodup_cons.mp unique).2
                  have hc := ((items_value_sublist base 0 index data child hf).map Prod.fst).nodup hu
                  simp only [Nat.zero_add] at hc
                  obtain ⟨result, inside, hr, ho, hn⟩ := ih (base ++ [.index index]) child
                    (by simpa only [atPath, hf, Option.bind_some] using found) hc
                  obtain ⟨outside, hfo, hfn⟩ := itemCursors_set_split base 0 index child result data hf
                  simp only [Nat.zero_add] at hfo hfn
                  refine ⟨
                    .list (data.set index result),
                    (base, data.length) :: (inside ++ outside),
                    ?_,
                    ?_,
                    ?_
                  ⟩
                  · simp only [ResponseMerging.modifyAtPath, hf, Option.bind_eq_bind,
                      Option.bind_some, hr, Option.pure_def]
                  · have hp := (hfo.trans (ho.append_right outside)).cons (base, data.length)
                    apply hp.trans
                    simpa only [List.append_assoc, List.singleton_append]
                      using cursors_swap [(base, data.length)]
                        (listCursors (base ++ .index index :: rest) old)
                        (inside ++ outside)
                  · have hp := (hfn.trans (hn.append_right outside)).cons (base, data.length)
                    simp only [listCursors, List.length_set]
                    apply hp.trans
                    simpa only [List.append_assoc, List.singleton_append]
                      using cursors_swap [(base, data.length)]
                        (listCursors (base ++ .index index :: rest) updated)
                        (inside ++ outside)

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
