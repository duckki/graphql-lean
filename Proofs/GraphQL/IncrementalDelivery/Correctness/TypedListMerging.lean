import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedObjectMerging

/-! Appending a streamed payload at an existing list preserves all typed entries.
The append index is the actual attachment length, not a guessed stream offset.
-/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

/-- Read-only lookup follows object names and list indices in a response value. -/
def atPath : ResponsePath → ResponseValue → Option ResponseValue
  | [], data => some data
  | .field name :: rest, .object data =>
      (data.find? (fun field => field.1 == name)).bind (fun field => atPath rest field.2)
  | .index index :: rest, .list data => data[index]?.bind (atPath rest)
  | _, _ => none

/-- A unique typed entry identifies a value at its relative path, by path induction. -/
theorem atPath_of_entry (base path : ResponsePath) (data : ResponseValue) (atom : Atom)
    (member : (base ++ path, atom) ∈ value base data)
    (unique : ((value base data).map Prod.fst).Nodup)
    : ∃ found, atPath path data = some found ∧ rootAtom found = atom := by
  induction path generalizing base data with
  | nil =>
      exact ⟨data, rfl, (value_root_atom base data atom (by simpa using member)).symm⟩
  | cons segment rest ih =>
      have hne : base ++ segment :: rest ≠ base := by
        intro he
        have hl := congrArg List.length he
        simp at hl
      cases data with
      | null =>
          have he := List.mem_singleton.mp member
          exact (hne (Prod.mk.inj he).1).elim
      | scalar text =>
          have he := List.mem_singleton.mp member
          exact (hne (Prod.mk.inj he).1).elim
      | object data =>
          have hm : (base ++ segment :: rest, atom) ∈ fields base data := by
            rcases List.mem_cons.mp member with he | hm
            · exact (hne (Prod.mk.inj he).1).elim
            · exact hm
          obtain ⟨name, child, hc, hm⟩ := fields_entry_member base data _ hm
          have hseg : segment = .field name :=
            below_children_eq (⟨rest, by simp⟩ : Below (base ++ [segment])
              (base ++ segment :: rest)) (value_below _ child _ hm)
          subst segment
          have hu := (List.nodup_cons.mp unique).2
          have hcu := ((value_sublist_fields base name child data hc).map Prod.fst).nodup hu
          obtain ⟨found, hf, ha⟩ := ih (base ++ [.field name]) child
            (by simpa only [List.append_assoc, List.singleton_append] using hm) hcu
          refine ⟨found, ?_, ha⟩
          simp only [atPath, fields_find_member name child data (fields_keys_nodup base data hu) hc,
            Option.bind_some, hf]
      | list data =>
          have hm : (base ++ segment :: rest, atom) ∈ items base 0 data := by
            rcases List.mem_cons.mp member with he | hm
            · exact (hne (Prod.mk.inj he).1).elim
            · exact hm
          obtain ⟨index, child, hc, hm⟩ := items_entry_member base 0 data _ hm
          simp only [Nat.zero_add] at hm
          have hseg : segment = .index index :=
            below_children_eq (⟨rest, by simp⟩ : Below (base ++ [segment])
              (base ++ segment :: rest)) (value_below _ child _ hm)
          subst segment
          have hu := (List.nodup_cons.mp unique).2
          have hcu := ((items_value_sublist base 0 index data child hc).map Prod.fst).nodup hu
          simp only [Nat.zero_add] at hcu
          obtain ⟨found, hf, ha⟩ := ih (base ++ [.index index]) child
            (by simpa only [List.append_assoc, List.singleton_append] using hm) hcu
          exact ⟨found, by simp only [atPath, hc, Option.bind_some, hf], ha⟩

/-- A list-tag entry identifies an actual list, by typed lookup and constructor cases. -/
theorem atPath_list_of_entry (base path : ResponsePath) (data : ResponseValue)
    (member : (base ++ path, Atom.list) ∈ value base data)
    (unique : ((value base data).map Prod.fst).Nodup)
    : ∃ items, atPath path data = some (.list items) := by
  obtain ⟨found, hf, ha⟩ := atPath_of_entry base path data .list member unique
  cases found <;> simp only [rootAtom] at ha
  · contradiction
  · contradiction
  · contradiction
  · exact ⟨_, hf⟩

/-- A successful lookup's typed subtree is a sublist of the whole inventory,
by induction on the lookup path. -/
theorem atPath_entries_sublist (base path : ResponsePath) (data found : ResponseValue)
    (hf : atPath path data = some found)
    : (value (base ++ path) found).Sublist (value base data) := by
  induction path generalizing base data with
  | nil =>
      have he : data = found := Option.some.inj hf
      subst data
      simp
  | cons segment rest ih =>
      cases segment with
      | field name =>
          cases data with
          | null | scalar _ | list _ => simp [atPath] at hf
          | object data =>
              cases hc : data.find? (fun field => field.1 == name) with
              | none => simp [atPath, hc] at hf
              | some field =>
                  have hk : field.1 = name := by simpa using List.find?_some hc
                  have hs := ih (base ++ [.field name]) field.2
                    (by simpa only [atPath, hc, Option.bind_some] using hf)
                  have hm : (name, field.2) ∈ data := by
                    rw [← hk]
                    exact List.mem_of_find?_eq_some hc
                  simpa only [List.append_assoc, List.singleton_append, value]
                    using (hs.trans (value_sublist_fields base name field.2 data hm)).cons
                      (base, Atom.object)
      | index index =>
          cases data with
          | null | scalar _ | object _ => simp [atPath] at hf
          | list data =>
              cases hc : data[index]? with
              | none => simp [atPath, hc] at hf
              | some child =>
                  have hs := ih (base ++ [.index index]) child
                    (by simpa only [atPath, hc, Option.bind_some] using hf)
                  have hm := items_value_sublist base 0 index data child hc
                  simp only [Nat.zero_add] at hm
                  simpa only [List.append_assoc, List.singleton_append, value]
                    using (hs.trans hm).cons (base, Atom.list)

/-- Typed entries of appended lists concatenate at the shifted index, by list
induction.
-/
theorem items_append (path : ResponsePath) (index : Nat) (left right : List ResponseValue)
    : items path index (left ++ right)
      = items path index left ++ items path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [items]
  | cons head tail ih =>
      simp [items, ih, List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

/-- A successful local modification extends exactly its typed subtree, by path
induction and field/item replacement lemmas. -/
theorem modifyAtPath_entries (base path : ResponsePath) (data old updated : ResponseValue)
    (modify : ResponseValue → Option ResponseValue) (extra : List Entry)
    (found : atPath path data = some old) (changed : modify old = some updated)
    (unique : ((value base data).map Prod.fst).Nodup)
    (entries : (value (base ++ path) updated).Perm (value (base ++ path) old ++ extra))
    : ∃ result,
        ResponseMerging.modifyAtPath path modify data = some result
        ∧ (value base result).Perm (value base data ++ extra) := by
  induction path generalizing base data with
  | nil =>
      have he : data = old := Option.some.inj found
      subst data
      exact ⟨updated, changed, by simpa only [List.append_nil] using entries⟩
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
                  have hfound : atPath rest child = some old := by simpa only [atPath, hf, Option.bind_some] using found
                  obtain ⟨result, hr, he⟩ := ih (base ++ [.field name]) child hfound hc
                    (by simpa only [List.append_assoc, List.singleton_append] using entries)
                  refine ⟨
                    .object
                      (data.map
                        (fun field => if field.1 == name then (name, result) else field)),
                    ?_,
                    ?_
                  ⟩
                  · simp only [ResponseMerging.modifyAtPath, hf, Option.bind_eq_bind,
                      Option.bind_some, hr, Option.pure_def]
                  · simpa only [value, List.cons_append]
                      using (fields_replace_entries base name child result data extra
                              hkeys hm he).cons
                        (base, Atom.object)
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
                  have hfound : atPath rest child = some old := by simpa only [atPath, hf, Option.bind_some] using found
                  obtain ⟨result, hr, he⟩ := ih (base ++ [.index index]) child hfound hc
                    (by simpa only [List.append_assoc, List.singleton_append] using entries)
                  refine ⟨.list (data.set index result), ?_, ?_⟩
                  · simp only [ResponseMerging.modifyAtPath, hf, Option.bind_eq_bind,
                      Option.bind_some, hr, Option.pure_def]
                  · simpa only [value, List.cons_append]
                      using (items_set_entries base 0 index child result data extra hf
                              (by simpa only [Nat.zero_add] using he)).cons
                        (base, Atom.list)

/-- Appending list items at an existing list preserves all old typed entries and
adds the suffix at the old length, by local modification and list concatenation. -/
theorem modifyAtPath_list_entries (base path : ResponsePath) (data : ResponseValue)
    (existing incoming : List ResponseValue)
    (found : atPath path data = some (.list existing))
    (unique : ((value base data).map Prod.fst).Nodup)
    : ∃ updated,
        ResponseMerging.modifyAtPath path
            (fun data =>
              match data with
              | .list existing => some (.list (existing ++ incoming))
              | _ => none) data
          = some updated
        ∧ (value base updated).Perm
            (value base data ++ items (base ++ path) existing.length incoming) := by
  apply modifyAtPath_entries base path data (.list existing) (.list (existing ++ incoming))
    _ (items (base ++ path) existing.length incoming) found rfl unique
  simp [value, items_append]

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
