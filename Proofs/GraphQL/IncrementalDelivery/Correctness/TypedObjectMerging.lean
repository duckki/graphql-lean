import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedResponse
import Proofs.GraphQL.IncrementalDelivery.Correctness.ResponseMerging

/-! Object patches preserve exact typed entries when their parent exists. -/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

/-- A typed field entry comes from one response field, by list induction. -/
theorem fields_entry_member (base : ResponsePath) (data : List (Name × ResponseValue))
    (entry : Entry) (hm : entry ∈ fields base data)
    : ∃ name child,
        (name, child) ∈ data ∧ entry ∈ value (base ++ [.field name]) child := by
  induction data with
  | nil => simp [fields] at hm
  | cons field rest ih =>
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨field.1, field.2, by simp, hm⟩
      · obtain ⟨name, child, hc, hm⟩ := ih hm
        exact ⟨name, child, by simp [hc], hm⟩

/-- A successful field lookup witnesses membership, by induction over the fields. -/
theorem fields_find_member (name : Name) (child : ResponseValue)
    (data : List (Name × ResponseValue)) (hn : (data.map Prod.fst).Nodup)
    (hm : (name, child) ∈ data)
    : data.find? (fun field => field.1 == name) = some (name, child) := by
  induction data with
  | nil => simp at hm
  | cons field rest ih =>
      have hnd := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with rfl | hm
      · simp
      · have hne : field.1 ≠ name := by
          intro he
          exact hnd.1 (List.mem_map.mpr ⟨(name, child), hm, he.symm⟩)
        simpa [hne] using ih hnd.2 hm

/-- Replacing an absent field leaves the object unchanged, by list induction. -/
theorem fields_map_absent (name : Name) (updated : ResponseValue)
    (data : List (Name × ResponseValue)) (hn : name ∉ data.map Prod.fst)
    : data.map (fun field => if field.1 == name then (name, updated) else field)
      = data := by
  induction data with
  | nil => rfl
  | cons field rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hn
      simp only [List.map_cons, beq_eq_false_iff_ne.mpr (Ne.symm hn.1),
        Bool.false_eq_true, ↓reduceIte, ih hn.2]

/-- Replacing a uniquely named field replaces exactly its typed subtree, by
splitting the surrounding field entries and transporting the entry permutation. -/
theorem fields_replace_entries (base : ResponsePath) (name : Name)
    (old updated : ResponseValue) (data : List (Name × ResponseValue))
    (extra : List Entry) (hn : (data.map Prod.fst).Nodup) (hm : (name, old) ∈ data)
    (hp
      : (value (base ++ [.field name]) updated).Perm
          (value (base ++ [.field name]) old ++ extra))
    : (fields base
        (data.map (fun field => if field.1 == name then (name, updated) else field))).Perm
        (fields base data ++ extra) := by
  induction data with
  | nil => simp at hm
  | cons field rest ih =>
      have hnd := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with rfl | hm
      · simp only [List.map_cons, beq_self_eq_true, ↓reduceIte,
          fields_map_absent name updated rest hnd.1, fields]
        apply (hp.append_right (fields base rest)).trans
        simpa [List.append_assoc]
          using (List.perm_append_comm (l₁ := extra) (l₂ := fields base rest)).append_left
            (value (base ++ [.field name]) old)
      · have hne : field.1 ≠ name := by
          intro he
          exact hnd.1 (List.mem_map.mpr ⟨(name, old), hm, he.symm⟩)
        simpa [hne, fields, List.append_assoc]
          using (ih hnd.2 hm).append_left (value (base ++ [.field field.1]) field.2)

/-- A typed item entry comes from one indexed list value, by list induction. -/
theorem items_entry_member (base : ResponsePath) (start : Nat) (data : List ResponseValue)
    (entry : Entry) (hm : entry ∈ items base start data)
    : ∃ index child,
        data[index]? = some child
        ∧ entry ∈ value (base ++ [.index (start + index)]) child := by
  induction data generalizing start with
  | nil => simp [items] at hm
  | cons head rest ih =>
      rcases List.mem_append.mp hm with hm | hm
      · exact ⟨0, head, rfl, by simpa using hm⟩
      · obtain ⟨index, child, hc, hm⟩ := ih (start + 1) hm
        exact ⟨index + 1, child, hc, by simpa [Nat.add_assoc, Nat.add_comm 1] using hm⟩

/-- An indexed item's typed entries form a sublist of the full item inventory,
by induction on its position. -/
theorem items_value_sublist (base : ResponsePath) (start index : Nat)
    (data : List ResponseValue) (child : ResponseValue) (hm : data[index]? = some child)
    : (value (base ++ [.index (start + index)]) child).Sublist
        (items base start data) := by
  induction data generalizing start index with
  | nil => simp at hm
  | cons head rest ih =>
      cases index with
      | zero =>
          simp at hm
          subst child
          simp only [Nat.add_zero, items]
          exact List.sublist_append_left _ _
      | succ index =>
          simp only [List.getElem?_cons_succ] at hm
          have hp := (ih (start + 1) index hm).trans
            (List.sublist_append_right (value (base ++ [.index start]) head)
              (items base (start + 1) rest))
          simpa [items, Nat.add_assoc, Nat.add_comm 1] using hp

/-- Updating one list item replaces exactly its typed subtree, by indexed induction. -/
theorem items_set_entries (base : ResponsePath) (start index : Nat)
    (old updated : ResponseValue) (data : List ResponseValue) (extra : List Entry)
    (hm : data[index]? = some old)
    (hp
      : (value (base ++ [.index (start + index)]) updated).Perm
          (value (base ++ [.index (start + index)]) old ++ extra))
    : (items base start (data.set index updated)).Perm
        (items base start data ++ extra) := by
  induction data generalizing start index with
  | nil => simp at hm
  | cons head rest ih =>
      cases index with
      | zero =>
          simp at hm
          subst head
          simp only [Nat.add_zero] at hp
          simp only [List.set_cons_zero, items]
          apply (hp.append_right (items base (start + 1) rest)).trans
          simpa [List.append_assoc]
            using (List.perm_append_comm (l₁ := extra)
                    (l₂ := items base (start + 1) rest)).append_left
              (value (base ++ [.index start]) old)
      | succ index =>
          simp only [List.getElem?_cons_succ] at hm
          have hp' := ih (start + 1) index hm
            (by simpa [Nat.add_assoc, Nat.add_comm 1] using hp)
          simpa [items, List.append_assoc]
            using hp'.append_left (value (base ++ [.index start]) head)

/-- A disjoint object patch at an existing object merges successfully and appends
exactly its typed entries, by induction on the attachment path. -/
theorem modifyAtPath_object_entries (base path : ResponsePath) (data : ResponseValue)
    (incoming : List (Name × ResponseValue))
    (hm : (base ++ path, Atom.object) ∈ value base data)
    (hn : ((value base data ++ fields (base ++ path) incoming).map Prod.fst).Nodup)
    : ∃ updated,
        ResponseMerging.modifyAtPath path
            (fun data =>
              match data with
              | .object existing =>
                  some (.object (ResponseMerging.putFields existing incoming))
              | _ => none) data
          = some updated
        ∧ (value base updated).Perm
            (value base data ++ fields (base ++ path) incoming) := by
  induction path generalizing base data with
  | nil =>
      simp only [List.append_nil] at hm hn ⊢
      have ha := value_root_atom base data .object hm
      cases data with
      | null | scalar text | list items => simp [rootAtom] at ha
      | object existing =>
          have hk : ((existing ++ incoming).map Prod.fst).Nodup := by
            apply fields_keys_nodup base
            simpa [value, fields_append] using (List.nodup_cons.mp hn).2
          refine ⟨.object (existing ++ incoming), ?_, ?_⟩
          · simp [ResponseMerging.modifyAtPath,
              putFields_eq_append_of_nodup existing incoming hk]
          · simp [value, fields_append]
  | cons segment rest ih =>
      have hne : base ++ segment :: rest ≠ base := by
        intro he
        have hl := congrArg List.length he
        simp at hl
      cases data with
      | null =>
          simp only [value, List.mem_singleton, Prod.mk.injEq] at hm
          exact (hne hm.1).elim
      | scalar text => simp [value] at hm
      | object existing =>
          have hmf : (base ++ segment :: rest, Atom.object) ∈ fields base existing := by
            rcases List.mem_cons.mp hm with he | hm
            · exact (hne (Prod.mk.inj he).1).elim
            · exact hm
          obtain ⟨name, child, hc, hmchild⟩ := fields_entry_member base existing _ hmf
          have hseg : segment = .field name :=
            below_children_eq (⟨rest, by simp⟩ : Below (base ++ [segment])
                (base ++ segment :: rest))
              (value_below _ child _ hmchild)
          subst segment
          have hnd : ((fields base existing).map Prod.fst).Nodup := by
            exact (List.nodup_cons.mp (List.nodup_append.mp
              (by simpa only [List.map_append, value, List.map_cons] using hn)).1).2
          have hkeys := fields_keys_nodup base existing hnd
          have hsub := (value_sublist_fields base name child existing hc).cons (base, Atom.object)
          have hnchild := ((hsub.append_right
            (fields (base ++ .field name :: rest) incoming)).map Prod.fst).nodup hn
          obtain ⟨updated, hu, hp⟩ := ih (base ++ [.field name]) child
            (by simpa [List.append_assoc] using hmchild)
            (by simpa [List.append_assoc] using hnchild)
          refine ⟨.object (existing.map
            (fun field => if field.1 == name then (name, updated) else field)), ?_, ?_⟩
          · simp only [ResponseMerging.modifyAtPath,
              fields_find_member name child existing hkeys hc, Option.bind_eq_bind,
              Option.bind_some, hu, Option.pure_def]
          · have hmapped := fields_replace_entries base name child updated existing
              (fields ((base ++ [.field name]) ++ rest) incoming) hkeys hc hp
            simpa [value, List.append_assoc] using hmapped.cons (base, Atom.object)
      | list existing =>
          have hmf : (base ++ segment :: rest, Atom.object) ∈ items base 0 existing := by
            rcases List.mem_cons.mp hm with he | hm
            · cases (Prod.mk.inj he).2
            · exact hm
          obtain ⟨index, child, hc, hmchild⟩ := items_entry_member base 0 existing _ hmf
          simp only [Nat.zero_add] at hmchild
          have hseg : segment = .index index :=
            below_children_eq (⟨rest, by simp⟩ : Below (base ++ [segment])
                (base ++ segment :: rest))
              (value_below _ child _ hmchild)
          subst segment
          have hsub := (items_value_sublist base 0 index existing child hc).cons
            (base, Atom.list)
          simp only [Nat.zero_add] at hsub
          have hnchild := ((hsub.append_right
            (fields (base ++ .index index :: rest) incoming)).map Prod.fst).nodup hn
          obtain ⟨updated, hu, hp⟩ := ih (base ++ [.index index]) child
            (by simpa [List.append_assoc] using hmchild)
            (by simpa [List.append_assoc] using hnchild)
          refine ⟨.list (existing.set index updated), ?_, ?_⟩
          · simp only [ResponseMerging.modifyAtPath, hc, Option.bind_eq_bind,
              Option.bind_some, hu, Option.pure_def]
          · have hmapped := items_set_entries base 0 index child updated existing
              (fields ((base ++ [.index index]) ++ rest) incoming) hc
              (by simpa using hp)
            simpa [value, List.append_assoc] using hmapped.cons (base, Atom.list)

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
