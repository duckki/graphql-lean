import Proofs.GraphQL.IncrementalDelivery.Semantics.BasicErrors
import Proofs.GraphQL.IncrementalDelivery.Semantics.PathOwnership

/-! Typed absolute response entries, independent of scheduling or reconstruction. -/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

/-- The payload tag retained at one absolute response position. -/
inductive Atom where
  | null
  | scalar (text : String)
  | object
  | list
deriving DecidableEq, BEq, Repr

abbrev Entry := ResponsePath × Atom

/-- The tag of a response value before descending into its children. -/
def rootAtom : ResponseValue → Atom
  | .null => .null
  | .scalar text => .scalar text
  | .object _ => .object
  | .list _ => .list

mutual
  /-- Typed entries of a value, including its root container and all descendants. -/
  def value (path : ResponsePath) : ResponseValue → List Entry
    | .null => [(path, .null)]
    | .scalar text => [(path, .scalar text)]
    | .object data => (path, .object) :: fields path data
    | .list data => (path, .list) :: items path 0 data

  /-- Typed entries introduced by object fields under their response-name paths. -/
  def fields (path : ResponsePath) : List (Name × ResponseValue) → List Entry
    | [] => []
    | (name, data) :: rest =>
        value (path ++ [.field name]) data ++ fields path rest

  /-- Typed entries introduced by list items from the supplied absolute index. -/
  def items (path : ResponsePath) (index : Nat) : List ResponseValue → List Entry
    | [] => []
    | data :: rest =>
        value (path ++ [.index index]) data ++ items path (index + 1) rest
end

/-- Successful outcomes contribute typed entries; bubbling failures contribute none. -/
def result (entries : α → List Entry) : Result α → List Entry
  | .error _ => []
  | .ok (data, _) => entries data

/-- Object-field concatenation concatenates entries, by list induction. -/
@[simp]
theorem fields_append (path : ResponsePath) (left right : List (Name × ResponseValue))
    : fields path (left ++ right) = fields path left ++ fields path right := by
  induction left with
  | nil => rfl
  | cons head rest ih => simp [fields, ih, List.append_assoc]

/-- Every value contributes its own root tag, by its four constructors. -/
theorem root_mem_value (path : ResponsePath) (data : ResponseValue)
    : (path, rootAtom data) ∈ value path data := by
  cases data <;> simp [value, rootAtom]

/-- A value whose entries extend to a null singleton is null; its root tag is decisive. -/
theorem null_of_perm (path : ResponsePath) (data : ResponseValue) (extra : List Entry)
    (h : (value path data ++ extra).Perm (value path .null))
    : data = .null := by
  have hm := h.mem_iff.mp (List.mem_append_left extra (root_mem_value path data))
  have ha : rootAtom data = .null := by simpa [value] using hm
  cases data <;> simp_all [rootAtom]

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

mutual
  /-- Forgetting value tags recovers all source paths, by mutual structural descent. -/
  theorem value_paths (path : ResponsePath) (data : ResponseValue)
      : (value path data).map Prod.fst = DeliveryPaths.value true path data := by
    cases data with
    | null => rfl
    | scalar text => rfl
    | object data => simp [value, DeliveryPaths.value, fields_paths]
    | list data => simp [value, DeliveryPaths.value, items_paths]

  /-- Forgetting object-field tags recovers source field paths, by list descent. -/
  theorem fields_paths (path : ResponsePath) (data : List (Name × ResponseValue))
      : (fields path data).map Prod.fst = DeliveryPaths.fields true path data := by
    cases data with
    | nil => rfl
    | cons field rest => simp [fields, DeliveryPaths.fields, value_paths, fields_paths]

  /-- Forgetting item tags recovers indexed source paths, by list descent. -/
  theorem items_paths (path : ResponsePath) (index : Nat) (data : List ResponseValue)
      : (items path index data).map Prod.fst
        = DeliveryPaths.items true path index data := by
    cases data with
    | nil => rfl
    | cons head rest => simp [items, DeliveryPaths.items, value_paths, items_paths]
end

mutual
  /-- All value entries lie below the value's root, by structural descent. -/
  theorem value_below (path : ResponsePath) (data : ResponseValue) (entry : Entry)
      (h : entry ∈ value path data)
      : Below path entry.1 := by
    cases data with
    | null =>
        have he : entry = (path, Atom.null) := by simpa [value] using h
        subst entry
        exact below_self path
    | scalar text =>
        have he : entry = (path, Atom.scalar text) := by simpa [value] using h
        subst entry
        exact below_self path
    | object data =>
        rcases List.mem_cons.mp h with rfl | h
        · exact below_self path
        · exact underFields_below (fields_under path data entry h)
    | list data =>
        rcases List.mem_cons.mp h with rfl | h
        · exact below_self path
        · exact underItems_below (items_under path 0 data entry h)

  /-- Object entries lie below their field names, by mutual value/list descent. -/
  theorem fields_under (path : ResponsePath) (data : List (Name × ResponseValue))
      (entry : Entry) (h : entry ∈ fields path data)
      : UnderFields path (data.map Prod.fst) entry.1 := by
    cases data with
    | nil => simp [fields] at h
    | cons field rest =>
        rcases List.mem_append.mp h with h | h
        · exact ⟨field.1, by simp, value_below _ field.2 entry h⟩
        · exact underFields_mono (fun name hn => List.mem_cons_of_mem _ hn)
            (fields_under path rest entry h)

  /-- List entries lie below an index at least the starting index, by list descent. -/
  theorem items_under (path : ResponsePath) (index : Nat) (data : List ResponseValue)
      (entry : Entry) (h : entry ∈ items path index data)
      : UnderItems path index entry.1 := by
    cases data with
    | nil => simp [items] at h
    | cons head rest =>
        rcases List.mem_append.mp h with h | h
        · exact ⟨index, Nat.le_refl _, value_below _ head entry h⟩
        · obtain ⟨next, hn, he⟩ := items_under path (index + 1) rest entry h
          exact ⟨next, by omega, he⟩
end

/-- Retain precisely the typed entries at or below an absolute response path. -/
def subtree (path : ResponsePath) (entries : List Entry) : List Entry :=
  entries.filter (fun entry => path.isPrefixOf entry.1)

/-- Boolean path-prefix lookup agrees with the suffix witness for Below. -/
theorem isPrefixOf_iff_below (base path : ResponsePath)
    : base.isPrefixOf path = true ↔ Below base path := by
  simp only [List.isPrefixOf_iff_prefix, List.IsPrefix, Below]
  exact exists_congr (fun _ => eq_comm)

/-- Selecting a value's root subtree retains every entry, by path provenance. -/
theorem subtree_value (path : ResponsePath) (data : ResponseValue)
    : subtree path (value path data) = value path data := by
  apply List.filter_eq_self.mpr
  intro entry he
  exact (isPrefixOf_iff_below _ _).mpr (value_below path data entry he)

/-- Subtree selection distributes over concatenation, by filter append. -/
@[simp]
theorem subtree_append (path : ResponsePath) (left right : List Entry)
    : subtree path (left ++ right) = subtree path left ++ subtree path right :=
  List.filter_append left right

/-- Distinct child segments have disjoint subtrees, by prefix separation. -/
theorem subtree_child_value_other (path : ResponsePath) (left right : ResponsePathSegment)
    (h : left ≠ right) (data : ResponseValue)
    : subtree (path ++ [left]) (value (path ++ [right]) data) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry he
  intro hp
  exact h (below_children_eq ((isPrefixOf_iff_below _ _).mp hp)
    (value_below _ data entry he))

/-- Selecting the first field's subtree retains its value and matching later fields. -/
theorem subtree_fields_cons (path : ResponsePath) (name : Name)
    (field : Name × ResponseValue) (rest : List (Name × ResponseValue))
    : subtree (path ++ [.field name]) (fields path (field :: rest))
      = (if field.1 = name then value (path ++ [.field name]) field.2 else [])
        ++ subtree (path ++ [.field name]) (fields path rest) := by
  rw [fields, subtree_append]
  by_cases h : field.1 = name
  · simp [h, subtree_value]
  · rw [subtree_child_value_other path (.field name) (.field field.1)
      (by intro he; cases he; exact h rfl)]
    simp [h]

/-- An absent field name has no subtree entries, by field-list induction. -/
theorem subtree_fields_absent (path : ResponsePath) (name : Name)
    (data : List (Name × ResponseValue)) (h : name ∉ data.map Prod.fst)
    : subtree (path ++ [.field name]) (fields path data) = [] := by
  induction data with
  | nil => rfl
  | cons field rest ih =>
      rw [subtree_fields_cons]
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp [Ne.symm h.1, ih h.2]

/-- A unique field's selected subtree is exactly its value, by list induction. -/
theorem subtree_fields_member (path : ResponsePath) (name : Name) (data : ResponseValue)
    (fieldsList : List (Name × ResponseValue))
    (hn : (fieldsList.map Prod.fst).Nodup) (hm : (name, data) ∈ fieldsList)
    : subtree (path ++ [.field name]) (fields path fieldsList)
      = value (path ++ [.field name]) data := by
  induction fieldsList with
  | nil => simp at hm
  | cons field rest ih =>
      have hnd := List.nodup_cons.mp hn
      rw [subtree_fields_cons]
      rcases List.mem_cons.mp hm with rfl | hm
      · simp [subtree_fields_absent path name rest hnd.1]
      · have hne : field.1 ≠ name := by
          intro he
          exact hnd.1 (List.mem_map.mpr ⟨(name, data), hm, he.symm⟩)
        simp [hne, ih hnd.2 hm]

/-- No list entry belongs to an index before the supplied offset, by index bounds. -/
theorem subtree_items_before (path : ResponsePath) (before start : Nat)
    (h : before < start) (data : List ResponseValue)
    : subtree (path ++ [.index before]) (items path start data) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro entry he
  intro hp
  obtain ⟨index, hi, hb⟩ := items_under path start data entry he
  have heq := below_children_eq ((isPrefixOf_iff_below _ _).mp hp) hb
  cases heq
  omega

/-- Selecting the first item's subtree yields exactly its value entries. -/
theorem subtree_items_cons (path : ResponsePath) (index : Nat)
    (head : ResponseValue) (rest : List ResponseValue)
    : subtree (path ++ [.index index]) (items path index (head :: rest))
      = value (path ++ [.index index]) head := by
  simp [items, subtree_value, subtree_items_before path index (index + 1) (by omega)]

/-- An object's selected field entries form a sublist, by membership induction. -/
theorem value_sublist_fields (path : ResponsePath) (name : Name) (data : ResponseValue)
    (fieldsList : List (Name × ResponseValue)) (hm : (name, data) ∈ fieldsList)
    : (value (path ++ [.field name]) data).Sublist (fields path fieldsList) := by
  induction fieldsList with
  | nil => simp at hm
  | cons field rest ih =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.sublist_append_left _ _
      · exact (ih hm).trans (List.sublist_append_right _ _)

/-- Unique typed paths imply unique object field names; duplicate roots contradict
uniqueness. -/
theorem fields_keys_nodup (path : ResponsePath) (data : List (Name × ResponseValue))
    (hn : ((fields path data).map Prod.fst).Nodup)
    : (data.map Prod.fst).Nodup := by
  induction data with
  | nil => simp
  | cons field rest ih =>
      simp only [fields, List.map_append, List.nodup_append] at hn
      refine List.nodup_cons.mpr ⟨?_, ih hn.2.1⟩
      intro hm
      obtain ⟨other, ho, he⟩ := List.mem_map.mp hm
      have hr := (value_sublist_fields path other.1 other.2 rest ho).subset
        (root_mem_value _ other.2)
      exact hn.2.2 _ (List.mem_map.mpr ⟨_, root_mem_value _ field.2, rfl⟩)
        _ (List.mem_map.mpr ⟨_, hr, rfl⟩) (by simp [he])

/-- Only the root's own tag occurs at its path; descendant paths are strictly longer. -/
theorem value_root_atom (path : ResponsePath) (data : ResponseValue) (atom : Atom)
    (hm : (path, atom) ∈ value path data)
    : atom = rootAtom data := by
  cases data with
  | null => simpa [value, rootAtom] using hm
  | scalar text => simpa [value, rootAtom] using hm
  | object data =>
      rcases List.mem_cons.mp hm with he | hm
      · exact (Prod.mk.inj he).2
      · exact False.elim (underFields_ne (fields_under path data _ hm) rfl)
  | list data =>
      rcases List.mem_cons.mp hm with he | hm
      · exact (Prod.mk.inj he).2
      · exact False.elim (underItems_ne (items_under path 0 data _ hm) rfl)

/-- Permuting typed value entries preserves the root tag, by root membership. -/
theorem rootAtom_of_perm (path : ResponsePath) (left right : ResponseValue)
    (hp : (value path left).Perm (value path right))
    : rootAtom left = rootAtom right :=
  value_root_atom path right _ (hp.mem_iff.mp (root_mem_value path left))

/-- A field map with no typed entries is empty, since each field contributes a root. -/
theorem fields_nil_of_perm (path : ResponsePath) (data : List (Name × ResponseValue))
    (hp : ([] : List Entry).Perm (fields path data))
    : data = [] := by
  have he := List.Perm.nil_eq hp
  cases data with
  | nil => rfl
  | cons field rest =>
      have hm := List.mem_append_left (fields path rest)
        (root_mem_value (path ++ [.field field.1]) field.2)
      change _ ∈ fields path (field :: rest) at hm
      rw [← he] at hm
      simp at hm

/-- Equal object entry inventories match each field name to a corresponding subtree. -/
theorem fields_matching (path : ResponsePath) (name : Name) (data : ResponseValue)
    (rest other : List (Name × ResponseValue))
    (hp : (fields path ((name, data) :: rest)).Perm (fields path other))
    : ∃ next, (name, next) ∈ other := by
  have hm := hp.mem_iff.mp (List.mem_append_left (fields path rest)
    (root_mem_value (path ++ [.field name]) data))
  obtain ⟨otherName, hn, hb⟩ := fields_under path other _ hm
  have he := below_children_eq (below_self (path ++ [.field name])) hb
  cases he
  obtain ⟨field, hf, he⟩ := List.mem_map.mp hn
  exact ⟨field.2, he ▸ hf⟩

/-- A list with no typed entries is empty, since each item contributes a root. -/
theorem items_nil_of_perm (path : ResponsePath) (index : Nat)
    (data : List ResponseValue) (hp : ([] : List Entry).Perm (items path index data))
    : data = [] := by
  have he := List.Perm.nil_eq hp
  cases data with
  | nil => rfl
  | cons head rest =>
      have hm := List.mem_append_left (items path (index + 1) rest)
        (root_mem_value (path ++ [.index index]) head)
      change _ ∈ items path index (head :: rest) at hm
      rw [← he] at hm
      simp at hm

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
