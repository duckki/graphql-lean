import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Statements

/-!
Response-object key facts for semantic separation.

GraphQL response semantic equivalence ignores sibling response-field order by
canonicalizing object fields. These lemmas recover response-name membership from
canonical object equality.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

namespace ResponseKeys

namespace ResponseValue

open Execution

theorem mem_map_fst_canonicalObjectFields_iff (name : Name)
    : ∀ fields : List (Name × ResponseValue),
        name ∈ (ResponseValue.canonicalObjectFields fields).map Prod.fst
        ↔ name ∈ fields.map Prod.fst
  | [] => by
      simp [ResponseValue.canonicalObjectFields]
  | (fieldName, value) :: rest => by
      simp [ResponseValue.canonicalObjectFields,
        mem_map_fst_canonicalObjectFields_iff name rest]

theorem mem_map_fst_insertObjectFieldSorted_iff
    (name : Name) (field : Name × ResponseValue)
    : ∀ fields : List (Name × ResponseValue),
        name ∈ (ResponseValue.insertObjectFieldSorted field fields).map Prod.fst
        ↔ name = field.1 ∨ name ∈ fields.map Prod.fst
  | [] => by
      simp [ResponseValue.insertObjectFieldSorted]
  | candidate :: rest => by
      by_cases hle : field.1 <= candidate.1
      · simp [ResponseValue.insertObjectFieldSorted, hle]
      · simp [ResponseValue.insertObjectFieldSorted, hle,
          mem_map_fst_insertObjectFieldSorted_iff name field rest]
        constructor
        · intro h
          rcases h with hcandidate | hfield | hrest
          · exact Or.inr (Or.inl hcandidate)
          · exact Or.inl hfield
          · exact Or.inr (Or.inr hrest)
        · intro h
          rcases h with hfield | hcandidate | hrest
          · exact Or.inr (Or.inl hfield)
          · exact Or.inl hcandidate
          · exact Or.inr (Or.inr hrest)

theorem mem_map_fst_sortObjectFieldsByName_iff (name : Name)
    : ∀ fields : List (Name × ResponseValue),
        name ∈ (ResponseValue.sortObjectFieldsByName fields).map Prod.fst
        ↔ name ∈ fields.map Prod.fst
  | [] => by
      simp [ResponseValue.sortObjectFieldsByName]
  | field :: rest => by
      simp [ResponseValue.sortObjectFieldsByName,
        mem_map_fst_insertObjectFieldSorted_iff name field
          (ResponseValue.sortObjectFieldsByName rest),
        mem_map_fst_sortObjectFieldsByName_iff name rest]

theorem mem_insertObjectFieldSorted_iff
    (field candidate : Name × ResponseValue)
    (fields : List (Name × ResponseValue))
    : candidate ∈ ResponseValue.insertObjectFieldSorted field fields
      ↔ candidate = field ∨ candidate ∈ fields := by
  induction fields with
  | nil =>
      simp [ResponseValue.insertObjectFieldSorted]
  | cons head rest ih =>
      by_cases hle : field.1 <= head.1
      · simp [ResponseValue.insertObjectFieldSorted, hle]
      · simp [ResponseValue.insertObjectFieldSorted, hle, ih, or_left_comm]

theorem mem_sortObjectFieldsByName_iff
    (fields : List (Name × ResponseValue))
    (candidate : Name × ResponseValue)
    : candidate ∈ ResponseValue.sortObjectFieldsByName fields ↔ candidate ∈ fields := by
  induction fields with
  | nil =>
      simp [ResponseValue.sortObjectFieldsByName]
  | cons field rest ih =>
      simp [ResponseValue.sortObjectFieldsByName,
        mem_insertObjectFieldSorted_iff, ih]

theorem canonicalObjectFields_map_fst (fields : List (Name × ResponseValue))
    : (ResponseValue.canonicalObjectFields fields).map Prod.fst
      = fields.map Prod.fst := by
  induction fields with
  | nil =>
      simp [ResponseValue.canonicalObjectFields]
  | cons field rest ih =>
      simp [ResponseValue.canonicalObjectFields, ih]

theorem canonicalObjectFields_mem
    {fields : List (Name × ResponseValue)} {name : Name}
    {value : ResponseValue}
    : (name, value) ∈ fields
      -> (name, ResponseValue.canonical value)
          ∈ ResponseValue.canonicalObjectFields fields := by
  intro hmem
  induction fields with
  | nil =>
      simp at hmem
  | cons field rest ih =>
      rcases field with ⟨fieldName, fieldValue⟩
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp [ResponseValue.canonicalObjectFields]
      · exact List.mem_cons_of_mem _ (ih htail)

theorem canonicalObjectFields_nodup (fields : List (Name × ResponseValue))
    : (fields.map Prod.fst).Nodup
      -> ((ResponseValue.canonicalObjectFields fields).map Prod.fst).Nodup := by
  intro hnodup
  simpa [canonicalObjectFields_map_fst] using hnodup

theorem insertObjectFieldSorted_nodup
    (field : Name × ResponseValue) (fields : List (Name × ResponseValue))
    : field.1 ∉ fields.map Prod.fst
      -> (fields.map Prod.fst).Nodup
      -> ((ResponseValue.insertObjectFieldSorted field fields).map Prod.fst).Nodup := by
  induction fields with
  | nil =>
      intro _hnot _hnodup
      simp [ResponseValue.insertObjectFieldSorted]
  | cons head rest ih =>
      intro hnot hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hheadNotRest, hrestNodup⟩
      have hfieldNeHead : field.1 ≠ head.1 := by
        intro heq
        exact hnot (by simp [heq])
      have hfieldNotRest : field.1 ∉ rest.map Prod.fst := by
        intro hmem
        exact hnot (by simp [hmem])
      by_cases hle : field.1 <= head.1
      · simpa [ResponseValue.insertObjectFieldSorted, hle] using
          List.nodup_cons.mpr ⟨hnot, hnodup⟩
      · have hinsertRestNodup :
            ((ResponseValue.insertObjectFieldSorted field rest).map
              Prod.fst).Nodup :=
          ih hfieldNotRest hrestNodup
        have hheadNotInsert :
            head.1 ∉
              (ResponseValue.insertObjectFieldSorted field rest).map
                Prod.fst := by
          intro hmem
          have hmem' :
              head.1 = field.1 ∨ head.1 ∈ rest.map Prod.fst := by
            simpa [mem_map_fst_insertObjectFieldSorted_iff] using hmem
          rcases hmem' with heq | hrest
          · exact hfieldNeHead heq.symm
          · exact hheadNotRest hrest
        simp [ResponseValue.insertObjectFieldSorted, hle, hheadNotInsert,
          hinsertRestNodup]

theorem sortObjectFieldsByName_nodup (fields : List (Name × ResponseValue))
    : (fields.map Prod.fst).Nodup
      -> ((ResponseValue.sortObjectFieldsByName fields).map Prod.fst).Nodup := by
  induction fields with
  | nil =>
      intro _hnodup
      simp [ResponseValue.sortObjectFieldsByName]
  | cons field rest ih =>
      intro hnodup
      rcases List.nodup_cons.mp hnodup with ⟨hfieldNotRest, hrestNodup⟩
      have hsortRestNodup :
          ((ResponseValue.sortObjectFieldsByName rest).map Prod.fst).Nodup :=
        ih hrestNodup
      have hfieldNotSortRest :
          field.1 ∉ (ResponseValue.sortObjectFieldsByName rest).map
            Prod.fst := by
        intro hmem
        exact hfieldNotRest
          ((mem_map_fst_sortObjectFieldsByName_iff field.1 rest).mp hmem)
      exact
        insertObjectFieldSorted_nodup field
          (ResponseValue.sortObjectFieldsByName rest)
          hfieldNotSortRest hsortRestNodup

theorem find?_eq_some_of_mem_nodup
    {fields : List (Name × ResponseValue)} {name : Name}
    {value : ResponseValue}
    : (name, value) ∈ fields
      -> (fields.map Prod.fst).Nodup
      -> fields.find? (fun field => field.1 == name) = some (name, value) := by
  intro hmem hnodup
  induction fields with
  | nil =>
      simp at hmem
  | cons field rest ih =>
      rcases field with ⟨fieldName, fieldValue⟩
      rcases List.nodup_cons.mp hnodup with ⟨hfieldNotRest, hrestNodup⟩
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp
      · have hnameInRest : name ∈ rest.map Prod.fst := by
          exact List.mem_map.mpr ⟨(name, value), htail, rfl⟩
        have hfieldNe : fieldName ≠ name := by
          intro heq
          exact hfieldNotRest (by simpa [heq] using hnameInRest)
        simp [hfieldNe, ih htail hrestNodup]

theorem sort_canonicalObjectFields_find?_eq_some
    {fields : List (Name × ResponseValue)} {name : Name}
    {value : ResponseValue}
    : (name, value) ∈ fields
      -> (fields.map Prod.fst).Nodup
      -> (ResponseValue.sortObjectFieldsByName
            (ResponseValue.canonicalObjectFields fields)).find?
            (fun field => field.1 == name)
          = some (name, ResponseValue.canonical value) := by
  intro hmem hnodup
  have hcanonicalMem :
      (name, ResponseValue.canonical value) ∈
        ResponseValue.canonicalObjectFields fields :=
    canonicalObjectFields_mem hmem
  have hsortedMem :
      (name, ResponseValue.canonical value) ∈
        ResponseValue.sortObjectFieldsByName
          (ResponseValue.canonicalObjectFields fields) := by
    exact (mem_sortObjectFieldsByName_iff
      (ResponseValue.canonicalObjectFields fields)
      (name, ResponseValue.canonical value)).mpr hcanonicalMem
  have hsortedNodup :
      (((ResponseValue.sortObjectFieldsByName
          (ResponseValue.canonicalObjectFields fields)).map Prod.fst)).Nodup :=
    sortObjectFieldsByName_nodup (ResponseValue.canonicalObjectFields fields)
      (canonicalObjectFields_nodup fields hnodup)
  exact find?_eq_some_of_mem_nodup hsortedMem hsortedNodup

theorem canonical_object_eq_mem_fst_iff
    {left right : List (Name × ResponseValue)} {name : Name}
    : ResponseValue.canonical (.object left) = ResponseValue.canonical (.object right)
      -> (name ∈ left.map Prod.fst ↔ name ∈ right.map Prod.fst) := by
  intro heq
  unfold ResponseValue.canonical at heq
  injection heq with hfields
  constructor
  · intro hleft
    have hleftCanonical :
        name ∈
          (ResponseValue.sortObjectFieldsByName
            (ResponseValue.canonicalObjectFields left)).map Prod.fst := by
      simpa [mem_map_fst_sortObjectFieldsByName_iff,
        mem_map_fst_canonicalObjectFields_iff] using hleft
    have hrightCanonical :
        name ∈
          (ResponseValue.sortObjectFieldsByName
            (ResponseValue.canonicalObjectFields right)).map Prod.fst := by
      simpa [hfields] using hleftCanonical
    simpa [mem_map_fst_sortObjectFieldsByName_iff,
      mem_map_fst_canonicalObjectFields_iff] using hrightCanonical
  · intro hright
    have hrightCanonical :
        name ∈
          (ResponseValue.sortObjectFieldsByName
            (ResponseValue.canonicalObjectFields right)).map Prod.fst := by
      simpa [mem_map_fst_sortObjectFieldsByName_iff,
        mem_map_fst_canonicalObjectFields_iff] using hright
    have hleftCanonical :
        name ∈
          (ResponseValue.sortObjectFieldsByName
            (ResponseValue.canonicalObjectFields left)).map Prod.fst := by
      simpa [hfields] using hrightCanonical
    simpa [mem_map_fst_sortObjectFieldsByName_iff,
      mem_map_fst_canonicalObjectFields_iff] using hleftCanonical

theorem semanticEquivalent_object_mem_fst_iff
    {left right : List (Name × ResponseValue)} {name : Name}
    : ResponseValue.semanticEquivalent (.object left) (.object right)
      -> (name ∈ left.map Prod.fst ↔ name ∈ right.map Prod.fst) := by
  intro hsem
  exact canonical_object_eq_mem_fst_iff hsem

theorem semanticEquivalent_object_field_canonical_eq
    {left right : List (Name × ResponseValue)} {name : Name}
    {leftValue rightValue : ResponseValue}
    : ResponseValue.semanticEquivalent (.object left) (.object right)
      -> (left.map Prod.fst).Nodup
      -> (right.map Prod.fst).Nodup
      -> (name, leftValue) ∈ left
      -> (name, rightValue) ∈ right
      -> ResponseValue.canonical leftValue = ResponseValue.canonical rightValue := by
  intro hsemantic hleftNodup hrightNodup hleftMem hrightMem
  have hfields :
      ResponseValue.sortObjectFieldsByName
          (ResponseValue.canonicalObjectFields left)
        =
      ResponseValue.sortObjectFieldsByName
          (ResponseValue.canonicalObjectFields right) := by
    simpa [ResponseValue.semanticEquivalent, ResponseValue.canonical] using
      hsemantic
  have hleftFind :
      (ResponseValue.sortObjectFieldsByName
          (ResponseValue.canonicalObjectFields left)).find?
          (fun field => field.1 == name)
        =
      some (name, ResponseValue.canonical leftValue) :=
    sort_canonicalObjectFields_find?_eq_some hleftMem hleftNodup
  have hrightFind :
      (ResponseValue.sortObjectFieldsByName
          (ResponseValue.canonicalObjectFields right)).find?
          (fun field => field.1 == name)
        =
      some (name, ResponseValue.canonical rightValue) :=
    sort_canonicalObjectFields_find?_eq_some hrightMem hrightNodup
  have hfindEq :
      some (name, ResponseValue.canonical leftValue) =
        some (name, ResponseValue.canonical rightValue) := by
    calc
      some (name, ResponseValue.canonical leftValue)
          = (ResponseValue.sortObjectFieldsByName
              (ResponseValue.canonicalObjectFields left)).find?
              (fun field => field.1 == name) :=
        hleftFind.symm
      _ = (ResponseValue.sortObjectFieldsByName
            (ResponseValue.canonicalObjectFields right)).find?
            (fun field => field.1 == name) := by
        rw [hfields]
      _ = some (name, ResponseValue.canonical rightValue) := hrightFind
  have hpair :
      (name, ResponseValue.canonical leftValue) =
        (name, ResponseValue.canonical rightValue) :=
    Option.some.inj hfindEq
  exact congrArg Prod.snd hpair

end ResponseValue

theorem response_semanticEquivalent_object_mem_fst_iff
    {left right : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    : Execution.Response.semanticEquivalent
        ({ data := .object left, errors := leftErrors } : Execution.Response)
        ({ data := .object right, errors := rightErrors } : Execution.Response)
      -> (name ∈ left.map Prod.fst ↔ name ∈ right.map Prod.fst) := by
  intro hsem
  exact ResponseValue.semanticEquivalent_object_mem_fst_iff hsem.1

theorem response_semanticEquivalent_object_field_canonical_eq
    {left right : List (Name × Execution.ResponseValue)}
    {leftErrors rightErrors : Nat} {name : Name}
    {leftValue rightValue : Execution.ResponseValue}
    : Execution.Response.semanticEquivalent
        ({ data := .object left, errors := leftErrors } : Execution.Response)
        ({ data := .object right, errors := rightErrors } : Execution.Response)
      -> (left.map Prod.fst).Nodup
      -> (right.map Prod.fst).Nodup
      -> (name, leftValue) ∈ left
      -> (name, rightValue) ∈ right
      -> Execution.ResponseValue.semanticEquivalent leftValue rightValue := by
  intro hsem hleftNodup hrightNodup hleftMem hrightMem
  exact ResponseValue.semanticEquivalent_object_field_canonical_eq hsem.1
    hleftNodup hrightNodup hleftMem hrightMem

end ResponseKeys

end GroundTypeNormalization

end NormalForm

end GraphQL
