import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Theories.QueryInclusion.Support.Validation.FieldMerge

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.FieldMerge

theorem collectFields_mem_mergedFieldSelectionSet (schema : Schema) (objectType : Name)
    : ∀ {fields : List Execution.ExecutableField} {scopedField : ScopedField},
        scopedField
          ∈ collectFields schema objectType (Execution.mergedFieldSelectionSet fields)
        -> ∃ field,
            field ∈ fields
            ∧ scopedField ∈ collectFields schema objectType field.selectionSet
  | [], scopedField, hscoped => by
      simp [Execution.mergedFieldSelectionSet, collectFields] at hscoped
  | field :: rest, scopedField, hscoped => by
      rw [Execution.mergedFieldSelectionSet_cons] at hscoped
      rw [collectFields_append] at hscoped
      rcases List.mem_append.mp hscoped with hhead | htail
      · exact ⟨field, by simp, hhead⟩
      · rcases collectFields_mem_mergedFieldSelectionSet schema objectType
            htail with
          ⟨tailField, htailField, htailScoped⟩
        exact ⟨tailField, by simp [htailField], htailScoped⟩

theorem fieldsInSetCanMerge_pair_subfields
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    (left right : ScopedField)
    : fieldsInSetCanMerge schema parentType selectionSet
      -> left ∈ collectFields schema parentType selectionSet
      -> right ∈ collectFields schema parentType selectionSet
      -> left.responseName = right.responseName
      -> (left.parentType = right.parentType
          ∨ ¬ schema.objectType left.parentType
          ∨ ¬ schema.objectType right.parentType)
      -> ∀ objectType,
          fieldsInSetCanMerge schema objectType
            (left.selectionSet ++ right.selectionSet) := by
  intro hmerge hleft hright hresponse hparents
  exact fieldsForNameCanMerge_subfields
    (fieldsInSetCanMerge_pair hmerge hleft hright hresponse) hparents

theorem fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise
    (schema : Schema) (objectType : Name)
    (fields : List Execution.ExecutableField)
    : (∀ first,
        first ∈ fields
        -> ∀ later,
            later ∈ fields
            -> fieldsInSetCanMerge schema objectType
                (first.selectionSet ++ later.selectionSet))
      -> fieldsInSetCanMerge schema objectType
          (Execution.mergedFieldSelectionSet fields) := by
  intro hpairwise
  unfold fieldsInSetCanMerge
  refine FieldsInSetCanMerge.intro objectType
    (Execution.mergedFieldSelectionSet fields) ?_
  dsimp
  intro left hleft right hright hresponse
  rcases collectFields_mem_mergedFieldSelectionSet schema objectType hleft
    with ⟨first, hfirst, hleftScoped⟩
  rcases collectFields_mem_mergedFieldSelectionSet schema objectType hright
    with ⟨later, hlater, hrightScoped⟩
  have hleftAppend :
      left ∈ collectFields schema objectType
        (first.selectionSet ++ later.selectionSet) := by
    rw [collectFields_append]
    exact List.mem_append.mpr (Or.inl hleftScoped)
  have hrightAppend :
      right ∈ collectFields schema objectType
        (first.selectionSet ++ later.selectionSet) := by
    rw [collectFields_append]
    exact List.mem_append.mpr (Or.inr hrightScoped)
  exact fieldsInSetCanMerge_pair
    (hpairwise first hfirst later hlater) hleftAppend hrightAppend hresponse

end GraphQL.FieldMerge
