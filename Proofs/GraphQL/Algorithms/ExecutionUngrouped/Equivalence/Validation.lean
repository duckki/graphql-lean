import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Validation.FieldMerge
import Proofs.GraphQL.Validation.SelectionValidity

/-!
Validation and field-merge compatibility lemmas for the ungrouped equivalence proof.
-/

namespace GraphQL

namespace Validation

theorem selectionSetValid_singleton
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name) (selection : Selection)
    : selectionValid schema variableDefinitions parentType selection
      -> selectionSetValid schema variableDefinitions parentType [selection] := by
  intro hvalid
  unfold selectionSetValid
  intro candidate hmem
  simp at hmem
  subst candidate
  exact hvalid

theorem selectionValid_field_selectionSetValid_of_lookup_nonempty
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet : List Selection) (fieldDefinition : FieldDefinition)
    : selectionValid schema variableDefinitions parentType
        (.field responseName fieldName arguments directives selectionSet)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> selectionSet ≠ []
      -> selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType selectionSet := by
  intro hvalid hlookup hnonempty
  simp [selectionValid] at hvalid
  rcases hvalid with
    ⟨_hdirectives, candidate, hcandidateLookup, _harguments,
      hselectionSet⟩
  rw [hlookup] at hcandidateLookup
  cases hcandidateLookup
  unfold fieldSelectionSetValid at hselectionSet
  rcases hselectionSet with ⟨_houtput, hshape⟩
  rcases hshape with hleaf | hcomposite
  · exact False.elim (hnonempty hleaf.2)
  · exact hcomposite.2.2

theorem fieldSelectionSetValid_selectionSetValid
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (fieldDefinition : FieldDefinition) (selectionSet : List Selection)
    : fieldSelectionSetValid schema variableDefinitions fieldDefinition selectionSet
      -> selectionSetValid schema variableDefinitions
          fieldDefinition.outputType.namedType selectionSet := by
  intro hvalid
  unfold fieldSelectionSetValid at hvalid
  rcases hvalid with ⟨_houtput, hshape⟩
  rcases hshape with hleaf | hcomposite
  · rw [hleaf.2]
    unfold selectionSetValid
    intro selection hselection
    simp at hselection
  · exact hcomposite.2.2

theorem selectionSetValid_mergedFieldSelectionSet
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    : ∀ fields : List Execution.ExecutableField,
        (∀ field,
          field ∈ fields
          -> selectionSetValid schema variableDefinitions parentType field.selectionSet)
        -> selectionSetValid schema variableDefinitions parentType
            (Execution.mergedFieldSelectionSet fields)
  | [], _hvalid => by
      simp [Execution.mergedFieldSelectionSet, selectionSetValid]
  | field :: rest, hvalid => by
      have hfield :
          selectionSetValid schema variableDefinitions parentType
            field.selectionSet :=
        hvalid field (by simp)
      have hrest :
          selectionSetValid schema variableDefinitions parentType
            (Execution.mergedFieldSelectionSet rest) :=
        selectionSetValid_mergedFieldSelectionSet schema variableDefinitions
          parentType rest
          (by
            intro candidate hcandidate
            exact hvalid candidate (by simp [hcandidate]))
      simpa [Execution.mergedFieldSelectionSet] using
        Validation.selectionSetValid_append hfield hrest

theorem selectionSetValid_mergedFieldSelectionSet_cons
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    (parentType : Name)
    (field : Execution.ExecutableField)
    (fields : List Execution.ExecutableField)
    : selectionSetValid schema variableDefinitions parentType field.selectionSet
      -> (∀ candidate,
            candidate ∈ fields
            -> selectionSetValid schema variableDefinitions parentType
                candidate.selectionSet)
      -> selectionSetValid schema variableDefinitions parentType
          (Execution.mergedFieldSelectionSet (field :: fields)) := by
  intro hfield hfields
  exact
    selectionSetValid_mergedFieldSelectionSet schema variableDefinitions
      parentType (field :: fields)
      (by
        intro candidate hcandidate
        rcases List.mem_cons.mp hcandidate with hhead | htail
        · subst candidate
          exact hfield
        · exact hfields candidate htail)

end Validation

namespace FieldMerge

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

theorem collectFields_mergedFieldSelectionSet_mem_of_field_mem
    (schema : Schema) (objectType : Name)
    : ∀ {fields : List Execution.ExecutableField}
        {field : Execution.ExecutableField}
        {scopedField : ScopedField},
        field ∈ fields
        -> scopedField ∈ collectFields schema objectType field.selectionSet
        -> scopedField
            ∈ collectFields schema objectType (Execution.mergedFieldSelectionSet fields)
  | [], field, scopedField, hfield, _hscoped => by
      simp at hfield
  | head :: rest, field, scopedField, hfield, hscoped => by
      rcases List.mem_cons.mp hfield with hhead | hrest
      · subst head
        rw [Execution.mergedFieldSelectionSet_cons]
        rw [collectFields_append]
        exact List.mem_append.mpr (Or.inl hscoped)
      · rw [Execution.mergedFieldSelectionSet_cons]
        rw [collectFields_append]
        exact List.mem_append.mpr
          (Or.inr
            (collectFields_mergedFieldSelectionSet_mem_of_field_mem schema
              objectType hrest hscoped))

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

theorem fieldsInSetCanMerge_mono
    (schema : Schema) (parentType : Name)
    (sourceSelectionSet targetSelectionSet : List Selection)
    : fieldsInSetCanMerge schema parentType targetSelectionSet
      -> (∀ scopedField,
            scopedField ∈ collectFields schema parentType sourceSelectionSet
            -> scopedField ∈ collectFields schema parentType targetSelectionSet)
      -> fieldsInSetCanMerge schema parentType sourceSelectionSet := by
  intro hmerge hsubset
  unfold fieldsInSetCanMerge
  refine FieldsInSetCanMerge.intro parentType sourceSelectionSet ?_
  dsimp
  intro left hleft right hright hresponse
  exact fieldsInSetCanMerge_pair hmerge
    (hsubset left hleft) (hsubset right hright) hresponse

theorem fieldsInSetCanMerge_append_left
    (schema : Schema) (parentType : Name)
    (left right : List Selection)
    : fieldsInSetCanMerge schema parentType (left ++ right)
      -> fieldsInSetCanMerge schema parentType left := by
  intro hmerge
  exact fieldsInSetCanMerge_mono schema parentType left (left ++ right)
    hmerge
    (by
      intro scopedField hscoped
      rw [collectFields_append]
      exact List.mem_append.mpr (Or.inl hscoped))

theorem fieldsInSetCanMerge_self_subfields
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    (scopedField : ScopedField)
    : fieldsInSetCanMerge schema parentType selectionSet
      -> scopedField ∈ collectFields schema parentType selectionSet
      -> ∀ objectType,
          fieldsInSetCanMerge schema objectType scopedField.selectionSet := by
  intro hmerge hscoped objectType
  exact fieldsInSetCanMerge_append_left schema objectType
    scopedField.selectionSet scopedField.selectionSet
    (fieldsInSetCanMerge_pair_subfields schema parentType selectionSet
      scopedField scopedField hmerge hscoped hscoped rfl (Or.inl rfl)
      objectType)

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

end FieldMerge

end GraphQL
