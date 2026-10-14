import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.Execution

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.QueryInclusion

open Execution
universe u v

mutual
  theorem collectFields_object_ref_irrelevant
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name) (leftRef : α) (rightRef : β)
      (selectionSet : List Selection)
      : collectFields schema variableValues parentType (.object runtimeType leftRef)
          selectionSet
        = collectFields schema variableValues parentType (.object runtimeType rightRef)
            selectionSet := by
    cases selectionSet with
    | nil => rfl
    | cons selection rest =>
        simp only [collectFields]
        rw [collectSelection_object_ref_irrelevant schema variableValues parentType
          runtimeType leftRef rightRef selection]
        rw [collectFields_object_ref_irrelevant schema variableValues parentType
          runtimeType leftRef rightRef rest]

  theorem collectSelection_object_ref_irrelevant
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name) (leftRef : α) (rightRef : β)
      (selection : Selection)
      : collectSelection schema variableValues parentType (.object runtimeType leftRef)
          selection
        = collectSelection schema variableValues parentType (.object runtimeType rightRef)
            selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rfl
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            simp only [collectSelection]
            split
            · exact collectFields_object_ref_irrelevant schema variableValues parentType
                runtimeType leftRef rightRef selectionSet
            · rfl
        | some typeName =>
            simp only [collectSelection, doesFragmentTypeApplyBool, runtimeObjectType?]
            split
            · by_cases happlies :
                  schema.typeIncludesObjectBool typeName runtimeType = true
              · simp only [happlies, ↓reduceIte]
                exact collectFields_object_ref_irrelevant schema variableValues parentType
                  runtimeType leftRef rightRef selectionSet
              · simp [happlies]
            · rfl
end

theorem collectRuntimeFieldGroups_eq_collectFields_object
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (ref : ObjectRef)
    (selectionSet : List Selection)
    : collectRuntimeFieldGroups schema variableValues parentType runtimeType selectionSet
      = collectFields schema variableValues parentType (.object runtimeType ref)
          selectionSet := by
  exact collectFields_object_ref_irrelevant schema variableValues parentType runtimeType
    PUnit.unit ref selectionSet

theorem executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet
    (fields : List ExecutableField)
    : executableFieldsMergedSelectionSet fields = mergedFieldSelectionSet fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      change field.selectionSet ++ executableFieldsMergedSelectionSet rest
        = field.selectionSet ++ mergedFieldSelectionSet rest
      rw [ih]

end GraphQL.QueryInclusion
