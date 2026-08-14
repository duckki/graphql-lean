import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.GroundBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.CoercionDiff
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedValidSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.OperationBridge

/-!
Operation-level assembly for ground normal-form uniqueness.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_validNormalSelectionSets
    {schema : Schema} {left right : Operation}
    : normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hdefinitions hsem
  have hroot :
      left.rootType schema = right.rootType schema :=
    operation_rootType_eq_of_operationDefinitionValid hleftValid hrightValid
  refine ⟨?_, ?_⟩
  · cases left.operationType
    cases right.operationType
    rfl
  · intro variableValues
    let leftValues := Execution.coerceVariableValues left variableValues
    let rightValues := Execution.coerceVariableValues right variableValues
    have hvalues :
        Execution.variableValuesCoercionEquivalent leftValues rightValues :=
      Execution.coerceVariableValues_coercionEquivalent_of_variableDefinitionsEquivalent
        (Execution.variableValuesCoercionEquivalent_refl variableValues)
        hdefinitions
    have hleftSelectionValid :=
      Validation.operationDefinitionValid_selectionSetValid hleftValid
    have hrightSelectionValid :
        Validation.selectionSetValid schema right.variableDefinitions
          (left.rootType schema) right.selectionSet := by
      simpa [hroot] using
        Validation.operationDefinitionValid_selectionSetValid hrightValid
    have hleftSelectionNormal :
        selectionSetNormal schema (left.rootType schema) left.selectionSet := by
      simpa [operationNormal] using hleftNormal
    have hrightSelectionNormal :
        selectionSetNormal schema (left.rootType schema) right.selectionSet := by
      simpa [operationNormal, hroot] using hrightNormal
    have hobject :
        objectTypeNameBool schema (left.rootType schema) = true :=
      operation_root_objectTypeNameBool_of_wf_valid hschema hleftValid
    apply
      CompleteNormalization.validNormalObjectSelectionSets_semanticallyEquivalent_equalUpToReordering
        hvalues hschema hleftSelectionValid hrightSelectionValid hleftFree
        hrightFree hleftSelectionNormal hrightSelectionNormal hobject
    intro ObjectRef resolvers fuel source hsource
    rcases hsource with ⟨runtimeType, ref, hsource, hinclude⟩
    have hleftRoot :
        Execution.rootSourceAppliesBool schema left source = true := by
      simp [hsource, Execution.rootSourceAppliesBool,
        Execution.runtimeObjectType?, hinclude]
    have hrightInclude :
        schema.typeIncludesObjectBool (right.rootType schema)
          runtimeType = true := by
      simpa [hroot] using hinclude
    have hrightRoot :
        Execution.rootSourceAppliesBool schema right source = true := by
      simp [hsource, Execution.rootSourceAppliesBool,
        Execution.runtimeObjectType?, hrightInclude]
    simpa only [leftValues, rightValues, Execution.executeQueryWithFuel,
      hleftRoot, hrightRoot, if_true, Execution.executeSelectionSetAsResponse,
      Execution.executeSelectionSet, hroot] using
        hsem resolvers variableValues fuel source

end GroundTypeNormalization

end NormalForm

end GraphQL
