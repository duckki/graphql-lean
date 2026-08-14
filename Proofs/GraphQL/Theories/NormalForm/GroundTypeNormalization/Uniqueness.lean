import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedOperationBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedValidSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.NormalizeBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ReorderingSoundness
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.ArgumentNodup

/-!
Ground-type normal-form uniqueness theorem surface.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

private theorem
    normal_operations_equalUpToReordering_semanticallyEquivalent_of_argumentsNodup
    {schema : Schema} {left right : Operation}
    (hrootObject : objectTypeNameBool schema (left.rootType schema) = true)
    (hleftArgumentsNodup : Execution.selectionSetArgumentsNodup left.selectionSet)
    (hrightArgumentsNodup : Execution.selectionSetArgumentsNodup right.selectionSet)
    (hleftFree : operationDirectiveFree left)
    (hrightFree : operationDirectiveFree right)
    (hleftNormal : operationNormal schema left)
    (hrightNormal : operationNormal schema right)
    (hdefinitions
      : variableDefinitionsEquivalent left.variableDefinitions right.variableDefinitions)
    (hequal : operationsEqualUpToReorderingWithCoercion schema left right)
    : operationsSemanticallyEquivalent schema left right := by
  rcases hequal with ⟨_hroot, hselectionEqual⟩
  have hrootType : (left.rootType schema) = (right.rootType schema) := by
    cases left.operationType
    cases right.operationType
    rfl
  have hrightSelectionNormal :
    selectionSetNormal schema (left.rootType schema) right.selectionSet := by
    simpa [operationNormal, hrootType] using hrightNormal
  intro ObjectRef resolvers variableValues fuel source
  have hrootApplies :
      Execution.rootSourceAppliesBool schema left source =
        Execution.rootSourceAppliesBool schema right source := by
    simp [Execution.rootSourceAppliesBool, hrootType]
  cases hleftRoot : Execution.rootSourceAppliesBool schema left source with
  | false =>
      have hrightRoot :
          Execution.rootSourceAppliesBool schema right source = false := by
        simpa [hleftRoot] using hrootApplies.symm
      simp [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
        Execution.Response.semanticEquivalent,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical]
  | true =>
      have hrightRoot :
          Execution.rootSourceAppliesBool schema right source = true := by
        simpa [hleftRoot] using hrootApplies.symm
      have hsource :=
        rootSourceAppliesBool_true_object schema left source hleftRoot
      have heffectiveValues :
          Execution.variableValuesCoercionEquivalent
            (Execution.coerceVariableValues left variableValues)
            (Execution.coerceVariableValues right variableValues) :=
        Execution.coerceVariableValues_coercionEquivalent_of_variableDefinitionsEquivalent
          (Execution.variableValuesCoercionEquivalent_refl variableValues)
          hdefinitions
      have hselectionEqualSame :=
        selectionSetEqualUpToReorderingWithCoercion_right_to_left heffectiveValues
          (hselectionEqual variableValues)
      have hselectionResponse :=
        selectionSetsSemanticallyEquivalent_of_equalUpToReordering
          hleftArgumentsNodup hrightArgumentsNodup
          hleftFree hrightFree hleftNormal hrightSelectionNormal hrootObject
          hselectionEqualSame resolvers fuel source hsource
      have hrightExecution :
          Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues left variableValues) fuel
              (left.rootType schema) source right.selectionSet
            =
          Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues right variableValues) fuel
              (left.rootType schema) source right.selectionSet := by
        unfold Execution.executeSelectionSetAsResponse
        rw [CompleteNormalization.executeSelectionSet_eq_of_variableValuesCoercionEquivalent
          schema resolvers heffectiveValues fuel (left.rootType schema) source
          right.selectionSet]
      have hselectionResponse' :
          Execution.Response.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues left variableValues) fuel
              (left.rootType schema) source left.selectionSet)
            (Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues right variableValues) fuel
              (left.rootType schema) source right.selectionSet) := by
        rw [← hrightExecution]
        exact hselectionResponse
      simpa [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
        Execution.executeSelectionSetAsResponse,
        Execution.executeSelectionSet, hrootType] using
          hselectionResponse'

theorem normal_operations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : normalOperationsEqualUpToReorderingSemanticallyEquivalent schema left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hleftNormal hrightNormal
    hdefinitions hequal
  exact
    normal_operations_equalUpToReordering_semanticallyEquivalent_of_argumentsNodup
      (operation_root_objectTypeNameBool_of_wf_valid hschema hleftValid)
      (Execution.selectionSetArgumentsNodup_of_selectionSetValid
        (Validation.operationDefinitionValid_selectionSetValid hleftValid))
      (Execution.selectionSetArgumentsNodup_of_selectionSetValid
        (Validation.operationDefinitionValid_selectionSetValid hrightValid))
      hleftFree hrightFree hleftNormal hrightNormal hdefinitions hequal

theorem normalizeOperations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : normalizeOperationsEqualUpToReorderingSemanticallyEquivalent schema left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hdefinitions hequal
  have hleftNormalizedFree :
      operationDirectiveFree (normalizeOperation schema left) :=
    normalizeOperation_directiveFree schema left hleftFree
  have hrightNormalizedFree :
      operationDirectiveFree (normalizeOperation schema right) :=
    normalizeOperation_directiveFree schema right hrightFree
  have hleftNormalizedNormal :
      operationNormal schema (normalizeOperation schema left) := by
    simpa [normalizeOperationNormal] using
      normalizeOperation_normal schema left hschema hleftValid
  have hrightNormalizedNormal :
      operationNormal schema (normalizeOperation schema right) := by
    simpa [normalizeOperationNormal] using
      normalizeOperation_normal schema right hschema hrightValid
  have hnormalizedDefinitions :
      variableDefinitionsEquivalent
        (normalizeOperation schema left).variableDefinitions
        (normalizeOperation schema right).variableDefinitions := by
    simpa [normalizeOperation_variableDefinitions] using hdefinitions
  have hnormalizedSemantics :
      operationsSemanticallyEquivalent schema
        (normalizeOperation schema left)
        (normalizeOperation schema right) :=
    normal_operations_equalUpToReordering_semanticallyEquivalent_of_argumentsNodup
      (by
        simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
          operation_root_objectTypeNameBool_of_wf_valid hschema hleftValid)
      (normalizeOperation_selectionSetArgumentsNodup schema left
        (Execution.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hleftValid)))
      (normalizeOperation_selectionSetArgumentsNodup schema right
        (Execution.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hrightValid)))
      hleftNormalizedFree hrightNormalizedFree hleftNormalizedNormal
      hrightNormalizedNormal hnormalizedDefinitions hequal
  have hleftEquivalent :
      operationsEquivalent schema left (normalizeOperation schema left) :=
    groundTypeNormalFormSemanticsPreservation schema left hschema hleftValid
      hleftFree
  have hrightEquivalent :
      operationsEquivalent schema right (normalizeOperation schema right) :=
    groundTypeNormalFormSemanticsPreservation schema right hschema hrightValid
      hrightFree
  intro ObjectRef resolvers variableValues fuel source
  have hleftResponse :=
    hleftEquivalent resolvers variableValues fuel source
  have hrightResponse :=
    hrightEquivalent resolvers variableValues fuel source
  simpa [hleftResponse, hrightResponse] using
    hnormalizedSemantics resolvers variableValues fuel source

theorem normal_operations_semanticallyEquivalent_equalUpToReordering
    {schema : Schema} {left right : Operation}
    : normalOperationsSemanticallyEquivalentEqualUpToReordering schema left right := by
  exact
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_validNormalSelectionSets

theorem normalizeOperation_uniqueUpToReordering {schema : Schema} {left right : Operation}
    : normalizeOperationUniqueUpToReordering schema left right := by
  exact
    normalizeOperation_uniqueUpToReordering_of_normal_operations
      (normal_operations_semanticallyEquivalent_equalUpToReordering
        (schema := schema) (left := normalizeOperation schema left)
        (right := normalizeOperation schema right))

end GroundTypeNormalization

end NormalForm

end GraphQL
