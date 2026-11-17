import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Semantics.Final
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity

/-! Ungrouped-execution corollaries requiring normalizer validity preservation. -/

namespace GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

open GraphQL.Execution

variable {ObjectRef : Type}

theorem completeNormalizationPreservesUngroupedExecution_of_normalizeOperation
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationFieldsValidInPossibleTypes schema operation
      -> NormalForm.operationFieldsSameOutputShape schema operation
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> Validation.operationVariablesUsed
          (NormalForm.normalizeOperation schema operation)
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.normalizeOperation schema operation) depth source
          = executeQueryWithFuel schema resolvers variableValues
              (NormalForm.completeNormalizeOperation schema
                (NormalForm.normalizeOperation schema operation)) depth source := by
  intro hschema hvalid hfields hshapes hfree hfeasibleAll hvariablesUsed
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid_of_operationFieldsValid schema
      operation hschema hvalid hfields hshapes hfree hfeasibleAll hvariablesUsed
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  apply completeNormalizationPreservesUngroupedExecution_of_source_eq_spec
    schema (NormalForm.normalizeOperation schema operation) resolvers
    variableValues depth source hschema hnormalizedValid
    (NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation)
      (Execution.coerceVariableValues
        (NormalForm.normalizeOperation schema operation) variableValues)
      hnormalizedFree)
  exact executeQueryWithFuel_normalizeOperation_eq_spec schema operation
    resolvers variableValues depth source hschema hvalid hfree

theorem normalizeThenCompleteUngroupedExecution_semanticsPreserved
    (schema : Schema) (operation : Operation)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> NormalForm.operationFieldsValidInPossibleTypes schema operation
      -> NormalForm.operationFieldsSameOutputShape schema operation
      -> NormalForm.operationDirectiveFree operation
      -> NormalForm.selectionSetsTypeConditionFeasibleInEveryNormalizerScope schema
      -> Validation.operationVariablesUsed
          (NormalForm.normalizeOperation schema operation)
      -> executeQueryWithFuel schema resolvers variableValues
            (NormalForm.completeNormalizeOperation schema
              (NormalForm.normalizeOperation schema operation)) depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues operation
              depth source := by
  intro hschema hvalid hfields hshapes hfree hfeasibleAll hvariablesUsed
  have hnormalizedValid :
      Validation.operationDefinitionValid schema
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_valid_of_operationFieldsValid schema
      operation hschema hvalid hfields hshapes hfree hfeasibleAll hvariablesUsed
  have hnormalizedFree :
      NormalForm.operationDirectiveFree
        (NormalForm.normalizeOperation schema operation) :=
    NormalForm.GroundTypeNormalization.normalizeOperation_directiveFree schema
      operation hfree
  have hcomplete :
      operationBoolVarsComplete
        (NormalForm.normalizeOperation schema operation)
        (Execution.coerceVariableValues
          (NormalForm.normalizeOperation schema operation) variableValues) :=
    NormalForm.CompleteNormalization.operationBoolVarsComplete_of_operationDirectiveFree
      (NormalForm.normalizeOperation schema operation)
      (Execution.coerceVariableValues
        (NormalForm.normalizeOperation schema operation) variableValues)
      hnormalizedFree
  have hcompleteUngrouped :
      executeQueryWithFuel schema resolvers variableValues
          (NormalForm.completeNormalizeOperation schema
            (NormalForm.normalizeOperation schema operation)) depth source
        =
      Execution.executeQueryWithFuel schema resolvers variableValues
        (NormalForm.normalizeOperation schema operation) depth source :=
    executeQueryWithFuel_completeNormalizeOperation_semanticsPreserved schema
      (NormalForm.normalizeOperation schema operation) resolvers
      variableValues depth source hschema hnormalizedValid hcomplete
  have hgroundSpec
      : Execution.executeQueryWithFuel schema resolvers variableValues operation
          depth source
        = Execution.executeQueryWithFuel schema resolvers variableValues
            (NormalForm.normalizeOperation schema operation) depth source := by
    exact
      NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation
        schema operation hschema hvalid hfree resolvers variableValues depth
        source
  exact hcompleteUngrouped.trans hgroundSpec.symm

end GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
