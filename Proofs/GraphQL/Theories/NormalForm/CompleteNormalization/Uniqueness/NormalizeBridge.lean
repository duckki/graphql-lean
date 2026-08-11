import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Semantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.OperationBridge
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.RestrictedSemantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity

/-!
Bridge from uniqueness of complete-normal operations to uniqueness of complete
normalization results.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem completeNormalizeOperation_boolVarsEquivalent
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hboolFeasible : operationBoolTypeConditionFeasible schema operation)
    : operationBoolVarsEquivalent operation
        (completeNormalizeOperation schema operation) := by
  have hrootObject : objectTypeNameBool schema (operation.rootType schema) = true :=
    GroundTypeNormalization.operation_root_objectTypeNameBool_of_wf_valid
      hschema hvalid
  intro candidate
  cases hvariables : operationBoolVars operation with
  | nil =>
      have hnormal :
          completeNormalSelectionSet schema [] (operation.rootType schema)
            (completeNormalizeRootSelectionSet schema [] (operation.rootType schema)
              operation.selectionSet) :=
        completeNormalizeRootSelectionSet_normal_nil schema hschema
          (operation.rootType schema) operation.selectionSet
          (completeNormalizeRootSelectionSet schema [] (operation.rootType schema)
            operation.selectionSet) hrootObject rfl
      have hnormalizedFree :
          selectionSetDirectiveFree
            (completeNormalizeRootSelectionSet schema [] (operation.rootType schema)
              operation.selectionSet) :=
        hnormal.2.2
      have hnormalizedVariables :
          operationBoolVars (completeNormalizeOperation schema operation) =
            [] := by
        unfold operationBoolVars
        rw [completeNormalizeOperation_selectionSet, hvariables]
        rw [selectionSetDirectiveFree_booleanVariables_nil _ hnormalizedFree]
        rfl
      rw [hnormalizedVariables]
  | cons varName variables =>
      have hvariablesNodup : (varName :: variables).Nodup := by
        simpa [hvariables] using operationBoolVars_nodup operation
      have hnormal :
          completeNormalSelectionSet schema (varName :: variables)
            (operation.rootType schema)
            (completeNormalizeRootSelectionSet schema
              (varName :: variables) (operation.rootType schema)
              operation.selectionSet) :=
        completeNormalizeRootSelectionSet_normal_cons schema hschema varName
          variables hvariablesNodup (operation.rootType schema) operation.selectionSet
          (completeNormalizeRootSelectionSet schema (varName :: variables)
            (operation.rootType schema) operation.selectionSet) hrootObject rfl
      have hnormalizedNonempty :
          completeNormalizeRootSelectionSet schema (varName :: variables)
            (operation.rootType schema) operation.selectionSet ≠ [] := by
        simpa [hvariables] using
          completeNormalizeRootSelectionSet_ne_nil_of_boolTypeFeasible schema
            operation hschema hvalid hboolFeasible
      have hnormalizedIff :=
        operationBoolVars_mem_iff_of_completeNormalSelectionSet_cons hnormal
          hnormalizedNonempty candidate
      have hnormalizedOperationIff :
          candidate ∈ operationBoolVars
              (completeNormalizeOperation schema operation)
            ↔ candidate ∈ varName :: variables := by
        unfold operationBoolVars
        rw [completeNormalizeOperation_selectionSet, hvariables]
        exact hnormalizedIff
      simpa [hvariables] using hnormalizedOperationIff.symm

theorem completeNormalizeOperation_uniqueUpToReordering
    {schema : Schema} {left right : Operation}
    : completeNormalizeOperationUniqueUpToReordering schema left right := by
  intro hschema hleftValid hrightValid hleftFields hrightFields
    hleftBoolFeasible hrightBoolFeasible hvariables hsem
  have hleftNormalizedValid :
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema left) :=
    completeNormalizeOperation_valid schema left hschema hleftValid
      hleftFields hleftBoolFeasible
  have hrightNormalizedValid :
      Validation.operationDefinitionValid schema
        (completeNormalizeOperation schema right) :=
    completeNormalizeOperation_valid schema right hschema hrightValid
      hrightFields hrightBoolFeasible
  have hleftNormalizedNormal :
      completeNormalOperation schema
        (completeNormalizeOperation schema left) :=
    completeNormalizeOperation_normal schema left hschema hleftValid
  have hrightNormalizedNormal :
      completeNormalOperation schema
        (completeNormalizeOperation schema right) :=
    completeNormalizeOperation_normal schema right hschema hrightValid
  have hleftVariables :=
    completeNormalizeOperation_boolVarsEquivalent schema left hschema
      hleftValid hleftBoolFeasible
  have hrightVariables :=
    completeNormalizeOperation_boolVarsEquivalent schema right hschema
      hrightValid hrightBoolFeasible
  have hnormalizedVariables :
      operationBoolVarsEquivalent
        (completeNormalizeOperation schema left)
        (completeNormalizeOperation schema right) :=
    fun varName =>
      (hleftVariables varName).symm.trans
        ((hvariables varName).trans (hrightVariables varName))
  have hnormalizedSemantics :
      operationsSemanticallyEquivalentForCompleteBoolVars schema
        (operationBoolVars (completeNormalizeOperation schema left))
        (completeNormalizeOperation schema left)
        (completeNormalizeOperation schema right) := by
    intro ObjectRef resolvers variableValues fuel source
      hnormalizedComplete
    have hleftComplete :
        boolVarsComplete (operationBoolVars left) variableValues := by
      intro varName hmem
      exact hnormalizedComplete varName ((hleftVariables varName).1 hmem)
    have hrightComplete :
        boolVarsComplete (operationBoolVars right) variableValues := by
      intro varName hmem
      exact hleftComplete varName ((hvariables varName).2 hmem)
    have hleftExecution :=
      completeNormalizationSemanticsPreserved schema left hschema hleftValid
        resolvers variableValues fuel source
        (operationBoolVarsComplete_coerceVariableValues
          left variableValues hleftComplete)
    have hrightExecution :=
      completeNormalizationSemanticsPreserved schema right hschema hrightValid
        resolvers variableValues fuel source
        (operationBoolVarsComplete_coerceVariableValues
          right variableValues hrightComplete)
    rw [← hleftExecution, ← hrightExecution]
    exact hsem resolvers variableValues fuel source
  exact
    complete_normal_operations_equalUpToReordering_of_complete_bool_vars_semantics
      hschema hleftNormalizedValid hrightNormalizedValid
      hleftNormalizedNormal hrightNormalizedNormal hnormalizedVariables
      hnormalizedSemantics

end CompleteNormalization

end NormalForm

end GraphQL
