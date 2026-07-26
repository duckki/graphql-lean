import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationVariables

/-!
Operation projection and top-level correctness-wrapper facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem completeNormalizeOperation_rootType (schema : Schema) (operation : Operation)
    : (completeNormalizeOperation schema operation).rootType = operation.rootType := by
  rfl

theorem completeNormalizeOperation_name (schema : Schema) (operation : Operation)
    : (completeNormalizeOperation schema operation).name = operation.name := by
  rfl

theorem completeNormalizeOperation_variableDefinitions
    (schema : Schema) (operation : Operation)
    : (completeNormalizeOperation schema operation).variableDefinitions
      = operation.variableDefinitions := by
  rfl

theorem completeNormalizeOperation_selectionSet (schema : Schema) (operation : Operation)
    : (completeNormalizeOperation schema operation).selectionSet
      = completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          operation.rootType operation.selectionSet := by
  rfl

theorem completeNormalizeOperation_rootSourceAppliesBool (schema : Schema)
    (operation : Operation) (source : Execution.ResolverValue ObjectRef)
    : Execution.rootSourceAppliesBool schema
        (completeNormalizeOperation schema operation) source
      = Execution.rootSourceAppliesBool schema operation source := by
  have hroot := completeNormalizeOperation_rootType schema operation
  simp [Execution.rootSourceAppliesBool, hroot]

theorem completeNormalizationSemanticsPreserved_of_selectionSet
    (schema : Schema) (operation : Operation)
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.operationDefinitionValid schema operation
        -> ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
              variableValues depth (source : Execution.ResolverValue ObjectRef),
            operationBoolVarsComplete operation variableValues
            -> Execution.rootSourceAppliesBool schema operation source = true
            -> Execution.executeSelectionSet schema resolvers variableValues depth
                  operation.rootType source operation.selectionSet
                = Execution.executeSelectionSet schema resolvers variableValues depth
                    operation.rootType source
                    (completeNormalizeOperation schema operation).selectionSet)
      -> completeNormalizationSemanticsPreserved schema operation := by
  intro hselection hschema hvalid ObjectRef resolvers variableValues depth
    source hcomplete
  cases hroot : Execution.rootSourceAppliesBool schema operation source with
  | false =>
      have hnormalizedRoot :
          Execution.rootSourceAppliesBool schema
              (completeNormalizeOperation schema operation) source =
            false := by
        simpa [completeNormalizeOperation_rootSourceAppliesBool
          schema operation source] using hroot
      simp [Execution.executeQueryWithFuel, hroot, hnormalizedRoot]
  | true =>
      have hnormalizedRoot :
          Execution.rootSourceAppliesBool schema
              (completeNormalizeOperation schema operation) source =
            true := by
        simpa [completeNormalizeOperation_rootSourceAppliesBool
          schema operation source] using hroot
      have hnormalizedRootType :
          (completeNormalizeOperation schema operation).rootType =
            operation.rootType :=
        completeNormalizeOperation_rootType schema operation
      have hselectionEq :=
        hselection hschema hvalid resolvers variableValues depth source
          hcomplete hroot
      have hrootSelectionEq :
          Execution.executeRootSelectionSet schema resolvers variableValues
            depth operation.rootType source operation.selectionSet =
          Execution.executeRootSelectionSet schema resolvers variableValues
            depth operation.rootType source
            (completeNormalizeOperation schema operation).selectionSet := by
        simpa [Execution.executeSelectionSet] using hselectionEq
      simp [Execution.executeQueryWithFuel, hroot, hnormalizedRoot,
        hnormalizedRootType, hrootSelectionEq]

end CompleteNormalization

end NormalForm

end GraphQL
