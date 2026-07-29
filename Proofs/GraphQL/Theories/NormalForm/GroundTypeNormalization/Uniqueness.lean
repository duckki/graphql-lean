import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedOperationBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedValidSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.NormalizeBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.ReorderingSoundness

/-!
Ground-type normal-form uniqueness theorem surface.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem normal_operations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : normalOperationsEqualUpToReorderingSemanticallyEquivalent schema left right := by
  intro hleftFree hrightFree hleftNormal hrightNormal hequal
  rcases hequal with ⟨_hroot, hselectionEqual⟩
  have hrootType : (left.rootType schema) = (right.rootType schema) := by
    cases left.operationType
    cases right.operationType
    rfl
  have hrightSelectionNormal :
    selectionSetNormal schema (left.rootType schema) right.selectionSet := by
    simpa [operationNormal, hrootType] using hrightNormal
  have hselectionSem :
      selectionSetsSemanticallyEquivalent schema (left.rootType schema)
        left.selectionSet right.selectionSet :=
    selectionSetsSemanticallyEquivalent_of_equalUpToReordering
      hleftFree hrightFree hleftNormal hrightSelectionNormal hselectionEqual
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
      have hleftValues :=
        CompleteNormalization.executeSelectionSet_eq_of_directiveFree_variableValues
          schema resolvers variableValues
          (Execution.coerceVariableValues left variableValues) fuel (left.rootType schema)
          source left.selectionSet hleftFree
      have hrightValues :=
        CompleteNormalization.executeSelectionSet_eq_of_directiveFree_variableValues
          schema resolvers variableValues
          (Execution.coerceVariableValues right variableValues) fuel (left.rootType schema)
          source right.selectionSet hrightFree
      have hselectionResponse :=
        hselectionSem resolvers variableValues fuel source hsource
      simp only [Execution.executeSelectionSetAsResponse] at hselectionResponse
      rw [hleftValues, hrightValues] at hselectionResponse
      simpa [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
        Execution.executeSelectionSetAsResponse,
        Execution.executeSelectionSet, hrootType] using hselectionResponse

theorem normalizeOperations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : normalizeOperationsEqualUpToReorderingSemanticallyEquivalent schema left right := by
  intro hschema hleftValid hrightValid hleftFree hrightFree hequal
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
  have hnormalizedSemantics :
      operationsSemanticallyEquivalent schema
        (normalizeOperation schema left)
        (normalizeOperation schema right) :=
    normal_operations_equalUpToReordering_semanticallyEquivalent
      hleftNormalizedFree hrightNormalizedFree hleftNormalizedNormal
      hrightNormalizedNormal hequal
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
    normal_operations_semanticallyEquivalent_equalUpToReordering_of_valid_object_diff_observable_trace_data_separates
      (fun hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hobject responsePath htrace =>
        not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_pairedPath
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject htrace)

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
