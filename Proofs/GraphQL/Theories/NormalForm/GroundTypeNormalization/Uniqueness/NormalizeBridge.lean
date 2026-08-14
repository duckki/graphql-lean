import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.OperationSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.OperationBridge
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity

/-!
Bridge from uniqueness of already-normal operations to uniqueness of normalized
operations.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem normalizeOperation_uniqueUpToReordering_of_normal_operations
    {schema : Schema} {left right : Operation}
    : normalOperationsSemanticallyEquivalentEqualUpToReordering schema
        (normalizeOperation schema left) (normalizeOperation schema right)
      -> normalizeOperationUniqueUpToReordering schema left right := by
  intro hnormalUnique hschema hleftValid hrightValid hleftFree hrightFree
    hleftFields hrightFields hleftFeasible hrightFeasible hdefinitions hsem
  have hleftNormalizedValid :
      Validation.operationDefinitionValid schema
        (normalizeOperation schema left) :=
    normalizeOperation_valid schema left hschema hleftValid hleftFree
      hleftFields hleftFeasible
  have hrightNormalizedValid :
      Validation.operationDefinitionValid schema
        (normalizeOperation schema right) :=
    normalizeOperation_valid schema right hschema hrightValid hrightFree
      hrightFields hrightFeasible
  have hleftNormalizedFree :
      operationDirectiveFree (normalizeOperation schema left) :=
    normalizeOperation_directiveFree schema left hleftFree
  have hrightNormalizedFree :
      operationDirectiveFree (normalizeOperation schema right) :=
    normalizeOperation_directiveFree schema right hrightFree
  have hleftNormalizedNormal :
      operationNormal schema (normalizeOperation schema left) :=
    by simpa [normalizeOperationNormal] using
      normalizeOperation_normal schema left hschema hleftValid
  have hrightNormalizedNormal :
      operationNormal schema (normalizeOperation schema right) :=
    by simpa [normalizeOperationNormal] using
      normalizeOperation_normal schema right hschema hrightValid
  have hnormalizedDefinitions :
      variableDefinitionsEquivalent
        (normalizeOperation schema left).variableDefinitions
        (normalizeOperation schema right).variableDefinitions := by
    simpa [normalizeOperation_variableDefinitions] using hdefinitions
  have hleftEquivalent :
      operationsEquivalent schema left (normalizeOperation schema left) :=
    groundTypeNormalFormSemanticsPreservation schema left hschema hleftValid
      hleftFree
  have hrightEquivalent :
      operationsEquivalent schema right (normalizeOperation schema right) :=
    groundTypeNormalFormSemanticsPreservation schema right hschema hrightValid
      hrightFree
  have hnormalizedSem :
      operationsSemanticallyEquivalent schema
        (normalizeOperation schema left) (normalizeOperation schema right) := by
    intro ObjectRef resolvers variableValues fuel source
    have hleftResponse :=
      hleftEquivalent resolvers variableValues fuel source
    have hrightResponse :=
      hrightEquivalent resolvers variableValues fuel source
    simpa [hleftResponse, hrightResponse] using
      hsem resolvers variableValues fuel source
  exact
    hnormalUnique hschema hleftNormalizedValid hrightNormalizedValid
      hleftNormalizedFree hrightNormalizedFree hleftNormalizedNormal
      hrightNormalizedNormal hnormalizedDefinitions hnormalizedSem

end GroundTypeNormalization

end NormalForm

end GraphQL
