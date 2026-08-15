import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Normality
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.OperationSemantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.ReadinessPreservation
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
  intro hnormalUnique hschema hleftValid hrightValid hleftCoercion hrightCoercion
    hleftFree hrightFree
    hleftFields hrightFields hdefinitions hsem
  have hleftNormalizedValid :
      Validation.operationDefinitionValid schema
        (normalizeOperation schema left) :=
    normalizeOperation_valid schema left hschema hleftValid hleftCoercion
      hleftFree hleftFields
  have hrightNormalizedValid :
      Validation.operationDefinitionValid schema
        (normalizeOperation schema right) :=
    normalizeOperation_valid schema right hschema hrightValid hrightCoercion
      hrightFree hrightFields
  have hleftNormalizedFree :
      operationDirectiveFree (normalizeOperation schema left) :=
    normalizeOperation_directiveFree schema left hleftCoercion
  have hrightNormalizedFree :
      operationDirectiveFree (normalizeOperation schema right) :=
    normalizeOperation_directiveFree schema right hrightCoercion
  have hleftNormalizedNormal :
      operationNormal schema (normalizeOperation schema left) :=
    by simpa [normalizeOperationNormal] using
      normalizeOperation_normal schema left hschema hleftValid
  have hrightNormalizedNormal :
      operationNormal schema (normalizeOperation schema right) :=
    by simpa [normalizeOperationNormal] using
      normalizeOperation_normal schema right hschema hrightValid
  have hnormalizedDefinitions :
      variableDefinitionsSyntacticallyEquivalent
        (normalizeOperation schema left).variableDefinitions
        (normalizeOperation schema right).variableDefinitions := by
    simpa [normalizeOperation_variableDefinitions] using hdefinitions
  have hleftEquivalent :
      operationsEquivalent schema left (normalizeOperation schema left) :=
    groundTypeNormalFormSemanticsPreservation schema left hschema hleftValid
      hleftCoercion
  have hrightEquivalent :
      operationsEquivalent schema right (normalizeOperation schema right) :=
    groundTypeNormalFormSemanticsPreservation schema right hschema hrightValid
      hrightCoercion
  have hnormalizedSem :
      operationsSemanticallyEquivalent schema
        (normalizeOperation schema left) (normalizeOperation schema right) := by
    intro ObjectRef resolvers variableValues fuel source
    intro hleftNormalizedCoercible hrightNormalizedCoercible
    have hleftCoercible :
        operationArgumentsCoercible schema variableValues left :=
      operationArgumentsCoercible_of_normalizeOperation schema left variableValues
        hschema hleftValid hleftCoercion hleftFree hleftFields
        hleftNormalizedCoercible
    have hrightCoercible :
        operationArgumentsCoercible schema variableValues right :=
      operationArgumentsCoercible_of_normalizeOperation schema right variableValues
        hschema hrightValid hrightCoercion hrightFree hrightFields
        hrightNormalizedCoercible
    have hleftResponse :=
      hleftEquivalent resolvers variableValues fuel source
    have hrightResponse :=
      hrightEquivalent resolvers variableValues fuel source
    simpa [hleftResponse, hrightResponse] using
      hsem resolvers variableValues fuel source hleftCoercible hrightCoercible
  exact
    hnormalUnique hschema hleftNormalizedValid hrightNormalizedValid
      hleftNormalizedFree hrightNormalizedFree hleftNormalizedNormal
      hrightNormalizedNormal hnormalizedDefinitions hnormalizedSem

end GroundTypeNormalization

end NormalForm

end GraphQL
