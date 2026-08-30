import Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality.OutcomeCharacterization

/-! Selection-set and operation best-bound theorems for ExactCases. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open Optimality

universe u v w

theorem summarizeSelectionSet_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : BestBound le laws.approximates
        (selectionSetOutcomes semantics schema parentType
          inheritedBooleanCondition selectionSet initial)
        (summarizeSelectionSet abstract schema parentType inheritedBooleanCondition
          selectionSet initial) := by
  unfold selectionSetOutcomes summarizeSelectionSet
  exact summarizeConditionTree_best laws schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition initial.pruningValues selectionSet)
    initial

-- The relational outcomes collectively cover every execution at the same complete
-- request context. Coverage is by common upper bounds: one execution may combine
-- several recursively selected cases, notably across heterogeneous list elements.
theorem selectionSetExecutionCovered
    {semantics : OutcomeSemantics.{u}} {concrete : ConcreteAlgebra.{v}}
    {abstract : Algebra.{w}} {schema : Schema} (variableValues : VariableValues)
    (soundness : Soundness concrete abstract schema variableValues)
    (laws : BestTransferLaws semantics abstract soundness.abstractLawful.le)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : SelectionSetExecutionCovered variableValues soundness laws parentType
        inheritedBooleanCondition selectionSet := by
  unfold SelectionSetExecutionCovered
  intro ObjectRef resolvers fuel runtimeType ref hinherited hpossible
  dsimp only
  unfold OutcomeSet.IsUpperBound
  intro candidate hcandidate
  have hexecution := soundness.executeSelectionSetAnnotated_sound resolvers parentType
    inheritedBooleanCondition selectionSet fuel runtimeType ref hinherited hpossible
  have hbest := summarizeSelectionSet_best laws schema parentType
    inheritedBooleanCondition selectionSet
    (BooleanEnvironment.concrete variableValues)
  apply soundness.approximates_upward _ _ _
    (by exact hexecution)
  exact hbest.least candidate hcandidate

theorem summarizeOperation_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}} {schema : Schema}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (operation : Operation)
    : BestBound le laws.approximates
        (operationOutcomes semantics schema operation)
        (summarizeOperation abstract schema operation) := by
  unfold operationOutcomes summarizeOperation
  exact summarizeSelectionSet_best laws schema (operation.rootType schema) []
    operation.selectionSet BooleanEnvironment.unresolved

theorem analysisOptimal
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}} {schema : Schema}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (operation : Operation)
    : AnalysisOptimal laws schema operation :=
  summarizeOperation_best laws operation

theorem summarizeOperationWithVariables_best
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (variableValues : VariableValues) (operation : Operation)
    {le
      : (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> Prop}
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)) le)
    : BestBound le laws.approximates
        (operationOutcomesWithVariables semantics schema variableValues operation)
        (summarizeOperationWithVariables abstractFor schema variableValues
          operation) := by
  unfold operationOutcomesWithVariables summarizeOperationWithVariables
  exact summarizeSelectionSet_best laws schema (operation.rootType schema) []
    operation.selectionSet
    (BooleanEnvironment.concrete
      (Execution.coerceVariableValues operation variableValues))

theorem analysisWithVariablesOptimal
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (variableValues : VariableValues) (operation : Operation)
    {le
      : (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> (abstractFor (Execution.coerceVariableValues operation variableValues)).Summary
        -> Prop}
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)) le)
    : AnalysisWithVariablesOptimal abstractFor schema variableValues operation laws :=
  summarizeOperationWithVariables_best abstractFor variableValues operation laws

end ExactCases
end TreeSummary
end GraphQL
