import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseForestOptimality
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.CaseForestOutcomeLifting
import Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality.OutcomeCharacterization

/-! Selection-set and operation best-bound theorems for ExactCases. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open Optimality

universe u v w

theorem CaseCursor.summarizeSelectionSet_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (caseValues : VariableValues)
    : BestBound le laws.approximates
        (CaseCursor.selectionSetOutcomes semantics schema parentType
          inheritedBooleanCondition selectionSet (.symbolic caseValues))
        (CaseCursor.summarizeSelectionSet abstract schema parentType
          inheritedBooleanCondition selectionSet caseValues) := by
  unfold CaseCursor.selectionSetOutcomes CaseCursor.summarizeSelectionSet
  exact CaseCursor.summarizeConditionTree_best laws schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition [] selectionSet)
    caseValues

-- Proof-facing concrete specialization used to connect cursor outcomes to execution.
-- This is a theorem about the internal resolved fold, not a public evaluation entry
-- point.
theorem summarizeSelectionSetResolved_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : VariableValues)
    : BestBound le laws.approximates
        (CaseCursor.selectionSetOutcomes semantics schema parentType
          inheritedBooleanCondition selectionSet (.concrete variableValues))
        (summarizeSelectionSetResolved abstract schema parentType
          inheritedBooleanCondition selectionSet variableValues variableValues) := by
  unfold CaseCursor.selectionSetOutcomes summarizeSelectionSetResolved
  simpa [summarizeConditionTreeWithPruning, summarizeConditionTreeDecisionWithPruning,
    Internal.summarizeConditionTreeDecision, CaseCursor.BooleanEnvironment.pruningValues]
    using Internal.summarizeConditionTreeDecision_best laws schema
      inheritedBooleanCondition
      (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
        inheritedBooleanCondition variableValues selectionSet)
      (.concrete variableValues)

-- Every common bound of the shared cursor outcomes also bounds execution at the same
-- concrete request context.
theorem selectionSetExecutionCovered
    {semantics : OutcomeSemantics.{u}} {concrete : ConcreteAlgebra.{v}}
    {abstract : Algebra.{w}} {schema : Schema} (variableValues : VariableValues)
    (soundness : SoundnessWithFactoring concrete abstract schema variableValues)
    (laws : BestTransferLaws semantics abstract soundness.abstractLawful.le)
    (variableDefinitions : List VariableDefinition)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : SelectionSetExecutionCovered variableValues soundness laws variableDefinitions
        parentType inheritedBooleanCondition selectionSet := by
  unfold SelectionSetExecutionCovered
  intro ObjectRef resolvers fuel runtimeType ref hinherited hpossible hschema hobject
    hselectionValid hmerge
  dsimp only
  unfold OutcomeSet.IsUpperBound
  intro candidate hcandidate
  have hexecution := soundness.executeSelectionSetAnnotated_sound resolvers parentType
    inheritedBooleanCondition selectionSet fuel runtimeType ref hinherited hpossible
    variableDefinitions hschema hobject hselectionValid hmerge
  have hbest := summarizeSelectionSetResolved_best laws schema parentType
    inheritedBooleanCondition selectionSet variableValues
  apply soundness.approximates_upward _ _ _ hexecution
  exact hbest.least candidate hcandidate

theorem summarizeOperation_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}} {schema : Schema}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (operation : Operation)
    : BestBound le laws.approximates
        (operationOutcomes semantics schema operation)
        (summarizeOperation abstract schema operation) := by
  unfold operationOutcomes summarizeOperation
  exact CaseCursor.summarizeSelectionSet_best laws schema (operation.rootType schema) []
    operation.selectionSet []

theorem analysisOptimal
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}} {schema : Schema}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (operation : Operation)
    : AnalysisOptimal laws schema operation :=
  summarizeOperation_best laws operation

theorem summarizeOperationWithVariables_best
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues → Algebra.{v}) {schema : Schema}
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
  apply bestBound_of_attainable_iff
    (CaseForestOutcomeLifting.operationOutcomesWithVariables_iff_forest
      schema variableValues operation)
  exact summarizeOperationWithVariables_forest_best abstractFor variableValues operation laws

theorem analysisWithVariablesOptimal
    {semantics : OutcomeSemantics.{u}}
    (abstractFor : VariableValues → Algebra.{v}) {schema : Schema}
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
