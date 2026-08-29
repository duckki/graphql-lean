import Proofs.GraphQL.Theories.ConditionTree.BooleanVariables
import Proofs.GraphQL.Theories.ConditionTree.KnownFalsePruning
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision

/-! Exact-case traversal under a complete request Boolean environment. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open Internal

-- Proof-facing entry points keep extraction pruning independent from the environment
-- being summarized. Public callers use the canonical environment-derived context.
def summarizeConditionTreeDecisionWithPruning (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableOrder : BooleanVariableNames)
    (environment : BooleanEnvironment) (pruningValues : VariableValues)
    : BooleanDecision algebra.Summary :=
  (CaseCursor.summarizeDecisionWithPruning algebra schema variableOrder
    inheritedBooleanCondition [] (.ofConditionTree tree)
    tree.condition.possibleTypes environment pruningValues).compact
    algebra.join

def summarizeConditionTreeWithPruning (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (environment : BooleanEnvironment)
    (pruningValues : VariableValues)
    : algebra.Summary :=
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  (summarizeConditionTreeDecisionWithPruning algebra schema inheritedBooleanCondition tree
    variables environment pruningValues).collapse
    algebra

def summarizeConditionTreeResolved (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  summarizeConditionTreeWithPruning algebra schema inheritedBooleanCondition tree
    (BooleanEnvironment.complete variableValues) fixedVariableValues

def summarizeSelectionSetResolved (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  summarizeConditionTreeWithPruning algebra schema inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition fixedVariableValues selectionSet)
    (BooleanEnvironment.complete variableValues) fixedVariableValues

theorem BooleanEnvironment.ofCompleteValues_eq_complete (values : VariableValues)
    : BooleanEnvironment.ofCompleteValues values
      = BooleanEnvironment.complete values := by
  rfl

theorem summarizeOperationSelectionSet_eq_resolved_ofCompleteValues
    (algebra : Algebra) (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    : summarizeSelectionSet algebra schema (operation.rootType schema) []
        operation.selectionSet
        (BooleanEnvironment.ofCompleteValues variableValues)
      = summarizeSelectionSetResolved algebra schema (operation.rootType schema) []
          operation.selectionSet variableValues variableValues := by
  rfl

end ExactCases
end TreeSummary
end GraphQL
