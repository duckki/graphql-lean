import Proofs.GraphQL.Theories.ConditionTree.Extraction

/-! Feasibility and uniqueness facts for extracted condition trees. -/

namespace GraphQL
namespace ConditionTree

theorem extraction_conditions_feasible
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : schema.getPossibleTypes parentType ≠ []
      -> (canonicalBooleanCondition inheritedBooleanCondition).isSome = true
      -> ∀ condition,
          condition
            ∈ (ofSelectionSetInScope schema parentType inheritedBooleanCondition
                selectionSet).nodeConditions
          -> condition.FeasibleUnder inheritedBooleanCondition := by
  intro hpossible hinherited condition hcondition
  exact (extraction_correct schema parentType inheritedBooleanCondition selectionSet
          hpossible hinherited).conditionsFeasible
          condition hcondition

theorem extraction_conditions_unique
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : schema.getPossibleTypes parentType ≠ []
      -> (canonicalBooleanCondition inheritedBooleanCondition).isSome = true
      -> ((ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
          |>.nodeConditions).Nodup := by
  intro hpossible hinherited
  exact (extraction_correct schema parentType inheritedBooleanCondition selectionSet
          hpossible hinherited).nodeConditionsNodup

end ConditionTree
end GraphQL
