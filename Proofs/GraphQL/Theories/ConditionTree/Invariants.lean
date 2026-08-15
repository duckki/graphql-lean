import Proofs.GraphQL.Theories.ConditionTree.Extraction

/-! Public feasibility and separation witnesses for extracted condition trees. -/

namespace GraphQL
namespace ConditionTree

theorem extraction_conditionGroups_feasible
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : ExtractionConditionGroupsFeasible schema parentType inheritedBooleanCondition
        selectionSet := by
  intro hpossible hinherited condition hcondition
  exact (extraction_correct schema parentType inheritedBooleanCondition selectionSet
          hpossible hinherited).conditionsFeasible
          condition hcondition

theorem extraction_conditionGroups_separated
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : ExtractionConditionGroupsSeparated schema parentType inheritedBooleanCondition
        selectionSet := by
  intro hpossible hinherited
  exact (extraction_correct schema parentType inheritedBooleanCondition selectionSet
          hpossible hinherited).nodeConditionsNodup

end ConditionTree
end GraphQL
