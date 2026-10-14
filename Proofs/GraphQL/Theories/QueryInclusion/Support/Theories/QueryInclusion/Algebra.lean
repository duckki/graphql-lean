import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.QueryInclusion

open Execution
open scoped SyntacticEquivalence
open QueryInclusion
open Execution

mutual
  private theorem inputValueStructuralEquivalent_trans
      : ∀ {left middle right : InputValue},
          InputValue.structuralEquivalent left middle
          -> InputValue.structuralEquivalent middle right
          -> InputValue.structuralEquivalent left right := by
    intro left middle right hleft hright
    cases left <;> cases middle <;> cases right <;>
      simp [InputValue.structuralEquivalent] at hleft hright ⊢
    all_goals
      first
      | exact hleft.trans hright
      | exact inputValuesStructuralEquivalent_trans hleft hright
      | exact inputObjectFieldsStructuralEquivalent_trans hleft hright
      | trivial
      | contradiction

  private theorem inputValuesStructuralEquivalent_trans
      : ∀ {left middle right : List InputValue},
          InputValue.structuralValuesEquivalent left middle
          -> InputValue.structuralValuesEquivalent middle right
          -> InputValue.structuralValuesEquivalent left right
    | [], [], [], _hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent]
    | left :: lefts, middle :: middles, right :: rights, hleft, hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft hright ⊢
        exact ⟨inputValueStructuralEquivalent_trans hleft.1 hright.1,
          inputValuesStructuralEquivalent_trans hleft.2 hright.2⟩
    | [], [], _ :: _, _hleft, hright => by
        simp [InputValue.structuralValuesEquivalent] at hright
    | [], _ :: _, [], hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | [], _ :: _, _ :: _, hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | _ :: _, [], [], hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | _ :: _, [], _ :: _, hleft, _hright => by
        simp [InputValue.structuralValuesEquivalent] at hleft
    | _ :: _, _ :: _, [], _hleft, hright => by
        simp [InputValue.structuralValuesEquivalent] at hright

  private theorem inputObjectFieldsStructuralEquivalent_trans
      : ∀ {left middle right : List (Name × InputValue)},
          InputValue.structuralObjectFieldsEquivalent left middle
          -> InputValue.structuralObjectFieldsEquivalent middle right
          -> InputValue.structuralObjectFieldsEquivalent left right
    | [], [], [], _hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent]
    | (leftName, leftValue) :: lefts,
        (middleName, middleValue) :: middles,
        (rightName, rightValue) :: rights, hleft, hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft hright ⊢
        exact ⟨hleft.1.trans hright.1,
          inputValueStructuralEquivalent_trans hleft.2.1 hright.2.1,
          inputObjectFieldsStructuralEquivalent_trans hleft.2.2 hright.2.2⟩
    | [], [], _ :: _, _hleft, hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hright
    | [], _ :: _, [], hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | [], _ :: _, _ :: _, hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | _ :: _, [], [], hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | _ :: _, [], _ :: _, hleft, _hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hleft
    | _ :: _, _ :: _, [], _hleft, hright => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hright
end

theorem argumentsEquivalent_trans {left middle right : List Argument}
    : Argument.argumentsEquivalent left middle
      -> Argument.argumentsEquivalent middle right
      -> Argument.argumentsEquivalent left right := by
  intro hleft hright
  exact ⟨
    by
      intro argument hargument
      rcases hleft.1 argument hargument with ⟨middleArgument, hmiddle, hequivalentLeft⟩
      rcases hright.1 middleArgument hmiddle with ⟨rightArgument, hrightMember, hequivalentRight⟩
      exact ⟨rightArgument, hrightMember,
        ⟨hequivalentLeft.1.trans hequivalentRight.1,
          inputValueStructuralEquivalent_trans hequivalentLeft.2 hequivalentRight.2⟩⟩,
    by
      intro argument hargument
      rcases hright.2 argument hargument with ⟨middleArgument, hmiddle, hequivalentRight⟩
      rcases hleft.2 middleArgument hmiddle with ⟨leftArgument, hleftMember, hequivalentLeft⟩
      exact ⟨leftArgument, hleftMember,
        ⟨hequivalentLeft.1.trans hequivalentRight.1,
          inputValueStructuralEquivalent_trans hequivalentLeft.2 hequivalentRight.2⟩⟩
  ⟩

theorem argumentsSyntacticallyEquivalentBool_iff (left right : List Argument)
    : Argument.argumentsSyntacticallyEquivalentBool left right = true ↔ left ≡ right := by
  change Argument.argumentsSyntacticallyEquivalentBool left right = true
    ↔ Argument.argumentsEquivalent left right
  simp only [Argument.argumentsSyntacticallyEquivalentBool, decide_eq_true_iff]

end GraphQL.QueryInclusion
