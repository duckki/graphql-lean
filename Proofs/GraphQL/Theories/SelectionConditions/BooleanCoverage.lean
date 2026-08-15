import Proofs.GraphQL.Theories.SelectionConditions.Runtime
import GraphQL.Theories.ExecutionReadiness

/-! Runtime soundness of symbolic Boolean-clause subtraction. -/

namespace GraphQL
namespace SelectionConditions

open Execution

def booleanConditionsVariables (conditions : List (List BooleanLiteral)) : List Name :=
  (conditions.flatMap
    fun condition => condition.map BooleanLiteral.variableName).eraseDups

theorem BooleanLiteral.allows_or_complement_of_complete
    (variableValues : VariableValues) (literal : BooleanLiteral)
    (hcomplete
      : ∃ value,
          inputValueBoolean? variableValues (.variable literal.variableName) = some value)
    : literal.allows variableValues = true
      ∨ literal.complement.allows variableValues = true := by
  rcases hcomplete with ⟨value, hvalue⟩
  cases literal <;> cases value <;>
    simp_all [BooleanLiteral.allows, BooleanLiteral.complement,
      BooleanLiteral.variableName, BooleanLiteral.toDirective,
      directiveAllowsSelectionBool]

theorem subtractBooleanCondition_exists_allows (variableValues : VariableValues)
    : ∀ condition cover,
        booleanConditionAllows variableValues condition = true
        -> booleanConditionAllows variableValues cover = false
        -> boolVarsComplete (cover.map BooleanLiteral.variableName) variableValues
        -> ∃ remainder,
            remainder ∈ subtractBooleanCondition condition cover
            ∧ booleanConditionAllows variableValues remainder = true
  | condition, [], _hcondition, hcover, _hcomplete => by
      simp [booleanConditionAllows] at hcover
  | condition, literal :: rest, hcondition, hcover, hcomplete => by
      have hliteralComplete := hcomplete literal.variableName (by simp)
      have hrestComplete : boolVarsComplete
          (rest.map BooleanLiteral.variableName) variableValues := by
        intro variableName hvariable
        exact hcomplete variableName (by simp [hvariable])
      by_cases hcomplementMem : literal.complement ∈ condition
      · refine ⟨condition, ?_, hcondition⟩
        simp [subtractBooleanCondition, hcomplementMem]
      · by_cases hliteralMem : literal ∈ condition
        ·
          have hliteralAllows : literal.allows variableValues = true :=
            booleanConditionAllows_member variableValues condition hcondition
              hliteralMem
          have hrestFalse : booleanConditionAllows variableValues rest = false := by
            simpa [booleanConditionAllows, hliteralAllows] using hcover
          rcases subtractBooleanCondition_exists_allows variableValues condition rest
              hcondition hrestFalse hrestComplete with
            ⟨remainder, hmember, hallows⟩
          exact ⟨remainder, by
            simp [subtractBooleanCondition, hcomplementMem, hliteralMem,
              hmember], hallows⟩
        · rcases BooleanLiteral.allows_or_complement_of_complete variableValues
              literal hliteralComplete with hliteralAllows | hcomplementAllows
          · have hrestFalse : booleanConditionAllows variableValues rest = false := by
              simpa [booleanConditionAllows, hliteralAllows] using hcover
            have hinside : booleanConditionAllows variableValues
                (literal :: condition) = true := by
              simp [booleanConditionAllows, hliteralAllows, hcondition]
            rcases subtractBooleanCondition_exists_allows variableValues
                (literal :: condition) rest hinside hrestFalse hrestComplete with
              ⟨remainder, hmember, hallows⟩
            refine ⟨remainder, ?_, hallows⟩
            simp [subtractBooleanCondition, hcomplementMem, hliteralMem, hmember]
          · refine ⟨literal.complement :: condition, ?_, ?_⟩
            · simp [subtractBooleanCondition, hcomplementMem, hliteralMem]
            · simp [booleanConditionAllows, hcomplementAllows, hcondition]

theorem subtractBooleanConditions_exists_allows
    (variableValues : VariableValues)
    (conditions : List (List BooleanLiteral)) (cover : List BooleanLiteral)
    (hcondition
      : ∃ condition,
          condition ∈ conditions ∧ booleanConditionAllows variableValues condition = true)
    (hcover : booleanConditionAllows variableValues cover = false)
    (hcomplete : boolVarsComplete (cover.map BooleanLiteral.variableName) variableValues)
    : ∃ remainder,
        remainder ∈ subtractBooleanConditions conditions cover
        ∧ booleanConditionAllows variableValues remainder = true := by
  rcases hcondition with ⟨condition, hmember, hallows⟩
  rcases subtractBooleanCondition_exists_allows variableValues condition cover
      hallows hcover hcomplete with ⟨remainder, hremainder, hallows⟩
  exact ⟨remainder, by
    simp [subtractBooleanConditions]
    exact ⟨condition, hmember, hremainder⟩, hallows⟩

theorem uncoveredBooleanConditions_exists_allows (variableValues : VariableValues)
    : ∀ conditions covers,
        (∃ condition,
          condition ∈ conditions ∧ booleanConditionAllows variableValues condition = true)
        -> (∀ cover,
              cover ∈ covers -> booleanConditionAllows variableValues cover = false)
        -> boolVarsComplete (booleanConditionsVariables covers) variableValues
        -> ∃ remainder,
            remainder ∈ uncoveredBooleanConditions conditions covers
            ∧ booleanConditionAllows variableValues remainder = true
  | conditions, [], hcondition, _hcovers, _hcomplete => by
      simpa [uncoveredBooleanConditions] using hcondition
  | conditions, cover :: rest, hcondition, hcovers, hcomplete => by
      have hcoverFalse := hcovers cover (by simp)
      have hcoverComplete : boolVarsComplete
          (cover.map BooleanLiteral.variableName) variableValues := by
        intro variableName hvariable
        apply hcomplete variableName
        apply List.mem_eraseDups.mpr
        apply List.mem_append.mpr
        exact Or.inl hvariable
      have hrestComplete : boolVarsComplete
          (booleanConditionsVariables rest) variableValues := by
        intro variableName hvariable
        apply hcomplete variableName
        simp [booleanConditionsVariables] at hvariable ⊢
        exact Or.inr hvariable
      have hsubtracted := subtractBooleanConditions_exists_allows variableValues
        conditions cover hcondition hcoverFalse hcoverComplete
      apply uncoveredBooleanConditions_exists_allows variableValues
        (subtractBooleanConditions conditions cover) rest hsubtracted
      · intro candidate hcandidate
        exact hcovers candidate (by simp [hcandidate])
      · exact hrestComplete

-- A successful symbolic coverage check is a semantic implication for every complete
-- assignment of the variables mentioned by its covering clauses.
theorem booleanConditionCoveredByBool_sound
    (condition : List BooleanLiteral) (covers : List (List BooleanLiteral))
    (hcheck : booleanConditionCoveredByBool condition covers = true)
    (variableValues : VariableValues)
    (hcomplete : boolVarsComplete (booleanConditionsVariables covers) variableValues)
    (hcondition : booleanConditionAllows variableValues condition = true)
    : ∃ cover, cover ∈ covers ∧ booleanConditionAllows variableValues cover = true := by
  by_cases hcovered : ∃ cover,
      cover ∈ covers
      ∧ booleanConditionAllows variableValues cover = true
  · exact hcovered
  · have hcoversFalse : ∀ cover,
        cover ∈ covers
        -> booleanConditionAllows variableValues cover = false := by
      intro cover hcover
      cases hallows : booleanConditionAllows variableValues cover with
      | false => rfl
      | true =>
          exact False.elim <| hcovered ⟨cover, hcover, hallows⟩
    have hremainder := uncoveredBooleanConditions_exists_allows variableValues
      [condition] covers ⟨condition, by simp, hcondition⟩ hcoversFalse hcomplete
    rcases hremainder with ⟨remainder, hmember, _hallows⟩
    have hempty : uncoveredBooleanConditions [condition] covers = [] :=
      List.isEmpty_iff.mp hcheck
    rw [hempty] at hmember
    simp at hmember

end SelectionConditions
end GraphQL
