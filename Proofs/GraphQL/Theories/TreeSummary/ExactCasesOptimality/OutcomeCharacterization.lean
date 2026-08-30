import GraphQL.Theories.TreeSummary.ExactCasesOptimality
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Relation
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Soundness

/-! Executable characterization of ExactCases relational outcome semantics.

The public relational semantics is independent of the executable fold and analysis
algebra. This module characterizes it using the executable cursor, then transports
localized best-bound obligations through condition-tree traversal.
-/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution
open GraphQL.Execution.FieldGroups
open Optimality
open Internal
open CaseCursor

universe u v w

namespace OutcomeSemantics

-- Proof-only interpretation used to connect the relational outcome derivations to
-- the generic algebra-relation theorem. It is not part of the public relational
-- outcome semantics.
@[reducible]
private def proofAlgebra (semantics : OutcomeSemantics.{u}) : Algebra.{u} :=
  {
    Summary := OutcomeSet semantics.Summary
    empty := OutcomeSet.singleton semantics.empty
    combine := OutcomeSet.combine semantics.combine
    field :=
      fun group children =>
        OutcomeSet.bind children (semantics.fieldOutcomes group)
    join := OutcomeSet.union
  }

end OutcomeSemantics

namespace BestTransferLaws

private def relation {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le)
    : (OutcomeSemantics.proofAlgebra semantics).Relation abstract :=
  {
    related := BestBound le laws.approximates
    empty_related := laws.empty_best
    combine_related := fun _ _ _ _ => laws.combine_best _ _ _ _
    field_related := fun group _ _ => laws.field_best group _ _
    join_related := fun _ _ _ _ => laws.join_best _ _ _ _
  }

end BestTransferLaws

namespace CaseCursor.BooleanEnvironment

abbrev Matches (environment : BooleanEnvironment) (assignment : BooleanAssignment)
    : Prop :=
  assignment.Extends environment

private theorem statusForVariable_assign_self
    (environment : BooleanEnvironment) (variableName : Name) (value : Bool)
    (hstatus : environment.statusForVariable variableName = none)
    : (environment.assign variableName value).statusForVariable variableName
      = some value := by
  cases environment with
  | symbolic values =>
      simp only [statusForVariable, variableValues, inputValueBoolean?] at hstatus ⊢
      simp [assign, lookupVariableValue?, ConstInputValue.toInputValue,
        InputValue.staticBoolean?]
  | concrete values =>
      simp only [statusForVariable, variableValues] at hstatus
      split at hstatus <;> contradiction

private theorem statusForVariable_assign_of_ne
    (environment : BooleanEnvironment) (selectedVariable : Name) (selectedValue : Bool)
    {variableName : Name} (hne : variableName ≠ selectedVariable)
    : (environment.assign selectedVariable selectedValue).statusForVariable variableName
      = environment.statusForVariable variableName := by
  cases environment <;>
    simp [assign, statusForVariable, variableValues, inputValueBoolean?,
      lookupVariableValue?, InputValue.staticBoolean?, Ne.symm hne]

private theorem assign_comm_statusForVariable
    (environment : BooleanEnvironment) (leftVariable : Name) (leftValue : Bool)
    (rightVariable : Name) (rightValue : Bool)
    (hne : leftVariable ≠ rightVariable)
    : ∀ variableName,
        ((environment.assign leftVariable leftValue).assign rightVariable
          rightValue).statusForVariable
          variableName
        = ((environment.assign rightVariable rightValue).assign leftVariable
            leftValue).statusForVariable
            variableName := by
  intro variableName
  cases environment with
  | concrete values => rfl
  | symbolic values =>
      simp only [assign, statusForVariable, variableValues, inputValueBoolean?,
        lookupVariableValue?]
      by_cases hleft : leftVariable = variableName
      · subst variableName
        simp [Ne.symm hne, ConstInputValue.toInputValue,
          InputValue.staticBoolean?]
      · by_cases hright : rightVariable = variableName
        · subst variableName
          simp [hne, ConstInputValue.toInputValue, InputValue.staticBoolean?]
        · simp [hleft, hright]

theorem exists_matches (environment : BooleanEnvironment)
    : ∃ assignment, Matches environment assignment := by
  let assignment : BooleanAssignment := fun variableName =>
    (environment.statusForVariable variableName).getD false
  refine ⟨assignment, ?_⟩
  intro variableName value hstatus
  simp [assignment, hstatus]

theorem matches_assign_iff
    (environment : BooleanEnvironment) (assignment : BooleanAssignment)
    (variableName : Name) (value : Bool)
    (hstatus : environment.statusForVariable variableName = none)
    : Matches (environment.assign variableName value) assignment
      ↔ Matches environment assignment ∧ assignment variableName = value := by
  constructor
  · intro hmatches
    constructor
    · intro candidate candidateValue hcandidate
      by_cases hequal : candidate = variableName
      · subst candidate
        rw [hstatus] at hcandidate
        contradiction
      · apply hmatches candidate candidateValue
        rw [statusForVariable_assign_of_ne environment variableName value hequal]
        exact hcandidate
    · exact hmatches variableName value
        (statusForVariable_assign_self environment variableName value hstatus)
  · rintro ⟨hmatches, hvalue⟩
    intro candidate candidateValue hcandidate
    by_cases hequal : candidate = variableName
    · subst candidate
      rw [statusForVariable_assign_self environment variableName value hstatus] at hcandidate
      cases hcandidate
      exact hvalue
    · apply hmatches candidate candidateValue
      rw [statusForVariable_assign_of_ne environment variableName value hequal] at hcandidate
      exact hcandidate

@[simp]
theorem pruningValues_assign (environment : BooleanEnvironment)
    (variableName : Name) (value : Bool)
    : (environment.assign variableName value).pruningValues
      = environment.pruningValues := by
  cases environment <;> rfl

def Refines (refined initial : BooleanEnvironment) : Prop :=
  ∀ variableName value,
    initial.statusForVariable variableName = some value
    -> refined.statusForVariable variableName = some value

theorem extends_of_refines
    {assignment : BooleanAssignment} {refined initial : BooleanEnvironment}
    (hmatches : assignment.Extends refined) (hrefines : Refines refined initial)
    : assignment.Extends initial := by
  intro variableName value hstatus
  exact hmatches variableName value (hrefines variableName value hstatus)

private theorem assign_self_refines
    (environment : BooleanEnvironment) (assignment : BooleanAssignment)
    (hmatches : assignment.Extends environment) (variableName : Name)
    : Refines (environment.assign variableName (assignment variableName))
        environment := by
  intro candidate value hstatus
  by_cases hequal : candidate = variableName
  · subst candidate
    have hvalue := hmatches variableName value hstatus
    cases environment with
    | symbolic values =>
        simp [assign, statusForVariable, variableValues, inputValueBoolean?,
          lookupVariableValue?, ConstInputValue.toInputValue,
          InputValue.staticBoolean?, hvalue]
    | concrete values => simpa [assign] using hstatus
  · rw [statusForVariable_assign_of_ne environment variableName
      (assignment variableName) hequal]
    exact hstatus

private theorem extends_assign_self
    {environment : BooleanEnvironment} {assignment : BooleanAssignment}
    (hmatches : assignment.Extends environment) (variableName : Name)
    : assignment.Extends (environment.assign variableName (assignment variableName)) := by
  intro candidate value hstatus
  by_cases hequal : candidate = variableName
  · subst candidate
    cases environment with
    | symbolic values =>
        simpa [assign, statusForVariable, variableValues, inputValueBoolean?,
          lookupVariableValue?, ConstInputValue.toInputValue,
          InputValue.staticBoolean?] using hstatus
    | concrete values =>
        apply hmatches variableName value
        simpa [assign] using hstatus
  · apply hmatches candidate value
    rw [← statusForVariable_assign_of_ne environment variableName
      (assignment variableName) hequal]
    exact hstatus

theorem extends_assignVariables_self
    (assignment : BooleanAssignment) (variables : List Name)
    (environment : BooleanEnvironment) (hmatches : assignment.Extends environment)
    : assignment.Extends (environment.assignVariables variables assignment) := by
  unfold assignVariables
  induction variables generalizing environment with
  | nil => exact hmatches
  | cons variableName rest ih =>
      rw [List.foldl_cons]
      exact ih _ (extends_assign_self hmatches variableName)

theorem assignVariables_self_refines
    (assignment : BooleanAssignment) (variables : List Name)
    (environment : BooleanEnvironment) (hmatches : assignment.Extends environment)
    : Refines (environment.assignVariables variables assignment) environment := by
  unfold assignVariables
  induction variables generalizing environment with
  | nil =>
      intro variableName value hstatus
      exact hstatus
  | cons variableName rest ih =>
      rw [List.foldl_cons]
      have hnext := extends_assign_self hmatches variableName
      have hrest := ih _ hnext
      intro candidate value hstatus
      exact hrest candidate value
        (assign_self_refines environment assignment hmatches variableName
          candidate value hstatus)

@[simp]
theorem pruningValues_assignVariables
    (environment : BooleanEnvironment) (assignment : BooleanAssignment)
    (variables : List Name)
    : (environment.assignVariables variables assignment).pruningValues
      = environment.pruningValues := by
  unfold assignVariables
  induction variables generalizing environment with
  | nil => rfl
  | cons variableName rest ih =>
      rw [List.foldl_cons, ih, pruningValues_assign]

end CaseCursor.BooleanEnvironment

namespace Internal.BooleanDecision

-- Evaluation fixes Boolean splits by one total assignment while retaining type-case
-- joins as nondeterministic unions.
private def evaluateOutcome (assignment : BooleanAssignment)
    : BooleanDecision (OutcomeSet α) -> OutcomeSet α
  | .leaf outcomes => outcomes
  | .split variableName onFalse onTrue =>
      if assignment variableName then
        evaluateOutcome assignment onTrue
      else
        evaluateOutcome assignment onFalse
  | .join left right =>
      OutcomeSet.union (evaluateOutcome assignment left)
        (evaluateOutcome assignment right)

-- Every split is unresolved in the environment at that point, and both children are
-- checked after recording their selected value. This invariant lets a collapsed split
-- join be represented by one consistent global assignment.
private inductive ResolvedBy : BooleanEnvironment -> BooleanDecision α -> Prop
  | leaf (environment summary) : ResolvedBy environment (.leaf summary)
  | split (environment variableName onFalse onTrue)
    (hstatus : environment.statusForVariable variableName = none)
    (hfalse : ResolvedBy (environment.assign variableName false) onFalse)
    (htrue : ResolvedBy (environment.assign variableName true) onTrue)
    : ResolvedBy environment (.split variableName onFalse onTrue)
  | join (environment left right)
    (hleft : ResolvedBy environment left)
    (hright : ResolvedBy environment right)
    : ResolvedBy environment (.join left right)

private theorem ResolvedBy.map (transform : α -> β)
    {environment : BooleanEnvironment} {decision : BooleanDecision α}
    (hdecision : ResolvedBy environment decision)
    : ResolvedBy environment (decision.map transform) := by
  induction hdecision with
  | leaf => exact .leaf _ _
  | split _ _ _ _ hstatus _ _ ihFalse ihTrue =>
      exact .split _ _ _ _ hstatus ihFalse ihTrue
  | join _ _ _ _ _ ihLeft ihRight => exact .join _ _ _ ihLeft ihRight

private theorem ResolvedBy.congr
    {leftEnvironment rightEnvironment : BooleanEnvironment}
    {decision : BooleanDecision α}
    (hstatus
      : ∀ variableName,
          leftEnvironment.statusForVariable variableName
          = rightEnvironment.statusForVariable variableName)
    (hdecision : ResolvedBy leftEnvironment decision)
    : ResolvedBy rightEnvironment decision := by
  induction hdecision generalizing rightEnvironment with
  | leaf => exact .leaf _ _
  | split environment variableName onFalse onTrue hnone _ _ ihFalse ihTrue =>
      have hrightNone := (hstatus variableName).symm.trans hnone
      apply ResolvedBy.split rightEnvironment variableName onFalse onTrue hrightNone
      · apply ihFalse
        intro candidate
        by_cases hequal : candidate = variableName
        · subst candidate
          rw [BooleanEnvironment.statusForVariable_assign_self environment variableName
            false hnone]
          rw [BooleanEnvironment.statusForVariable_assign_self rightEnvironment
            variableName false hrightNone]
        · rw [BooleanEnvironment.statusForVariable_assign_of_ne environment variableName
              false hequal,
            BooleanEnvironment.statusForVariable_assign_of_ne rightEnvironment variableName
              false hequal]
          exact hstatus candidate
      · apply ihTrue
        intro candidate
        by_cases hequal : candidate = variableName
        · subst candidate
          rw [BooleanEnvironment.statusForVariable_assign_self environment variableName
            true hnone]
          rw [BooleanEnvironment.statusForVariable_assign_self rightEnvironment
            variableName true hrightNone]
        · rw [BooleanEnvironment.statusForVariable_assign_of_ne environment variableName
              true hequal,
            BooleanEnvironment.statusForVariable_assign_of_ne rightEnvironment variableName
              true hequal]
          exact hstatus candidate
  | join environment left right _ _ ihLeft ihRight =>
      exact .join rightEnvironment left right (ihLeft hstatus) (ihRight hstatus)

private theorem ResolvedBy.restrict_of_known
    {environment : BooleanEnvironment} {decision : BooleanDecision α}
    (hdecision : ResolvedBy environment decision)
    (selectedVariable : Name) (selectedValue knownValue : Bool)
    (hknown : environment.statusForVariable selectedVariable = some knownValue)
    : ResolvedBy environment (decision.restrict selectedVariable selectedValue) := by
  induction hdecision with
  | leaf => exact .leaf _ _
  | split environment variableName onFalse onTrue hstatus _ _ ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split <;> rename_i hequal
      · subst variableName
        rw [hknown] at hstatus
        contradiction
      · have hne : selectedVariable ≠ variableName := Ne.symm hequal
        apply ResolvedBy.split environment variableName _ _ hstatus
        · apply ihFalse
          rw [BooleanEnvironment.statusForVariable_assign_of_ne environment variableName
            false hne]
          exact hknown
        · apply ihTrue
          rw [BooleanEnvironment.statusForVariable_assign_of_ne environment variableName
            true hne]
          exact hknown
  | join environment left right _ _ ihLeft ihRight =>
      exact .join environment _ _ (ihLeft hknown) (ihRight hknown)

private theorem ResolvedBy.restrict
    {environment : BooleanEnvironment} {decision : BooleanDecision α}
    (hdecision : ResolvedBy environment decision)
    (selectedVariable : Name) (selectedValue : Bool)
    (hselected : environment.statusForVariable selectedVariable = none)
    : ResolvedBy (environment.assign selectedVariable selectedValue)
        (decision.restrict selectedVariable selectedValue) := by
  induction hdecision with
  | leaf => exact .leaf _ _
  | split environment variableName onFalse onTrue hstatus hfalse htrue ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split <;> rename_i hequal
      · subst variableName
        cases selectedValue
        · exact hfalse.restrict_of_known selectedVariable false false
            (BooleanEnvironment.statusForVariable_assign_self environment
              selectedVariable false hstatus)
        · exact htrue.restrict_of_known selectedVariable true true
            (BooleanEnvironment.statusForVariable_assign_self environment
              selectedVariable true hstatus)
      · have hne : variableName ≠ selectedVariable := hequal
        have hselectedFalse
            : (environment.assign variableName false).statusForVariable selectedVariable
              = none := by
          rw [BooleanEnvironment.statusForVariable_assign_of_ne environment variableName
            false (Ne.symm hne), hselected]
        have hselectedTrue
            : (environment.assign variableName true).statusForVariable selectedVariable
              = none := by
          rw [BooleanEnvironment.statusForVariable_assign_of_ne environment variableName
            true (Ne.symm hne), hselected]
        apply ResolvedBy.split
        · rw [BooleanEnvironment.statusForVariable_assign_of_ne environment
            selectedVariable selectedValue hne, hstatus]
        · apply ResolvedBy.congr
            (BooleanEnvironment.assign_comm_statusForVariable environment variableName false
              selectedVariable selectedValue hne)
          exact ihFalse hselectedFalse
        · apply ResolvedBy.congr
            (BooleanEnvironment.assign_comm_statusForVariable environment variableName true
              selectedVariable selectedValue hne)
          exact ihTrue hselectedTrue
  | join environment left right hleft hright ihLeft ihRight =>
      exact .join _ _ _ (ihLeft hselected) (ihRight hselected)

private def proofNodeCount : BooleanDecision α -> Nat
  | .leaf _summary => 1
  | .split _variableName onFalse onTrue =>
      1 + proofNodeCount onFalse + proofNodeCount onTrue
  | .join left right => 1 + proofNodeCount left + proofNodeCount right

private theorem proofNodeCount_restrict_le (selectedVariable : Name)
    (selectedValue : Bool) (decision : BooleanDecision α)
    : proofNodeCount (decision.restrict selectedVariable selectedValue)
      ≤ proofNodeCount decision := by
  induction decision with
  | leaf => simp [BooleanDecision.restrict, proofNodeCount]
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split
      · cases selectedValue <;> simp_all [proofNodeCount] <;> omega
      · simp only [proofNodeCount]
        omega
  | join left right ihLeft ihRight =>
      simp only [BooleanDecision.restrict, proofNodeCount]
      omega

private theorem ResolvedBy.zipWith
    (variableOrder : BooleanVariableNames) (operation : α -> β -> γ)
    {environment : BooleanEnvironment}
    {left : BooleanDecision α} {right : BooleanDecision β}
    (hleft : ResolvedBy environment left) (hright : ResolvedBy environment right)
    : ResolvedBy environment
        (BooleanDecision.zipWith variableOrder operation left right) := by
  cases hleft with
  | leaf =>
      simp only [BooleanDecision.zipWith]
      exact hright.map _
  | @split _ leftVariable leftFalse leftTrue hleftStatus hleftFalse hleftTrue =>
      cases hright with
      | leaf =>
          simp only [BooleanDecision.zipWith]
          exact (ResolvedBy.split _ _ _ _ hleftStatus hleftFalse hleftTrue).map _
      | @split _ rightVariable rightFalse rightTrue hrightStatus hrightFalse hrightTrue =>
          simp only [BooleanDecision.zipWith]
          split <;> rename_i hequal
          · subst rightVariable
            exact .split _ leftVariable _ _ hleftStatus
              (ResolvedBy.zipWith variableOrder operation hleftFalse hrightFalse)
              (ResolvedBy.zipWith variableOrder operation hleftTrue hrightTrue)
          · split
            · exact .split _ leftVariable _ _ hleftStatus
                (ResolvedBy.zipWith variableOrder operation hleftFalse
                  ((ResolvedBy.split _ _ _ _ hrightStatus hrightFalse
                    hrightTrue).restrict leftVariable false hleftStatus))
                (ResolvedBy.zipWith variableOrder operation hleftTrue
                  ((ResolvedBy.split _ _ _ _ hrightStatus hrightFalse
                    hrightTrue).restrict leftVariable true hleftStatus))
            · exact .split _ rightVariable _ _ hrightStatus
                (ResolvedBy.zipWith variableOrder operation
                  ((ResolvedBy.split _ _ _ _ hleftStatus hleftFalse
                    hleftTrue).restrict rightVariable false hrightStatus)
                  hrightFalse)
                (ResolvedBy.zipWith variableOrder operation
                  ((ResolvedBy.split _ _ _ _ hleftStatus hleftFalse
                    hleftTrue).restrict rightVariable true hrightStatus)
                  hrightTrue)
      | @join _ rightFirst rightSecond hrightFirst hrightSecond =>
          simp only [BooleanDecision.zipWith]
          exact .join _ _ _
            (ResolvedBy.zipWith variableOrder operation
              (.split _ _ _ _ hleftStatus hleftFalse hleftTrue) hrightFirst)
            (ResolvedBy.zipWith variableOrder operation
              (.split _ _ _ _ hleftStatus hleftFalse hleftTrue) hrightSecond)
  | @join _ leftFirst leftSecond hleftFirst hleftSecond =>
      cases hright with
      | leaf =>
          simp only [BooleanDecision.zipWith]
          exact (ResolvedBy.join _ _ _ hleftFirst hleftSecond).map _
      | @split _ rightVariable rightFalse rightTrue hrightStatus hrightFalse hrightTrue =>
          simp only [BooleanDecision.zipWith]
          exact .join _ _ _
            (ResolvedBy.zipWith variableOrder operation hleftFirst
              (.split _ _ _ _ hrightStatus hrightFalse hrightTrue))
            (ResolvedBy.zipWith variableOrder operation hleftSecond
              (.split _ _ _ _ hrightStatus hrightFalse hrightTrue))
      | @join _ rightFirst rightSecond hrightFirst hrightSecond =>
          simp only [BooleanDecision.zipWith]
          exact .join _ _ _
            (ResolvedBy.zipWith variableOrder operation hleftFirst
              (.join _ _ _ hrightFirst hrightSecond))
            (ResolvedBy.zipWith variableOrder operation hleftSecond
              (.join _ _ _ hrightFirst hrightSecond))
termination_by proofNodeCount left + proofNodeCount right
decreasing_by
  all_goals subst_vars
  all_goals simp only [proofNodeCount]
  all_goals try omega
  all_goals
    have hrightFalse := proofNodeCount_restrict_le leftVariable false
      (.split rightVariable rightFalse rightTrue)
    have hrightTrue := proofNodeCount_restrict_le leftVariable true
      (.split rightVariable rightFalse rightTrue)
    have hleftFalse := proofNodeCount_restrict_le rightVariable false
      (.split leftVariable leftFalse leftTrue)
    have hleftTrue := proofNodeCount_restrict_le rightVariable true
      (.split leftVariable leftFalse leftTrue)
    simp only [proofNodeCount] at hrightFalse hrightTrue hleftFalse hleftTrue
    omega

private theorem ResolvedBy.combineMap (algebra : Algebra)
    (variableOrder : BooleanVariableNames) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (environment : BooleanEnvironment)
    (hitems : ∀ item hitem, ResolvedBy environment (summarize item hitem))
    : ResolvedBy environment
        (BooleanDecision.combineMap algebra variableOrder items summarize) := by
  induction items with
  | nil => simpa [BooleanDecision.combineMap] using
      (ResolvedBy.leaf environment algebra.empty)
  | cons item rest ih =>
      rw [BooleanDecision.combineMap]
      apply ResolvedBy.zipWith variableOrder algebra.combine
      · exact hitems item (by simp)
      · exact ih
          (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hitems candidate (by simp [hcandidate]))

private theorem ResolvedBy.joinMap (algebra : Algebra) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (environment : BooleanEnvironment)
    (hitems : ∀ item hitem, ResolvedBy environment (summarize item hitem))
    : ResolvedBy environment (BooleanDecision.joinMap algebra items summarize) := by
  cases items with
  | nil => simpa [BooleanDecision.joinMap] using
      (ResolvedBy.leaf environment algebra.empty)
  | cons item rest =>
      cases rest with
      | nil => simpa [BooleanDecision.joinMap] using hitems item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap]
          exact .join _ _ _
            (hitems item (by simp))
            (ResolvedBy.joinMap algebra (next :: tail)
              (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
              environment
              (fun candidate hcandidate => hitems candidate (by simp [hcandidate])))
termination_by items.length

private theorem ResolvedBy.compact (join : α -> α -> α)
    {environment : BooleanEnvironment} {decision : BooleanDecision α}
    (hdecision : ResolvedBy environment decision)
    : ResolvedBy environment (decision.compact join) := by
  induction hdecision with
  | leaf => exact .leaf _ _
  | split environment variableName onFalse onTrue hstatus _ _ ihFalse ihTrue =>
      exact .split _ _ _ _ hstatus ihFalse ihTrue
  | join environment left right _ _ ihLeft ihRight =>
      simp only [BooleanDecision.compact]
      cases hleft : left.compact join <;> cases hright : right.compact join <;>
        simp only [BooleanDecision.joinCases]
      all_goals first
        | exact .leaf _ _
        | exact .join _ _ _ (by simpa [hleft] using ihLeft)
            (by simpa [hright] using ihRight)

private theorem collapse_iff_exists_matches_evaluate
    (semantics : OutcomeSemantics.{u})
    {environment : BooleanEnvironment}
    {decision : BooleanDecision (OutcomeSet semantics.Summary)}
    (hdecision : ResolvedBy environment decision) (outcome : semantics.Summary)
    : decision.collapse (OutcomeSemantics.proofAlgebra semantics) outcome
      ↔ ∃ assignment,
          BooleanEnvironment.Matches environment assignment
          ∧ evaluateOutcome assignment decision outcome := by
  induction hdecision with
  | leaf environment outcomes =>
      simp only [BooleanDecision.collapse, evaluateOutcome]
      constructor
      · intro houtcome
        obtain ⟨assignment, hmatches⟩ := BooleanEnvironment.exists_matches environment
        exact ⟨assignment, hmatches, houtcome⟩
      · rintro ⟨_assignment, _hmatches, houtcome⟩
        exact houtcome
  | split environment variableName onFalse onTrue hstatus _ _ ihFalse ihTrue =>
      change (onFalse.collapse (OutcomeSemantics.proofAlgebra semantics) outcome
                ∨ onTrue.collapse (OutcomeSemantics.proofAlgebra semantics) outcome)
              ↔ ∃ assignment,
                  BooleanEnvironment.Matches environment assignment
                  ∧ (if assignment variableName then
                        evaluateOutcome assignment onTrue
                      else
                        evaluateOutcome assignment onFalse)
                      outcome
      constructor
      · intro houtcome
        rcases houtcome with hfalse | htrue
        · obtain ⟨assignment, hmatches, hevaluate⟩ := ihFalse.mp hfalse
          have hparts :=
            (BooleanEnvironment.matches_assign_iff environment assignment variableName
              false hstatus).mp hmatches
          exact ⟨assignment, hparts.1, by simpa [hparts.2] using hevaluate⟩
        · obtain ⟨assignment, hmatches, hevaluate⟩ := ihTrue.mp htrue
          have hparts :=
            (BooleanEnvironment.matches_assign_iff environment assignment variableName
              true hstatus).mp hmatches
          exact ⟨assignment, hparts.1, by simpa [hparts.2] using hevaluate⟩
      · rintro ⟨assignment, hmatches, hevaluate⟩
        by_cases hvalue : assignment variableName
        · apply Or.inr
          apply ihTrue.mpr
          exact ⟨assignment,
            (BooleanEnvironment.matches_assign_iff environment assignment variableName
              true hstatus).mpr ⟨hmatches, hvalue⟩,
            by simpa [hvalue] using hevaluate⟩
        · apply Or.inl
          apply ihFalse.mpr
          exact ⟨assignment,
            (BooleanEnvironment.matches_assign_iff environment assignment variableName
              false hstatus).mpr ⟨hmatches, Bool.eq_false_iff.mpr hvalue⟩,
            by simpa [hvalue] using hevaluate⟩
  | join environment left right _ _ ihLeft ihRight =>
      change (left.collapse (OutcomeSemantics.proofAlgebra semantics) outcome
                ∨ right.collapse (OutcomeSemantics.proofAlgebra semantics) outcome)
              ↔ ∃ assignment,
                  BooleanEnvironment.Matches environment assignment
                  ∧ (evaluateOutcome assignment left outcome
                      ∨ evaluateOutcome assignment right outcome)
      constructor
      · intro houtcome
        rcases houtcome with hleft | hright
        · obtain ⟨assignment, hmatches, hevaluate⟩ := ihLeft.mp hleft
          exact ⟨assignment, hmatches, Or.inl hevaluate⟩
        · obtain ⟨assignment, hmatches, hevaluate⟩ := ihRight.mp hright
          exact ⟨assignment, hmatches, Or.inr hevaluate⟩
      · rintro ⟨assignment, hmatches, hevaluate⟩
        rcases hevaluate with hleft | hright
        · exact Or.inl (ihLeft.mpr ⟨assignment, hmatches, hleft⟩)
        · exact Or.inr (ihRight.mpr ⟨assignment, hmatches, hright⟩)

private theorem evaluateOutcome_restrict
    (assignment : BooleanAssignment) (selectedVariable : Name) (selectedValue : Bool)
    (decision : BooleanDecision (OutcomeSet α))
    (hvalue : assignment selectedVariable = selectedValue)
    : evaluateOutcome assignment (decision.restrict selectedVariable selectedValue)
      = evaluateOutcome assignment decision := by
  induction decision with
  | leaf => rfl
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.restrict, evaluateOutcome]
      split <;> rename_i hequal
      · subst variableName
        cases selectedValue <;> simp_all
      · by_cases hbranch : assignment variableName
        · simp only [evaluateOutcome, hbranch, ↓reduceIte, ihTrue]
        · simp only [evaluateOutcome, hbranch, Bool.false_eq_true, ↓reduceIte,
            ihFalse]
  | join left right ihLeft ihRight =>
      simp only [BooleanDecision.restrict, evaluateOutcome, ihLeft, ihRight]

private theorem evaluateOutcome_map_bind
    (assignment : BooleanAssignment) (decision : BooleanDecision (OutcomeSet α))
    (next : α -> OutcomeSet β)
    : evaluateOutcome assignment (decision.map fun source => OutcomeSet.bind source next)
      = OutcomeSet.bind (evaluateOutcome assignment decision) next := by
  induction decision with
  | leaf => rfl
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.map, evaluateOutcome]
      split
      · exact ihTrue
      · exact ihFalse
  | join left right ihLeft ihRight =>
      simp only [BooleanDecision.map, evaluateOutcome, ihLeft, ihRight]
      funext outcome
      apply propext
      constructor
      · rintro (houtcome | houtcome)
        · rcases houtcome with ⟨input, hinput, hnext⟩
          exact ⟨input, Or.inl hinput, hnext⟩
        · rcases houtcome with ⟨input, hinput, hnext⟩
          exact ⟨input, Or.inr hinput, hnext⟩
      · rintro ⟨input, hinput, hnext⟩
        rcases hinput with hleft | hright
        · exact Or.inl ⟨input, hleft, hnext⟩
        · exact Or.inr ⟨input, hright, hnext⟩

private theorem evaluateOutcome_map_combine_left
    (semantics : OutcomeSemantics.{u}) (assignment : BooleanAssignment)
    (left : OutcomeSet semantics.Summary)
    (decision : BooleanDecision (OutcomeSet semantics.Summary))
    : evaluateOutcome assignment
        (decision.map (OutcomeSet.combine semantics.combine left))
      = OutcomeSet.combine semantics.combine left
          (evaluateOutcome assignment decision) := by
  induction decision with
  | leaf => rfl
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.map, evaluateOutcome]
      split
      · exact ihTrue
      · exact ihFalse
  | join first second ihFirst ihSecond =>
      simp only [BooleanDecision.map, evaluateOutcome, ihFirst, ihSecond]
      funext outcome
      apply propext
      constructor
      · rintro (houtcome | houtcome)
        · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
          exact ⟨l, r, hl, Or.inl hr, rfl⟩
        · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
          exact ⟨l, r, hl, Or.inr hr, rfl⟩
      · rintro ⟨l, r, hl, hr, rfl⟩
        rcases hr with hr | hr
        · exact Or.inl ⟨l, r, hl, hr, rfl⟩
        · exact Or.inr ⟨l, r, hl, hr, rfl⟩

private theorem evaluateOutcome_map_combine_right
    (semantics : OutcomeSemantics.{u}) (assignment : BooleanAssignment)
    (decision : BooleanDecision (OutcomeSet semantics.Summary))
    (right : OutcomeSet semantics.Summary)
    : evaluateOutcome assignment
        (decision.map fun left => OutcomeSet.combine semantics.combine left right)
      = OutcomeSet.combine semantics.combine
          (evaluateOutcome assignment decision) right := by
  induction decision with
  | leaf => rfl
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.map, evaluateOutcome]
      split
      · exact ihTrue
      · exact ihFalse
  | join first second ihFirst ihSecond =>
      simp only [BooleanDecision.map, evaluateOutcome, ihFirst, ihSecond]
      funext outcome
      apply propext
      constructor
      · rintro (houtcome | houtcome)
        · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
          exact ⟨l, r, Or.inl hl, hr, rfl⟩
        · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
          exact ⟨l, r, Or.inr hl, hr, rfl⟩
      · rintro ⟨l, r, hl, hr, rfl⟩
        rcases hl with hl | hl
        · exact Or.inl ⟨l, r, hl, hr, rfl⟩
        · exact Or.inr ⟨l, r, hl, hr, rfl⟩

private theorem evaluateOutcome_zipWith_combine
    (semantics : OutcomeSemantics.{u}) (variableOrder : BooleanVariableNames)
    (assignment : BooleanAssignment)
    (left right : BooleanDecision (OutcomeSet semantics.Summary))
    : evaluateOutcome assignment
        (BooleanDecision.zipWith variableOrder
          (OutcomeSet.combine semantics.combine) left right)
      = OutcomeSet.combine semantics.combine
          (evaluateOutcome assignment left) (evaluateOutcome assignment right) := by
  cases left with
  | leaf leftOutcomes =>
      simp only [BooleanDecision.zipWith]
      exact evaluateOutcome_map_combine_left semantics assignment leftOutcomes right
  | split leftVariable leftFalse leftTrue =>
      cases right with
      | leaf rightOutcomes =>
          simp only [BooleanDecision.zipWith]
          exact evaluateOutcome_map_combine_right semantics assignment
            (.split leftVariable leftFalse leftTrue) rightOutcomes
      | split rightVariable rightFalse rightTrue =>
          simp only [BooleanDecision.zipWith, evaluateOutcome]
          split <;> rename_i hequal
          · subst rightVariable
            by_cases hvalue : assignment leftVariable
            · simp only [evaluateOutcome, hvalue, ↓reduceIte]
              exact evaluateOutcome_zipWith_combine semantics variableOrder assignment
                leftTrue rightTrue
            · simp only [evaluateOutcome, hvalue, Bool.false_eq_true, ↓reduceIte]
              exact evaluateOutcome_zipWith_combine semantics variableOrder assignment
                leftFalse rightFalse
          · split
            · by_cases hvalue : assignment leftVariable
              · simp only [evaluateOutcome, hvalue, ↓reduceIte]
                rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment]
                rw [evaluateOutcome_restrict assignment leftVariable true _ hvalue]
                rw [evaluateOutcome]
              · simp only [evaluateOutcome, hvalue, Bool.false_eq_true, ↓reduceIte]
                rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment]
                rw [evaluateOutcome_restrict assignment leftVariable false _
                  (Bool.eq_false_iff.mpr hvalue)]
                rw [evaluateOutcome]
            · by_cases hvalue : assignment rightVariable
              · simp only [evaluateOutcome, hvalue, ↓reduceIte]
                rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment]
                rw [evaluateOutcome_restrict assignment rightVariable true _ hvalue]
                rw [evaluateOutcome]
              · simp only [evaluateOutcome, hvalue, Bool.false_eq_true, ↓reduceIte]
                rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment]
                rw [evaluateOutcome_restrict assignment rightVariable false _
                  (Bool.eq_false_iff.mpr hvalue)]
                rw [evaluateOutcome]
      | join rightFirst rightSecond =>
          simp only [BooleanDecision.zipWith, evaluateOutcome]
          rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment,
            evaluateOutcome_zipWith_combine semantics variableOrder assignment]
          funext outcome
          apply propext
          constructor
          · rintro (houtcome | houtcome)
            · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
              exact ⟨l, r, hl, Or.inl hr, rfl⟩
            · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
              exact ⟨l, r, hl, Or.inr hr, rfl⟩
          · rintro ⟨l, r, hl, hr, rfl⟩
            rcases hr with hr | hr
            · exact Or.inl ⟨l, r, hl, hr, rfl⟩
            · exact Or.inr ⟨l, r, hl, hr, rfl⟩
  | join leftFirst leftSecond =>
      cases right with
      | leaf rightOutcomes =>
          simp only [BooleanDecision.zipWith]
          exact evaluateOutcome_map_combine_right semantics assignment
            (.join leftFirst leftSecond) rightOutcomes
      | split rightVariable rightFalse rightTrue =>
          rw [show evaluateOutcome assignment (.join leftFirst leftSecond)
            = OutcomeSet.union (evaluateOutcome assignment leftFirst)
                (evaluateOutcome assignment leftSecond) from rfl]
          simp only [BooleanDecision.zipWith]
          change OutcomeSet.union
              (evaluateOutcome assignment
                (BooleanDecision.zipWith variableOrder
                  (OutcomeSet.combine semantics.combine) leftFirst
                  (.split rightVariable rightFalse rightTrue)))
              (evaluateOutcome assignment
                (BooleanDecision.zipWith variableOrder
                  (OutcomeSet.combine semantics.combine) leftSecond
                  (.split rightVariable rightFalse rightTrue)))
            = _
          rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment,
            evaluateOutcome_zipWith_combine semantics variableOrder assignment]
          funext outcome
          apply propext
          constructor
          · rintro (houtcome | houtcome)
            · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
              exact ⟨l, r, Or.inl hl, hr, rfl⟩
            · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
              exact ⟨l, r, Or.inr hl, hr, rfl⟩
          · rintro ⟨l, r, hl, hr, rfl⟩
            rcases hl with hl | hl
            · exact Or.inl ⟨l, r, hl, hr, rfl⟩
            · exact Or.inr ⟨l, r, hl, hr, rfl⟩
      | join rightFirst rightSecond =>
          rw [show evaluateOutcome assignment (.join leftFirst leftSecond)
            = OutcomeSet.union (evaluateOutcome assignment leftFirst)
                (evaluateOutcome assignment leftSecond) from rfl]
          simp only [BooleanDecision.zipWith]
          change OutcomeSet.union
              (evaluateOutcome assignment
                (BooleanDecision.zipWith variableOrder
                  (OutcomeSet.combine semantics.combine) leftFirst
                  (.join rightFirst rightSecond)))
              (evaluateOutcome assignment
                (BooleanDecision.zipWith variableOrder
                  (OutcomeSet.combine semantics.combine) leftSecond
                  (.join rightFirst rightSecond)))
            = _
          rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment,
            evaluateOutcome_zipWith_combine semantics variableOrder assignment]
          funext outcome
          apply propext
          constructor
          · rintro (houtcome | houtcome)
            · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
              exact ⟨l, r, Or.inl hl, hr, rfl⟩
            · rcases houtcome with ⟨l, r, hl, hr, rfl⟩
              exact ⟨l, r, Or.inr hl, hr, rfl⟩
          · rintro ⟨l, r, hl, hr, rfl⟩
            rcases hl with hl | hl
            · exact Or.inl ⟨l, r, hl, hr, rfl⟩
            · exact Or.inr ⟨l, r, hl, hr, rfl⟩
termination_by proofNodeCount left + proofNodeCount right
decreasing_by
  all_goals subst_vars
  all_goals simp only [proofNodeCount]
  all_goals try omega
  all_goals
    have hrightFalse := proofNodeCount_restrict_le leftVariable false
      (.split rightVariable rightFalse rightTrue)
    have hrightTrue := proofNodeCount_restrict_le leftVariable true
      (.split rightVariable rightFalse rightTrue)
    have hleftFalse := proofNodeCount_restrict_le rightVariable false
      (.split leftVariable leftFalse leftTrue)
    have hleftTrue := proofNodeCount_restrict_le rightVariable true
      (.split leftVariable leftFalse leftTrue)
    simp only [proofNodeCount] at hrightFalse hrightTrue hleftFalse hleftTrue
    omega

private theorem evaluateOutcome_combineMap
    (semantics : OutcomeSemantics.{u}) (variableOrder : BooleanVariableNames)
    (assignment : BooleanAssignment) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision (OutcomeSet semantics.Summary))
    : evaluateOutcome assignment
        (BooleanDecision.combineMap (OutcomeSemantics.proofAlgebra semantics)
          variableOrder items summarize)
      = TreeSummary.combineMap (OutcomeSemantics.proofAlgebra semantics) items
          fun item hitem => evaluateOutcome assignment (summarize item hitem) := by
  induction items with
  | nil =>
      rw [BooleanDecision.combineMap.eq_def, TreeSummary.combineMap]
      rfl
  | cons item rest ih =>
      rw [BooleanDecision.combineMap.eq_def, TreeSummary.combineMap]
      rw [evaluateOutcome_zipWith_combine semantics variableOrder assignment]
      rw [ih
        (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))]

private theorem evaluateOutcome_joinMap_of_mem
    (semantics : OutcomeSemantics.{u}) (assignment : BooleanAssignment)
    {items : List α}
    (summarize : ∀ item, item ∈ items -> BooleanDecision (OutcomeSet semantics.Summary))
    {item : α} {outcome : semantics.Summary}
    (hitem : item ∈ items)
    (houtcome : evaluateOutcome assignment (summarize item hitem) outcome)
    : evaluateOutcome assignment
        (BooleanDecision.joinMap (OutcomeSemantics.proofAlgebra semantics) items
          summarize)
        outcome := by
  induction items generalizing item with
  | nil => simp at hitem
  | cons head rest ih =>
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hitem
          subst head
          rw [BooleanDecision.joinMap.eq_def]
          exact houtcome
      | cons next tail =>
          simp only [List.mem_cons] at hitem
          rw [BooleanDecision.joinMap.eq_def, evaluateOutcome]
          rcases hitem with rfl | hitem
          · exact Or.inl houtcome
          · exact Or.inr
              (ih
                (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
                (by simpa using hitem) houtcome)

private theorem evaluateOutcome_joinMap_cases
    (semantics : OutcomeSemantics.{u}) (assignment : BooleanAssignment)
    {items : List α}
    (summarize : ∀ item, item ∈ items -> BooleanDecision (OutcomeSet semantics.Summary))
    {outcome : semantics.Summary}
    (houtcome
      : evaluateOutcome assignment
          (BooleanDecision.joinMap (OutcomeSemantics.proofAlgebra semantics) items
            summarize)
          outcome)
    : (items = [] ∧ outcome = semantics.empty)
      ∨ ∃ item hitem, evaluateOutcome assignment (summarize item hitem) outcome := by
  induction items with
  | nil =>
      exact Or.inl ⟨rfl, by
        rw [BooleanDecision.joinMap.eq_def, evaluateOutcome] at houtcome
        simpa [OutcomeSet.singleton] using houtcome⟩
  | cons head rest ih =>
      cases rest with
      | nil =>
          rw [BooleanDecision.joinMap.eq_def] at houtcome
          exact Or.inr ⟨head, by simp, houtcome⟩
      | cons next tail =>
          rw [BooleanDecision.joinMap.eq_def, evaluateOutcome] at houtcome
          rcases houtcome with hhead | hrest
          · exact Or.inr ⟨head, by simp, hhead⟩
          · rcases ih
              (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
              hrest with hempty | ⟨item, hitem, hitemOutcome⟩
            · simp at hempty
            · exact Or.inr ⟨item, by simp [hitem], hitemOutcome⟩

end Internal.BooleanDecision

private theorem CaseCursor.summarizeDecisionWithPruning_nil_optimality
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (environment : BooleanEnvironment) (pruningValues : VariableValues)
    (hbranches : cursor.pendingBranches = [])
    : cursor.summarizeDecisionWithPruning algebra schema variableOrder
        inheritedBooleanCondition caseCondition possibleTypes environment pruningValues
      = CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder
          (cursor.fieldGroups
            (Internal.extendBooleanCondition inheritedBooleanCondition caseCondition)
            possibleTypes)
          environment pruningValues := by
  rcases cursor with ⟨namedFields, pendingBranches⟩
  change pendingBranches = [] at hbranches
  subst pendingBranches
  rw [CaseCursor.summarizeDecisionWithPruning.eq_1]

private theorem CaseCursor.summarizeDecisionWithPruning_cons_optimality
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (environment : BooleanEnvironment) (pruningValues : VariableValues)
    (branch : Branch Tree) (rest : List (Branch Tree))
    (hbranches : cursor.pendingBranches = branch :: rest)
    : cursor.summarizeDecisionWithPruning algebra schema variableOrder
        inheritedBooleanCondition caseCondition possibleTypes environment pruningValues
      = match branch.condition with
        | .typeCondition _typeName =>
            BooleanDecision.joinMap algebra
              (possibleTypeRegions possibleTypes [branch.body.condition.possibleTypes])
              fun region _hregion =>
                if possibleTypesSubset region branch.body.condition.possibleTypes then
                  (cursor.selectBranch branch.body rest).summarizeDecisionWithPruning
                    algebra schema variableOrder inheritedBooleanCondition caseCondition
                    region environment pruningValues
                else
                  (cursor.skipBranch rest).summarizeDecisionWithPruning algebra schema
                    variableOrder inheritedBooleanCondition caseCondition region
                    environment pruningValues
        | .booleanLiteral literal =>
            match environment.statusForVariable literal.variableName with
            | some value =>
                let selectedLiteral :=
                  if value then
                    BooleanLiteral.positive literal.variableName
                  else
                    BooleanLiteral.negative literal.variableName
                (cursor.resolveBooleanBranch branch.body rest literal
                  value).summarizeDecisionWithPruning
                  algebra schema variableOrder inheritedBooleanCondition
                  (selectedLiteral :: caseCondition) possibleTypes environment
                  pruningValues
            | none =>
                .split literal.variableName
                  ((cursor.resolveBooleanBranch branch.body rest literal
                      false).summarizeDecisionWithPruning
                    algebra schema variableOrder inheritedBooleanCondition
                    (.negative literal.variableName :: caseCondition) possibleTypes
                    (environment.assign literal.variableName false) pruningValues)
                  ((cursor.resolveBooleanBranch branch.body rest literal
                      true).summarizeDecisionWithPruning
                    algebra schema variableOrder inheritedBooleanCondition
                    (.positive literal.variableName :: caseCondition) possibleTypes
                    (environment.assign literal.variableName true) pruningValues) := by
  rcases cursor with ⟨namedFields, pendingBranches⟩
  change pendingBranches = branch :: rest at hbranches
  subst pendingBranches
  rw [CaseCursor.summarizeDecisionWithPruning.eq_1]
  rfl

private theorem CaseCursor.summarizeDecisionWithPruning_resolvedBy
    (algebra : Algebra) (schema : Schema) (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (environment : BooleanEnvironment) (pruningValues : VariableValues)
    : BooleanDecision.ResolvedBy environment
        (cursor.summarizeDecisionWithPruning algebra schema variableOrder
          inheritedBooleanCondition caseCondition possibleTypes environment
          pruningValues) := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema pruningValues
    (motive1 := fun inherited caseCondition cursor possibleTypes environment =>
      BooleanDecision.ResolvedBy environment
        (cursor.summarizeDecisionWithPruning algebra schema variableOrder inherited
          caseCondition possibleTypes environment pruningValues))
    (motive2 := fun groups environment =>
      BooleanDecision.ResolvedBy environment
        (CaseCursor.summarizeFieldGroupsDecisionWithPruning algebra schema variableOrder
          groups environment pruningValues))
    (motive3 := fun group parentTypes environment =>
      BooleanDecision.ResolvedBy environment
        (CaseCursor.summarizeChildTypesDecisionWithPruning algebra schema variableOrder group
          parentTypes environment pruningValues))
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment hbranches ih
    rw [CaseCursor.summarizeDecisionWithPruning_nil_optimality algebra schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues hbranches]
    exact ih
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest hbranches
      typeName hcondition ihSelect ihSkip
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality algebra schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches]
    simp only [hcondition]
    apply BooleanDecision.ResolvedBy.joinMap algebra _ _ environment
    intro region hregion
    split
    · exact ihSelect region
    · exact ihSkip region
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest hbranches
      literal hcondition value hstatus selectedLiteral ih
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality algebra schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches]
    simp only [hcondition, hstatus]
    exact ih
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest hbranches
      literal hcondition hstatus ihFalse ihTrue
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality algebra schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues branch rest
      hbranches]
    simp only [hcondition, hstatus]
    exact .split environment literal.variableName _ _ hstatus ihFalse ihTrue
  case case5 =>
    intro groups environment ih
    simp only [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1]
    apply BooleanDecision.ResolvedBy.combineMap algebra variableOrder groups _ environment
    intro group hgroup
    exact (ih group hgroup).map _
  case case6 =>
    intro group parentTypes environment ih
    simp only [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.ResolvedBy.joinMap algebra parentTypes _ environment
    intro childParentType hparentType
    exact ih childParentType

private theorem summarizeConditionTreeDecision_resolvedBy
    (algebra : Algebra) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (variableOrder : BooleanVariableNames) (environment : BooleanEnvironment)
    : BooleanDecision.ResolvedBy environment
        (Internal.summarizeConditionTreeDecision algebra schema inheritedBooleanCondition
          tree variableOrder environment) := by
  unfold Internal.summarizeConditionTreeDecision
  apply BooleanDecision.ResolvedBy.compact
  exact CaseCursor.summarizeDecisionWithPruning_resolvedBy algebra schema variableOrder
    inheritedBooleanCondition [] (.ofConditionTree tree) tree.condition.possibleTypes
    environment environment.pruningValues

namespace CaseCursor

private theorem ContextOutcome.toEvaluate
    {semantics : OutcomeSemantics.{u}} {schema : Schema}
    {assignment : BooleanAssignment} {environment : BooleanEnvironment}
    {inheritedBooleanCondition caseCondition : List BooleanLiteral}
    {cursor : CaseCursor} {possibleTypes : PossibleTypeRegion}
    {outcome : semantics.Summary}
    (h
      : ContextOutcome semantics schema assignment environment
          inheritedBooleanCondition caseCondition cursor possibleTypes outcome)
    (variableOrder : BooleanVariableNames)
    : BooleanDecision.evaluateOutcome assignment
        (cursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics)
          schema variableOrder inheritedBooleanCondition caseCondition possibleTypes
          environment environment.pruningValues)
        outcome := by
  apply @ContextOutcome.rec semantics schema assignment
    (fun environment inherited caseCondition cursor possibleTypes
        outcome _h =>
      BooleanDecision.evaluateOutcome assignment
        (cursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics)
          schema variableOrder inherited caseCondition possibleTypes environment
          environment.pruningValues)
        outcome)
    (fun environment groups outcome _h =>
      BooleanDecision.evaluateOutcome assignment
        (CaseCursor.summarizeFieldGroupsDecisionWithPruning
          (OutcomeSemantics.proofAlgebra semantics) schema variableOrder groups environment
          environment.pruningValues)
        outcome)
    (fun environment group parentTypes outcome _h =>
      BooleanDecision.evaluateOutcome assignment
        (CaseCursor.summarizeChildTypesDecisionWithPruning
          (OutcomeSemantics.proofAlgebra semantics) schema variableOrder group parentTypes
          environment environment.pruningValues)
        outcome)
  case noTypeRegion =>
    intro environment inherited caseCondition cursor possibleTypes branch rest
      typeName hbranches hcondition hregions
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment environment.pruningValues
      branch rest hbranches]
    simp only [hcondition]
    rw [hregions, BooleanDecision.joinMap.eq_def, BooleanDecision.evaluateOutcome]
    simp [OutcomeSet.singleton]
  case selectTypeRegion =>
    intro environment inherited caseCondition cursor possibleTypes branch rest
      typeName region outcome hbranches hcondition hregion hselected _houtcome ih
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment environment.pruningValues
      branch rest hbranches]
    simp only [hcondition]
    apply BooleanDecision.evaluateOutcome_joinMap_of_mem semantics assignment _ hregion
    simp only [hselected, ↓reduceIte]
    exact ih
  case skipTypeRegion =>
    intro environment inherited caseCondition cursor possibleTypes branch rest
      typeName region outcome hbranches hcondition hregion hskipped _houtcome ih
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment environment.pruningValues
      branch rest hbranches]
    simp only [hcondition]
    apply BooleanDecision.evaluateOutcome_joinMap_of_mem semantics assignment _ hregion
    simp only [hskipped, Bool.false_eq_true, ↓reduceIte]
    exact ih
  case knownBoolean =>
    intro environment inherited caseCondition cursor possibleTypes branch rest
      literal value outcome hbranches hcondition hstatus _houtcome ih
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment environment.pruningValues
      branch rest hbranches]
    simp only [hcondition, hstatus]
    exact ih
  case splitBoolean =>
    intro environment inherited caseCondition cursor possibleTypes branch rest
      literal outcome hbranches hcondition hstatus _houtcome ih
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment environment.pruningValues
      branch rest hbranches]
    simp only [hcondition, hstatus, BooleanDecision.evaluateOutcome]
    rw [BooleanEnvironment.pruningValues_assign] at ih
    change BooleanDecision.evaluateOutcome assignment
      (CaseCursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics)
        schema variableOrder inherited
        ((if assignment literal.variableName then
            BooleanLiteral.positive literal.variableName
          else
            BooleanLiteral.negative literal.variableName) :: caseCondition)
        (cursor.resolveBooleanBranch branch.body rest literal
          (assignment literal.variableName))
        possibleTypes
        (environment.assign literal.variableName (assignment literal.variableName))
        environment.pruningValues)
      outcome at ih
    by_cases hvalue : assignment literal.variableName
    · simpa [hvalue] using ih
    · simpa [hvalue] using ih
  case fields =>
    intro environment inherited caseCondition cursor possibleTypes outcome
      hbranches _houtcome ih
    rw [CaseCursor.summarizeDecisionWithPruning_nil_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment environment.pruningValues
      hbranches]
    exact ih
  case nil =>
    intro environment
    rw [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1,
      BooleanDecision.evaluateOutcome_combineMap, TreeSummary.combineMap]
    simp [OutcomeSet.singleton]
  case cons =>
    intro environment group rest children fieldOutcome restOutcome _hchildren
      hfield _hrest ihChildren ihRest
    rw [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1,
      BooleanDecision.evaluateOutcome_combineMap, TreeSummary.combineMap]
    change OutcomeSet.combine semantics.combine
      (BooleanDecision.evaluateOutcome assignment
        ((CaseCursor.summarizeChildTypesDecisionWithPruning
          (OutcomeSemantics.proofAlgebra semantics) schema variableOrder group
          (childParentTypes schema group) environment environment.pruningValues).map
          fun source => OutcomeSet.bind source (semantics.fieldOutcomes group)))
      _ (semantics.combine fieldOutcome restOutcome)
    rw [BooleanDecision.evaluateOutcome_map_bind]
    rw [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1,
      BooleanDecision.evaluateOutcome_combineMap] at ihRest
    exact ⟨fieldOutcome, restOutcome, ⟨children, ihChildren, hfield⟩, ihRest, rfl⟩
  case none =>
    intro environment group
    rw [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1,
      BooleanDecision.joinMap.eq_def, BooleanDecision.evaluateOutcome]
    simp [OutcomeSet.singleton]
  case some =>
    intro environment group parentTypes childParentType outcome hparentType
      _houtcome ih
    rw [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1]
    apply BooleanDecision.evaluateOutcome_joinMap_of_mem semantics assignment _ hparentType
    simpa using ih
  case t => exact h

private theorem ContextOutcome.ofEvaluateWithPruning
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (variableOrder : BooleanVariableNames)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (environment : BooleanEnvironment) (pruningValues : VariableValues)
    (assignment : BooleanAssignment)
    (outcome : semantics.Summary)
    (hpruning : pruningValues = environment.pruningValues)
    (houtcome
      : BooleanDecision.evaluateOutcome assignment
          (cursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics)
            schema variableOrder inheritedBooleanCondition caseCondition possibleTypes
            environment pruningValues)
          outcome)
    : ContextOutcome semantics schema assignment environment inheritedBooleanCondition
        caseCondition cursor possibleTypes outcome := by
  apply CaseCursor.summarizeDecisionWithPruning.induct schema pruningValues
    (motive1 := fun inherited caseCondition cursor possibleTypes environment =>
      ∀ assignment outcome,
        pruningValues = environment.pruningValues ->
        BooleanDecision.evaluateOutcome assignment
            (cursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics)
              schema variableOrder inherited caseCondition possibleTypes environment
              pruningValues)
            outcome
          -> ContextOutcome semantics schema assignment environment inherited
              caseCondition cursor possibleTypes outcome)
    (motive2 := fun groups environment =>
      ∀ assignment outcome,
        pruningValues = environment.pruningValues ->
        BooleanDecision.evaluateOutcome assignment
            (CaseCursor.summarizeFieldGroupsDecisionWithPruning
              (OutcomeSemantics.proofAlgebra semantics) schema variableOrder groups
              environment pruningValues)
            outcome
          -> ContextFieldGroupsOutcome semantics schema assignment environment groups
              outcome)
    (motive3 := fun group parentTypes environment =>
      ∀ assignment outcome,
        pruningValues = environment.pruningValues ->
        BooleanDecision.evaluateOutcome assignment
            (CaseCursor.summarizeChildTypesDecisionWithPruning
              (OutcomeSemantics.proofAlgebra semantics) schema variableOrder group parentTypes
              environment pruningValues)
            outcome
          -> ContextChildTypesOutcome semantics schema assignment environment group
              parentTypes outcome)
  case case1 =>
    intro inherited caseCondition cursor possibleTypes environment hbranches ih assignment
      outcome hpruning houtcome
    rw [CaseCursor.summarizeDecisionWithPruning_nil_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues
      hbranches] at houtcome
    exact .fields assignment environment inherited caseCondition cursor possibleTypes
      outcome hbranches (ih assignment outcome hpruning houtcome)
  case case2 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest hbranches
      typeName hcondition ihSelect ihSkip assignment outcome hpruning houtcome
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues
      branch rest hbranches] at houtcome
    simp only [hcondition] at houtcome
    rcases BooleanDecision.evaluateOutcome_joinMap_cases semantics assignment _ houtcome with
      ⟨hregions, rfl⟩ | ⟨region, hregion, hregionOutcome⟩
    · exact .noTypeRegion assignment environment inherited caseCondition cursor
        possibleTypes branch rest typeName hbranches hcondition hregions
    · by_cases hselected
          : possibleTypesSubset region branch.body.condition.possibleTypes = true
      · simp only [hselected, ↓reduceIte] at hregionOutcome
        exact .selectTypeRegion assignment environment inherited caseCondition cursor
          possibleTypes branch rest typeName region outcome hbranches hcondition hregion
          hselected (ihSelect region assignment outcome hpruning hregionOutcome)
      · have hskipped :
            possibleTypesSubset region branch.body.condition.possibleTypes = false :=
          Bool.eq_false_iff.mpr hselected
        simp only [hskipped, Bool.false_eq_true, ↓reduceIte] at hregionOutcome
        exact .skipTypeRegion assignment environment inherited caseCondition cursor
          possibleTypes branch rest typeName region outcome hbranches hcondition hregion
          hskipped (ihSkip region assignment outcome hpruning hregionOutcome)
  case case3 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest hbranches
      literal hcondition value hstatus selectedLiteral ih assignment outcome hpruning
      houtcome
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues
      branch rest hbranches] at houtcome
    simp only [hcondition, hstatus] at houtcome
    exact .knownBoolean assignment environment inherited caseCondition cursor possibleTypes
      branch rest literal value outcome hbranches hcondition hstatus
      (ih assignment outcome hpruning houtcome)
  case case4 =>
    intro inherited caseCondition cursor possibleTypes environment branch rest hbranches
      literal hcondition hstatus ihFalse ihTrue assignment outcome hpruning houtcome
    rw [CaseCursor.summarizeDecisionWithPruning_cons_optimality _ schema variableOrder
      inherited caseCondition cursor possibleTypes environment pruningValues
      branch rest hbranches] at houtcome
    simp only [hcondition, hstatus, BooleanDecision.evaluateOutcome] at houtcome
    apply ContextOutcome.splitBoolean assignment environment inherited caseCondition cursor
      possibleTypes branch rest literal outcome hbranches hcondition hstatus
    by_cases hvalue : assignment literal.variableName
    · simp only [hvalue, ↓reduceIte]
      apply ihTrue assignment outcome
      · exact hpruning.trans
          (BooleanEnvironment.pruningValues_assign environment literal.variableName
            true).symm
      simpa [hvalue] using houtcome
    · simp only [hvalue, Bool.false_eq_true, ↓reduceIte]
      apply ihFalse assignment outcome
      · exact hpruning.trans
          (BooleanEnvironment.pruningValues_assign environment literal.variableName
            false).symm
      simpa [hvalue] using houtcome
  case case5 =>
    intro groups environment ih assignment outcome hpruning houtcome
    induction groups generalizing outcome with
    | nil =>
        rw [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1,
          BooleanDecision.evaluateOutcome_combineMap, TreeSummary.combineMap] at houtcome
        have hequal : outcome = semantics.empty := by
          simpa [OutcomeSet.singleton] using houtcome
        subst outcome
        exact .nil assignment environment
    | cons group rest ihRest =>
        rw [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1,
          BooleanDecision.evaluateOutcome_combineMap, TreeSummary.combineMap] at houtcome
        rcases houtcome with ⟨fieldOutcome, restOutcome, hfieldOutcome, hrestOutcome,
          rfl⟩
        rw [BooleanDecision.evaluateOutcome_map_bind] at hfieldOutcome
        rcases hfieldOutcome with ⟨children, hchildren, hfield⟩
        apply ContextFieldGroupsOutcome.cons assignment environment group rest children
          fieldOutcome restOutcome
        · exact ih group (by simp) assignment children hpruning hchildren
        · exact hfield
        · apply ihRest
            (fun candidate hcandidate => ih candidate (by simp [hcandidate]))
          rw [CaseCursor.summarizeFieldGroupsDecisionWithPruning.eq_1,
            BooleanDecision.evaluateOutcome_combineMap]
          exact hrestOutcome
  case case6 =>
    intro group parentTypes environment ih assignment outcome hpruning houtcome
    rw [CaseCursor.summarizeChildTypesDecisionWithPruning.eq_1] at houtcome
    rcases BooleanDecision.evaluateOutcome_joinMap_cases semantics assignment _ houtcome with
      ⟨hparentTypes, rfl⟩ | ⟨childParentType, hparentType, hchild⟩
    · subst parentTypes
      exact .none assignment environment group
    · have hchildOutcome := ih childParentType assignment outcome hpruning hchild
      rw [hpruning] at hchildOutcome
      exact .some assignment environment group parentTypes childParentType outcome
        hparentType hchildOutcome
  all_goals assumption

private theorem contextOutcome_iff_evaluate
    {semantics : OutcomeSemantics.{u}} (schema : Schema)
    (variableOrder : BooleanVariableNames) (assignment : BooleanAssignment)
    (environment : BooleanEnvironment)
    (inheritedBooleanCondition caseCondition : List BooleanLiteral)
    (cursor : CaseCursor) (possibleTypes : PossibleTypeRegion)
    (outcome : semantics.Summary)
    : ContextOutcome semantics schema assignment environment inheritedBooleanCondition
        caseCondition cursor possibleTypes outcome
      ↔ BooleanDecision.evaluateOutcome assignment
          (cursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics)
            schema variableOrder inheritedBooleanCondition caseCondition possibleTypes
            environment environment.pruningValues)
          outcome :=
  ⟨
    fun h => h.toEvaluate variableOrder,
    ContextOutcome.ofEvaluateWithPruning schema variableOrder inheritedBooleanCondition
      caseCondition cursor possibleTypes environment environment.pruningValues assignment
      outcome rfl
  ⟩

-- A derivation depends on an environment only through values fixed by its assignment
-- and through the immutable pruning context. This is the semantic counterpart of
-- resolving Boolean decisions incrementally in any branch-local order.
theorem ContextOutcome.changeEnvironment
    {semantics : OutcomeSemantics.{u}} {schema : Schema}
    {assignment : BooleanAssignment} {source : BooleanEnvironment}
    {inheritedBooleanCondition caseCondition : List BooleanLiteral}
    {cursor : CaseCursor} {possibleTypes : PossibleTypeRegion}
    {outcome : semantics.Summary}
    (houtcome
      : ContextOutcome semantics schema assignment source inheritedBooleanCondition
          caseCondition cursor possibleTypes outcome)
    (hsource : assignment.Extends source)
    (target : BooleanEnvironment) (htarget : assignment.Extends target)
    (hpruning : target.pruningValues = source.pruningValues)
    : ContextOutcome semantics schema assignment target inheritedBooleanCondition
        caseCondition cursor possibleTypes outcome := by
  apply @ContextOutcome.rec semantics schema assignment
    (fun source inherited caseCondition cursor possibleTypes outcome _h =>
      assignment.Extends source
      -> ∀ target,
          assignment.Extends target
          -> target.pruningValues = source.pruningValues
          -> ContextOutcome semantics schema assignment target inherited caseCondition
              cursor possibleTypes outcome)
    (fun source groups outcome _h =>
      assignment.Extends source
      -> ∀ target,
          assignment.Extends target
          -> target.pruningValues = source.pruningValues
          -> ContextFieldGroupsOutcome semantics schema assignment target groups outcome)
    (fun source group parentTypes outcome _h =>
      assignment.Extends source
      -> ∀ target,
          assignment.Extends target
          -> target.pruningValues = source.pruningValues
          -> ContextChildTypesOutcome semantics schema assignment target group parentTypes
              outcome)
  case noTypeRegion =>
    intro source inherited caseCondition cursor possibleTypes branch rest typeName
      hbranches hcondition hregions _hsource target _htarget _hpruning
    exact .noTypeRegion assignment target inherited caseCondition cursor possibleTypes
      branch rest typeName hbranches hcondition hregions
  case selectTypeRegion =>
    intro source inherited caseCondition cursor possibleTypes branch rest typeName region
      outcome hbranches hcondition hregion hselected _houtcome ih hsource target htarget
      hpruning
    exact .selectTypeRegion assignment target inherited caseCondition cursor possibleTypes
      branch rest typeName region outcome hbranches hcondition hregion hselected
      (ih hsource target htarget hpruning)
  case skipTypeRegion =>
    intro source inherited caseCondition cursor possibleTypes branch rest typeName region
      outcome hbranches hcondition hregion hskipped _houtcome ih hsource target htarget
      hpruning
    exact .skipTypeRegion assignment target inherited caseCondition cursor possibleTypes
      branch rest typeName region outcome hbranches hcondition hregion hskipped
      (ih hsource target htarget hpruning)
  case knownBoolean =>
    intro source inherited caseCondition cursor possibleTypes branch rest literal value
      outcome hbranches hcondition hstatus _houtcome ih hsource target htarget hpruning
    have hassignment : assignment literal.variableName = value :=
      hsource literal.variableName value hstatus
    subst value
    cases htargetStatus : target.statusForVariable literal.variableName with
    | none =>
        apply ContextOutcome.splitBoolean assignment target inherited caseCondition cursor
          possibleTypes branch rest literal outcome hbranches hcondition htargetStatus
        apply ih hsource
          (target.assign literal.variableName (assignment literal.variableName))
          (BooleanEnvironment.extends_assign_self htarget literal.variableName)
        simpa [BooleanEnvironment.pruningValues_assign] using hpruning
    | some targetValue =>
        have htargetValue : assignment literal.variableName = targetValue :=
          htarget literal.variableName targetValue htargetStatus
        subst targetValue
        exact .knownBoolean assignment target inherited caseCondition cursor possibleTypes
          branch rest literal (assignment literal.variableName) outcome hbranches hcondition
          htargetStatus
          (ih hsource target htarget hpruning)
  case splitBoolean =>
    intro source inherited caseCondition cursor possibleTypes branch rest literal outcome
      hbranches hcondition hstatus _houtcome ih hsource target htarget hpruning
    have hsourceAssigned :=
      BooleanEnvironment.extends_assign_self hsource literal.variableName
    cases htargetStatus : target.statusForVariable literal.variableName with
    | none =>
        apply ContextOutcome.splitBoolean assignment target inherited caseCondition cursor
          possibleTypes branch rest literal outcome hbranches hcondition htargetStatus
        apply ih hsourceAssigned
          (target.assign literal.variableName (assignment literal.variableName))
          (BooleanEnvironment.extends_assign_self htarget literal.variableName)
        simpa [BooleanEnvironment.pruningValues_assign] using hpruning
    | some targetValue =>
        have htargetValue : assignment literal.variableName = targetValue :=
          htarget literal.variableName targetValue htargetStatus
        subst targetValue
        apply ContextOutcome.knownBoolean assignment target inherited caseCondition cursor
          possibleTypes branch rest literal (assignment literal.variableName) outcome
          hbranches hcondition htargetStatus
        apply ih hsourceAssigned target htarget
        simpa [BooleanEnvironment.pruningValues_assign] using hpruning
  case fields =>
    intro source inherited caseCondition cursor possibleTypes outcome hbranches _houtcome ih
      hsource target htarget hpruning
    exact .fields assignment target inherited caseCondition cursor possibleTypes outcome
      hbranches (ih hsource target htarget hpruning)
  case nil =>
    intro source _hsource target _htarget _hpruning
    exact .nil assignment target
  case cons =>
    intro source group rest children fieldOutcome restOutcome _hchildren hfield _hrest
      ihChildren ihRest hsource target htarget hpruning
    exact .cons assignment target group rest children fieldOutcome restOutcome
      (ihChildren hsource target htarget hpruning) hfield
      (ihRest hsource target htarget hpruning)
  case none =>
    intro source group _hsource target _htarget _hpruning
    exact .none assignment target group
  case some =>
    intro source group parentTypes childParentType outcome hparentType _houtcome ih
      hsource target htarget hpruning
    apply ContextChildTypesOutcome.some assignment target group parentTypes childParentType
      outcome hparentType
    rw [hpruning]
    exact ih hsource target htarget hpruning
  all_goals assumption

end CaseCursor

-- The executable fold collects exactly the relationally derived cursor outcomes.
private theorem conditionTreeOutcomes_iff_proofFold
    (semantics : OutcomeSemantics.{u}) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (initial : BooleanEnvironment) (outcome : semantics.Summary)
    : CaseCursor.conditionTreeOutcomes semantics schema inheritedBooleanCondition
        tree initial outcome
      ↔ (Internal.summarizeConditionTreeDecision
          (OutcomeSemantics.proofAlgebra semantics) schema inheritedBooleanCondition
          tree (conditionTreeBooleanVariables tree).eraseDups initial).collapse
          (OutcomeSemantics.proofAlgebra semantics) outcome := by
  let variableOrder := (conditionTreeBooleanVariables tree).eraseDups
  let decision :=
    CaseCursor.summarizeDecisionWithPruning (OutcomeSemantics.proofAlgebra semantics) schema
      variableOrder inheritedBooleanCondition [] (.ofConditionTree tree)
      tree.condition.possibleTypes initial initial.pruningValues
  have hresolved : BooleanDecision.ResolvedBy initial decision :=
    CaseCursor.summarizeDecisionWithPruning_resolvedBy
      (OutcomeSemantics.proofAlgebra semantics) schema variableOrder
      inheritedBooleanCondition [] (.ofConditionTree tree) tree.condition.possibleTypes
      initial initial.pruningValues
  unfold CaseCursor.conditionTreeOutcomes
    Internal.summarizeConditionTreeDecision
  change (∃ assignment,
            assignment.Extends initial
            ∧ CaseCursor.ContextOutcome semantics schema assignment initial
                inheritedBooleanCondition [] (.ofConditionTree tree)
                tree.condition.possibleTypes outcome)
          ↔ (decision.compact (OutcomeSemantics.proofAlgebra semantics).join).collapse
              (OutcomeSemantics.proofAlgebra semantics) outcome
  rw [BooleanDecision.collapse_compact]
  rw [BooleanDecision.collapse_iff_exists_matches_evaluate semantics hresolved outcome]
  apply exists_congr
  intro assignment
  apply and_congr_right
  intro _hextends
  exact CaseCursor.contextOutcome_iff_evaluate schema variableOrder assignment initial
    inheritedBooleanCondition [] (.ofConditionTree tree) tree.condition.possibleTypes
    outcome

theorem bestBound_of_attainable_iff
    {ConcreteSummary : Type u} {AbstractSummary : Type v}
    {le : AbstractSummary -> AbstractSummary -> Prop}
    {related : ConcreteSummary -> AbstractSummary -> Prop}
    {left right : OutcomeSet ConcreteSummary} {estimate : AbstractSummary}
    (hiff : ∀ outcome, left outcome ↔ right outcome)
    (hbest : BestBound le related right estimate)
    : BestBound le related left estimate :=
  {
    feasible := by
      rcases hbest.feasible with ⟨outcome, houtcome⟩
      exact ⟨outcome, (hiff outcome).mpr houtcome⟩
    sound := fun outcome houtcome => hbest.sound outcome ((hiff outcome).mp houtcome)
    least :=
      fun candidate hcandidate =>
        hbest.least candidate
          fun outcome houtcome =>
            hcandidate outcome ((hiff outcome).mpr houtcome)
  }

-- The internal decision builder is the least abstract bound of the relational feasible
-- cases under any explicit Boolean environment. This proof-facing theorem does not add
-- a generic public evaluation entry point.
theorem Internal.summarizeConditionTreeDecision_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (initial : CaseCursor.BooleanEnvironment)
    : BestBound le laws.approximates
        (CaseCursor.conditionTreeOutcomes semantics schema
          inheritedBooleanCondition tree initial)
        ((Internal.summarizeConditionTreeDecision abstract schema
            inheritedBooleanCondition tree (conditionTreeBooleanVariables tree).eraseDups
            initial).collapse
          abstract) := by
  apply bestBound_of_attainable_iff
    (conditionTreeOutcomes_iff_proofFold semantics schema
      inheritedBooleanCondition tree initial)
  unfold Internal.summarizeConditionTreeDecision
  rw [BooleanDecision.collapse_compact, BooleanDecision.collapse_compact]
  apply BooleanDecision.Related.collapse
    (OutcomeSemantics.proofAlgebra semantics) abstract laws.relation
  exact CaseCursor.summarizeDecisionWithPruning_related
    (OutcomeSemantics.proofAlgebra semantics) abstract laws.relation schema
    (conditionTreeBooleanVariables tree).eraseDups inheritedBooleanCondition []
    (.ofConditionTree tree) tree.condition.possibleTypes initial initial.pruningValues

-- The symbolic cursor entry point is the corresponding specialization with every
-- absent Boolean still unresolved.
theorem CaseCursor.summarizeConditionTree_best
    {semantics : OutcomeSemantics.{u}} {abstract : Algebra.{v}}
    {le : abstract.Summary -> abstract.Summary -> Prop}
    (laws : BestTransferLaws semantics abstract le) (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (caseValues : VariableValues)
    : BestBound le laws.approximates
        (CaseCursor.conditionTreeOutcomes semantics schema
          inheritedBooleanCondition tree (.symbolic caseValues))
        (CaseCursor.summarizeConditionTree abstract schema inheritedBooleanCondition tree
          caseValues) := by
  simpa [CaseCursor.summarizeConditionTree] using
    Internal.summarizeConditionTreeDecision_best laws schema
      inheritedBooleanCondition tree (.symbolic caseValues)

end ExactCases
end TreeSummary
end GraphQL
