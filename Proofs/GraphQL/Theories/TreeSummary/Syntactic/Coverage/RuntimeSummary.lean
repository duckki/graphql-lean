import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Cases
import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Factorization
import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Coverage.Execution

/-! Runtime-selected summaries and local case construction for Syntactic coverage. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.Execution
open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open TreeSummary.Measure

universe u v
-- Runtime-selected fold used by the Syntactic soundness proof. Field children use the
-- widened public analysis; only the current condition branches follow the concrete
-- runtime type and Boolean traversal.
mutual
  def summarizeTreeAtRuntimeType (algebra : Algebra)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (runtimeType : Name)
      (tree : Tree) (traversal : Traversal)
      : algebra.Summary :=
    let groups := collectFieldGroups inheritedBooleanCondition tree.condition tree.fields
    algebra.combine
      (summarizeFieldGroups algebra schema groups traversal.summaryVariableValues)
      (summarizeBranchesAtRuntimeType algebra schema parentType
        inheritedBooleanCondition runtimeType tree.branches traversal)
  termination_by
    (Termination.conditionTreeResponseDepth tree, sizeOf tree, 0, 0)
  decreasing_by
    simp only [Termination.conditionTreeResponseDepth]
    apply Measure.quadruple_lt_of_depth_le_of_control_lt
    · exact Nat.le_max_right _ _
    · cases tree
      simp_wf
      omega

  def summarizeBranchesAtRuntimeType (algebra : Algebra)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral) (runtimeType : Name)
      (branches : List (Branch Tree)) (traversal : Traversal)
      : algebra.Summary :=
    match branches with
    | [] => algebra.empty
    | branch :: rest =>
        let branchSummary :=
          if traversal.includeBranchAtRuntimeType schema runtimeType branch.condition then
            summarizeTreeAtRuntimeType algebra schema
              (branch.condition.parentType parentType) inheritedBooleanCondition
              runtimeType branch.body traversal
          else
            algebra.empty
        algebra.combine branchSummary
          (summarizeBranchesAtRuntimeType algebra schema parentType
            inheritedBooleanCondition runtimeType rest traversal)
  termination_by
    (Termination.conditionBranchesResponseDepth branches, sizeOf branches, 0, 0)
  decreasing_by
    · simp only [Termination.conditionBranchesResponseDepth]
      apply Measure.quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_left _ _
      · cases branch
        simp_wf
        omega
    · simp only [Termination.conditionBranchesResponseDepth]
      apply Measure.quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_max_right _ _
      · simp_wf
        omega
end

theorem typeBranchBody_possibleTypes_eq
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (parent child : Condition) (typeName : Name)
    (htransition
      : conditionForBranch? schema inheritedBooleanCondition parent
          (.typeCondition typeName)
        = some child)
    : child.possibleTypes
      = intersectPossibleTypes parent.possibleTypes
          (schema.getPossibleTypes typeName) := by
  unfold conditionForBranch? at htransition
  let possibleTypes :=
    intersectPossibleTypes parent.possibleTypes (schema.getPossibleTypes typeName)
  by_cases hempty : possibleTypes.isEmpty = true
  · simp [possibleTypes, hempty] at htransition
  · simp only [possibleTypes, hempty, Bool.false_eq_true, if_false] at htransition
    cases htransition
    rfl

theorem summarizeTypeBranchCase?_getD_cons
    (algebra : Algebra) (lawful : algebra.Lawful) (runtimeType : Name)
    (branch : TypeBranchSummary algebra.Summary)
    (branches : List (TypeBranchSummary algebra.Summary))
    : (summarizeTypeBranchCase? algebra runtimeType (branch :: branches)).getD
        algebra.empty
      = if runtimeType ∈ branch.possibleTypes then
          algebra.combine branch.summary
            ((summarizeTypeBranchCase? algebra runtimeType branches).getD algebra.empty)
        else
          (summarizeTypeBranchCase? algebra runtimeType branches).getD algebra.empty := by
  by_cases hactive : runtimeType ∈ branch.possibleTypes
  · cases hrest : summarizeTypeBranchCase? algebra runtimeType branches <;>
      simp [summarizeTypeBranchCase?, hactive, hrest, lawful.combine_empty]
  · simp [summarizeTypeBranchCase?, hactive]

private theorem summarizeTypeBranchCase?_eq_of_condition_membership
    (algebra : Algebra) (left right : Name)
    (branches : List (TypeBranchSummary algebra.Summary))
    (hmembership
      : ∀ branch,
          branch ∈ branches
          -> branch.possibleTypes.contains left = branch.possibleTypes.contains right)
    : summarizeTypeBranchCase? algebra left branches
      = summarizeTypeBranchCase? algebra right branches := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      rw [summarizeTypeBranchCase?, summarizeTypeBranchCase?]
      rw [hmembership branch (by simp)]
      rw [ih (fun candidate hcandidate =>
        hmembership candidate (by simp [hcandidate]))]

theorem summarizeSelectedTypeBranches_le_runtimeCases
    (algebra : Algebra) (lawful : algebra.Lawful)
    (typeScope : PossibleTypes) (runtimeType : Name)
    (branches : List (TypeBranchSummary algebra.Summary))
    (hruntimeType : runtimeType ∈ typeScope)
    : lawful.le
        ((summarizeTypeBranchCase? algebra runtimeType branches).getD algebra.empty)
        (summarizeTypeRuntimeCases algebra typeScope branches) := by
  cases hcase : summarizeTypeBranchCase? algebra runtimeType branches with
  | none =>
      simp only [Option.getD_none]
      exact lawful.empty_le _
  | some summary =>
      simp only [Option.getD_some]
      have hexact :=
        ExactCases.possibleTypeRegions_exact typeScope
          (typeBranchPossibleTypes branches)
      rcases hexact.2.1 runtimeType hruntimeType with
        ⟨region, ⟨hregion, hruntimeRegion⟩, _hunique⟩
      cases region with
      | nil => simp at hruntimeRegion
      | cons representative rest =>
          have hrepresentative : representative ∈ representative :: rest := by simp
          have hsame :
              summarizeTypeBranchCase? algebra runtimeType branches
                = summarizeTypeBranchCase? algebra representative branches := by
            apply summarizeTypeBranchCase?_eq_of_condition_membership
            intro branch hbranch
            by_cases hempty : branch.possibleTypes.isEmpty = true
            · have hnil : branch.possibleTypes = [] := by
                simpa only [List.isEmpty_iff] using hempty
              simp [hnil]
            · exact hexact.2.2 (representative :: rest) hregion runtimeType
                hruntimeRegion representative hrepresentative branch.possibleTypes
                (List.mem_filterMap.mpr ⟨branch, hbranch, by simp [hempty]⟩)
          have hrepresentativeCase :
              summarizeTypeBranchCase? algebra representative branches
                = some summary := by
            rw [← hsame]
            exact hcase
          exact lawful.le_joinMap_of_mem
            (items := typeRuntimeCaseSummaries algebra typeScope branches)
            (fun selectedSummary _hselectedSummary => selectedSummary)
            (List.mem_filterMap.mpr
              ⟨representative :: rest, hregion, by
                simp [summarizeTypeBranchRegion?, hrepresentativeCase]⟩)

def runtimeBooleanAssignment (source : VariableValues) : BooleanAssignment :=
  runtimeBooleanDefault source

def BooleanValuesMatchRuntime (source values : VariableValues) : Prop :=
  BooleanValuesMatchForPruning source values

theorem booleanValuesMatchRuntime_empty (source : VariableValues)
    : BooleanValuesMatchRuntime source [] := by
  intro variableName value hvalue
  simp [inputValueBoolean?, lookupVariableValue?] at hvalue

theorem booleanValuesMatchRuntime_self (source : VariableValues)
    : BooleanValuesMatchRuntime source source := by
  intro variableName value hvalue
  simp [hvalue]

theorem evaluateBooleanLiteral_eq_runtime_of_some
    (source values : VariableValues)
    (hmatch : BooleanValuesMatchRuntime source values)
    (literal : BooleanLiteral) (result : Bool)
    (hevaluate : evaluateBooleanLiteral? values literal = some result)
    : (Traversal.withRuntimeBooleanDefaults source values).includeBranch
        (.booleanLiteral literal)
      = result := by
  cases literal with
  | positive variableName =>
      change (do
        let value ← inputValueBoolean? values (.variable variableName)
        pure (value == true)) = some result at hevaluate
      cases hvalue : inputValueBoolean? values (.variable variableName) with
      | none => simp [hvalue] at hevaluate
      | some value =>
          have heq := hmatch variableName value hvalue
          simp [hvalue] at hevaluate
          simpa [Traversal.withRuntimeBooleanDefaults, BooleanLiteral.variableName,
            BooleanLiteral.requiredValue, runtimeBooleanDefault, heq] using hevaluate
  | negative variableName =>
      change (do
        let value ← inputValueBoolean? values (.variable variableName)
        pure (value == false)) = some result at hevaluate
      cases hvalue : inputValueBoolean? values (.variable variableName) with
      | none => simp [hvalue] at hevaluate
      | some value =>
          have heq := hmatch variableName value hvalue
          simp [hvalue] at hevaluate
          simpa [Traversal.withRuntimeBooleanDefaults, BooleanLiteral.variableName,
            BooleanLiteral.requiredValue, runtimeBooleanDefault, heq] using hevaluate

theorem runtimeBooleanAssignment_matches
    (source values : VariableValues)
    (hmatch : BooleanValuesMatchRuntime source values)
    : BooleanAssignmentMatches (runtimeBooleanAssignment source) values := by
  intro variableName value hvalue
  exact (hmatch variableName value hvalue).symm

theorem runtimeType_mem_typeBranchBody
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (parent child : Condition) (typeName runtimeType : Name)
    (htransition
      : conditionForBranch? schema inheritedBooleanCondition parent
          (.typeCondition typeName)
        = some child)
    (hparent : runtimeType ∈ parent.possibleTypes)
    (hinclude : schema.typeIncludesObjectBool typeName runtimeType = true)
    : runtimeType ∈ child.possibleTypes := by
  unfold conditionForBranch? at htransition
  let possibleTypes :=
    intersectPossibleTypes parent.possibleTypes (schema.getPossibleTypes typeName)
  by_cases hempty : possibleTypes.isEmpty = true
  · simp [possibleTypes, hempty] at htransition
  · simp only [possibleTypes, hempty, Bool.false_eq_true, if_false] at htransition
    cases htransition
    apply List.contains_iff_mem.mp
    rw [SelectionConditions.contains_intersectPossibleTypes,
      List.contains_iff_mem.mpr hparent]
    simpa [Schema.typeIncludesObjectBool] using hinclude

theorem booleanBranchBody_possibleTypes
    (schema : Schema) (inheritedBooleanCondition : List BooleanLiteral)
    (parent child : Condition) (literal : BooleanLiteral)
    (htransition
      : conditionForBranch? schema inheritedBooleanCondition parent
          (.booleanLiteral literal)
        = some child)
    : child.possibleTypes = parent.possibleTypes := by
  simp only [conditionForBranch?] at htransition
  cases hcandidate : canonicalBooleanCondition (parent.booleanCondition ++ [literal]) with
  | none => simp [hcandidate] at htransition
  | some candidate =>
      let booleanCondition :=
        candidate.filter fun item => !inheritedBooleanCondition.contains item
      rw [hcandidate] at htransition
      change
        (canonicalBooleanCondition
            (inheritedBooleanCondition ++ booleanCondition)).bind
            (fun _globalBooleanCondition => some { parent with booleanCondition }) =
          some child at htransition
      cases hglobal
            : canonicalBooleanCondition
                (inheritedBooleanCondition ++ booleanCondition) with
      | none => simp [hglobal] at htransition
      | some globalCondition =>
          rw [hglobal] at htransition
          simp only [Option.bind_some] at htransition
          cases htransition
          rfl

end Syntactic
end TreeSummary
end GraphQL
