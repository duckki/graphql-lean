import Proofs.GraphQL.Theories.TreeSummary.Syntactic.RuntimePath

/-! Compactness and algebraic soundness of node-local Syntactic branch cases. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.ConditionTree

universe v

-----------------------------------------------------------------------------------------
-- Compact immediate-branch partition
-----------------------------------------------------------------------------------------

-- The one-pass node compiler never duplicates a source branch across its independent
-- type and Boolean families. Infeasible and known-false branches may make the bound
-- strict.
theorem summarizeImmediateBranches_cardinality_le
    (algebra : Algebra.{v}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (branches : List (Branch Tree)) (variableValues : Execution.VariableValues)
    (typeScope : PossibleTypes)
    : let summaries :=
        summarizeImmediateBranches algebra schema parentType inheritedBooleanCondition
          branches variableValues typeScope
      summaries.typeBranches.length + summaries.booleanBranches.length
      ≤ branches.length := by
  induction branches with
  | nil => simp [summarizeImmediateBranches]
  | cons branch rest ih =>
      dsimp only at ih
      cases hcondition : branch.condition with
      | typeCondition typeName =>
          rw [summarizeImmediateBranches]
          simp only [hcondition]
          split
          · simpa only [List.length_cons] using Nat.le_succ_of_le ih
          · simp only [List.length_cons]
            omega
      | booleanLiteral literal =>
          rw [summarizeImmediateBranches]
          simp only [hcondition]
          cases hevaluation : evaluateBooleanLiteral? variableValues literal with
          | none =>
              simp only [List.length_cons]
              omega
          | some value =>
              cases value
              · simpa only [List.length_cons] using Nat.le_succ_of_le ih
              · simp only [List.length_cons]
                omega

-----------------------------------------------------------------------------------------
-- Direct per-variable Boolean factorization
-----------------------------------------------------------------------------------------

abbrev BooleanAssignment := Name -> Bool

def selectedBooleanAlternative (algebra : Algebra.{v})
    (assignment : BooleanAssignment)
    (entry : Name × BooleanAlternatives algebra.Summary)
    : algebra.Summary :=
  (if assignment entry.1 then entry.2.whenTrue else entry.2.whenFalse).getD algebra.empty

def summarizeSelectedBooleanAlternatives (algebra : Algebra.{v})
    (assignment : BooleanAssignment)
    (entries : List (Name × BooleanAlternatives algebra.Summary))
    : algebra.Summary :=
  combineMap algebra entries
    fun entry _hentry =>
      selectedBooleanAlternative algebra assignment entry

def summarizeSelectedBooleanBranches (algebra : Algebra.{v})
    (assignment : BooleanAssignment)
    : List (BooleanBranchSummary algebra.Summary) -> algebra.Summary
  | [] => algebra.empty
  | branch :: rest =>
      algebra.combine
        (if assignment branch.literal.variableName = branch.literal.requiredValue then
            branch.summary
          else
            algebra.empty)
        (summarizeSelectedBooleanBranches algebra assignment rest)

theorem combineOptional_getD_right (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (summary : Option algebra.Summary) (right : algebra.Summary)
    : (combineOptional algebra summary (some right)).getD algebra.empty
      = algebra.combine (summary.getD algebra.empty) right := by
  cases summary <;> simp [combineOptional, lawful.empty_combine]

theorem summarizeSelectedBooleanAlternatives_add
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (assignment : BooleanAssignment)
    (branch : BooleanBranchSummary algebra.Summary)
    (entries : List (Name × BooleanAlternatives algebra.Summary))
    : summarizeSelectedBooleanAlternatives algebra assignment
        (addBooleanBranchSummary algebra branch entries)
      = algebra.combine
          (if assignment branch.literal.variableName = branch.literal.requiredValue then
              branch.summary
            else
              algebra.empty)
          (summarizeSelectedBooleanAlternatives algebra assignment entries) := by
  induction entries with
  | nil =>
      cases hrequired : branch.literal.requiredValue <;>
        cases hvalue : assignment branch.literal.variableName <;>
        simp [addBooleanBranchSummary, summarizeSelectedBooleanAlternatives, combineMap,
          selectedBooleanAlternative, BooleanAlternatives.add, hrequired, hvalue,
          lawful.empty_combine, lawful.combine_empty]
      all_goals rfl
  | cons entry rest ih =>
      rcases entry with ⟨variableName, alternatives⟩
      by_cases hname : branch.literal.variableName = variableName
      · subst variableName
        simp only [addBooleanBranchSummary, beq_self_eq_true, if_true]
        cases hrequired : branch.literal.requiredValue <;>
          cases hvalue : assignment branch.literal.variableName <;>
          simp [summarizeSelectedBooleanAlternatives, combineMap,
            selectedBooleanAlternative, BooleanAlternatives.add, hvalue,
            lawful.empty_combine]
        all_goals
          rw [combineOptional_getD_right algebra lawful]
          rw [lawful.combine_comm _ branch.summary]
          rw [lawful.combine_assoc]
      · have hbeq : (branch.literal.variableName == variableName) = false := by
          exact beq_eq_false_iff_ne.mpr hname
        simp only [addBooleanBranchSummary, hbeq, Bool.false_eq_true, ↓reduceIte]
        simp only [summarizeSelectedBooleanAlternatives, combineMap]
        change algebra.combine
            (selectedBooleanAlternative algebra assignment (variableName, alternatives))
            (summarizeSelectedBooleanAlternatives algebra assignment
              (addBooleanBranchSummary algebra branch rest))
          = algebra.combine
              (if assignment branch.literal.variableName
                    = branch.literal.requiredValue then
                branch.summary
              else
                algebra.empty)
              (algebra.combine
                (selectedBooleanAlternative algebra assignment
                  (variableName, alternatives))
                (summarizeSelectedBooleanAlternatives algebra assignment rest))
        rw [ih]
        rw [← lawful.combine_assoc]
        rw [lawful.combine_comm
          (selectedBooleanAlternative algebra assignment (variableName, alternatives))]
        rw [lawful.combine_assoc]

theorem summarizeSelectedBooleanAlternatives_foldl
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (assignment : BooleanAssignment)
    (branches : List (BooleanBranchSummary algebra.Summary))
    (entries : List (Name × BooleanAlternatives algebra.Summary))
    : summarizeSelectedBooleanAlternatives algebra assignment
        (branches.foldl
          (fun accumulated branch =>
            addBooleanBranchSummary algebra branch accumulated)
          entries)
      = algebra.combine
          (summarizeSelectedBooleanBranches algebra assignment branches)
          (summarizeSelectedBooleanAlternatives algebra assignment entries) := by
  induction branches generalizing entries with
  | nil =>
      rw [List.foldl]
      rw [summarizeSelectedBooleanBranches]
      change summarizeSelectedBooleanAlternatives algebra assignment entries
        = algebra.combine algebra.empty
            (summarizeSelectedBooleanAlternatives algebra assignment entries)
      exact (lawful.empty_combine _).symm
  | cons branch rest ih =>
      rw [List.foldl_cons, ih]
      rw [summarizeSelectedBooleanAlternatives_add algebra lawful]
      simp only [summarizeSelectedBooleanBranches]
      rw [← lawful.combine_assoc]
      exact congrArg
        (fun summary =>
          algebra.combine summary
            (summarizeSelectedBooleanAlternatives algebra assignment entries))
        (lawful.combine_comm _ _)

theorem summarizeSelectedBooleanAlternatives_collect
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (assignment : BooleanAssignment)
    (branches : List (BooleanBranchSummary algebra.Summary))
    : summarizeSelectedBooleanAlternatives algebra assignment
        (collectBooleanAlternatives algebra branches)
      = summarizeSelectedBooleanBranches algebra assignment branches := by
  unfold collectBooleanAlternatives
  rw [summarizeSelectedBooleanAlternatives_foldl algebra lawful]
  rw [summarizeSelectedBooleanAlternatives, combineMap, lawful.combine_empty]

def BooleanAssignmentMatches (assignment : BooleanAssignment)
    (variableValues : Execution.VariableValues)
    : Prop :=
  ∀ variableName value,
    Execution.inputValueBoolean? variableValues (.variable variableName) = some value
    -> assignment variableName = value

theorem selectedBooleanAlternative_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (assignment : BooleanAssignment)
    (variableValues : Execution.VariableValues)
    (hmatch : BooleanAssignmentMatches assignment variableValues)
    (entry : Name × BooleanAlternatives algebra.Summary)
    : lawful.le
        (selectedBooleanAlternative algebra assignment entry)
        ((summarizeBooleanAlternatives? algebra variableValues entry).getD
          algebra.empty) := by
  rcases entry with ⟨variableName, alternatives⟩
  cases hvalue : Execution.inputValueBoolean? variableValues (.variable variableName) with
  | some value =>
      have hassignment := hmatch variableName value hvalue
      cases value <;>
        simp [selectedBooleanAlternative, summarizeBooleanAlternatives?, hvalue,
          hassignment, lawful.le_refl]
  | none =>
      rcases alternatives with ⟨whenFalse, whenTrue⟩
      cases hassignment : assignment variableName <;>
        cases whenFalse <;>
        cases whenTrue <;>
        simp [selectedBooleanAlternative, summarizeBooleanAlternatives?, hvalue,
          hassignment, joinOptional, lawful.empty_le, lawful.le_refl,
          lawful.le_join_left, lawful.le_join_right]

theorem combineMap_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (items : List α) (lower upper : α -> algebra.Summary)
    (hle : ∀ item, item ∈ items -> lawful.le (lower item) (upper item))
    : lawful.le
        (combineMap algebra items fun item _hitem => lower item)
        (combineMap algebra items fun item _hitem => upper item) := by
  induction items with
  | nil =>
      rw [combineMap, combineMap]
      exact lawful.le_refl _
  | cons item rest ih =>
      rw [combineMap, combineMap]
      apply lawful.combine_mono
      · exact hle item (by simp)
      · exact ih fun candidate hcandidate => hle candidate (by simp [hcandidate])

theorem summarizeSelectedBooleanBranches_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (assignment : BooleanAssignment)
    (variableValues : Execution.VariableValues)
    (hmatch : BooleanAssignmentMatches assignment variableValues)
    (branches : List (BooleanBranchSummary algebra.Summary))
    : lawful.le
        (summarizeSelectedBooleanBranches algebra assignment branches)
        (summarizeBooleanBranchSummaries algebra variableValues branches) := by
  rw [← summarizeSelectedBooleanAlternatives_collect algebra lawful]
  unfold summarizeSelectedBooleanAlternatives summarizeBooleanBranchSummaries
  exact combineMap_le algebra lawful (collectBooleanAlternatives algebra branches)
    (selectedBooleanAlternative algebra assignment)
    (fun entry =>
      (summarizeBooleanAlternatives? algebra variableValues entry).getD algebra.empty)
    (fun entry _hentry =>
      selectedBooleanAlternative_le algebra lawful assignment variableValues hmatch entry)

end Syntactic
end TreeSummary
end GraphQL
