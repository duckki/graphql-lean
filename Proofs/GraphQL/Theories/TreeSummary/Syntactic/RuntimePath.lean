import GraphQL.Theories.TreeSummary.Syntactic
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.TreeSoundness.Invariants
import Proofs.GraphQL.Theories.TreeSummary.Algebra

/-! Proof-only runtime paths and extracted condition-group invariants. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.Execution
open GraphQL.ConditionTree
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

-- Proof-only policy selecting one concrete path through Boolean condition branches.
structure Traversal where
  includeBranch : BranchCondition -> Bool
  summaryVariableValues : Execution.VariableValues

def Traversal.all : Traversal :=
  { includeBranch := fun _branch => true, summaryVariableValues := [] }

def Traversal.withVariableValues (variableValues : Execution.VariableValues)
    : Traversal :=
  {
    includeBranch :=
      fun branchCondition =>
        match branchCondition with
        | .typeCondition _typeName => true
        | .booleanLiteral literal =>
            (evaluateBooleanLiteral? variableValues literal).getD true
    summaryVariableValues := variableValues
  }

mutual
  def traversedConditionGroups (tree : Tree) (traversal : Traversal) : List Condition :=
    tree.condition :: traversedBranchConditionGroups tree.branches traversal
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def traversedBranchConditionGroups (branches : List (Branch Tree))
      (traversal : Traversal)
      : List Condition :=
    match branches with
    | [] => []
    | branch :: rest =>
        let current :=
          if traversal.includeBranch branch.condition then
            traversedConditionGroups branch.body traversal
          else
            []
        current ++ traversedBranchConditionGroups rest traversal
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

-- The two condition lists have no common member. This proof-only helper describes the
-- subset of globally unique conditions selected by one runtime traversal.
def conditionGroupsDisjoint (left right : List Condition) : Prop :=
  ∀ condition, condition ∈ left -> condition ∉ right

mutual
  def visitedSiblingConditionGroupsDisjointInTree (tree : Tree) (traversal : Traversal)
      : Prop :=
    visitedSiblingConditionGroupsDisjoint tree.branches traversal
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def visitedSiblingConditionGroupsDisjoint (branches : List (Branch Tree))
      (traversal : Traversal)
      : Prop :=
    match branches with
    | [] => True
    | branch :: rest =>
        let current :=
          if traversal.includeBranch branch.condition then
            traversedConditionGroups branch.body traversal
          else
            []
        conditionGroupsDisjoint current (traversedBranchConditionGroups rest traversal)
        ∧ (if traversal.includeBranch branch.condition then
              visitedSiblingConditionGroupsDisjointInTree branch.body traversal
            else
              True)
        ∧ visitedSiblingConditionGroupsDisjoint rest traversal
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

-- Proof-only folds for the response-field pieces selected by one runtime traversal.
def summarizedChildren (algebra : Algebra) (schema : Schema)
    (traversal : Traversal) (group : CollectedFieldGroup)
    : algebra.Summary :=
  summarizeChildTypes algebra schema group (childParentTypes schema group)
    traversal.summaryVariableValues

def summarizedGroup (algebra : Algebra) (schema : Schema)
    (traversal : Traversal) (group : CollectedFieldGroup)
    : algebra.Summary :=
  algebra.field group (summarizedChildren algebra schema traversal group)

def summarizeCollectedChildren (algebra : Algebra) (schema : Schema)
    (traversal : Traversal)
    : List CollectedFieldGroup -> algebra.Summary
  | [] => algebra.empty
  | group :: rest =>
      algebra.combine (summarizedChildren algebra schema traversal group)
        (summarizeCollectedChildren algebra schema traversal rest)

def summarizeCollectedGroups (algebra : Algebra) (schema : Schema) (traversal : Traversal)
    : List CollectedFieldGroup -> algebra.Summary
  | [] => algebra.empty
  | group :: rest =>
      algebra.combine (summarizedGroup algebra schema traversal group)
        (summarizeCollectedGroups algebra schema traversal rest)

theorem foldChildSummaries_eq_summarizeCollectedChildren
    (algebra : Algebra) (schema : Schema) (traversal : Traversal)
    (groups : List CollectedFieldGroup)
    : foldChildSummaries algebra (summarizedChildren algebra schema traversal) groups
      = summarizeCollectedChildren algebra schema traversal groups := by
  induction groups with
  | nil => rfl
  | cons group rest =>
      simp [foldChildSummaries, summarizeCollectedChildren, *]

theorem foldFieldGroups_eq_summarizeCollectedGroups
    (algebra : Algebra) (schema : Schema) (traversal : Traversal)
    (groups : List CollectedFieldGroup)
    : foldFieldGroups algebra (summarizedChildren algebra schema traversal) groups
      = summarizeCollectedGroups algebra schema traversal groups := by
  induction groups with
  | nil => rfl
  | cons group rest =>
      simp [foldFieldGroups, summarizeCollectedGroups, summarizedGroup, *]

-- Proof-only traversal that resolves type conditions against one concrete runtime
-- object while preserving the supplied Boolean traversal policy.
def Traversal.includeBranchAtRuntimeType (traversal : Traversal) (schema : Schema)
    (runtimeType : Name) (branch : BranchCondition)
    : Bool :=
  match branch with
  | .typeCondition typeName => schema.typeIncludesObjectBool typeName runtimeType
  | .booleanLiteral _literal => traversal.includeBranch branch

def Traversal.atRuntimeType (traversal : Traversal) (schema : Schema) (runtimeType : Name)
    : Traversal :=
  {
    includeBranch := traversal.includeBranchAtRuntimeType schema runtimeType
    summaryVariableValues := traversal.summaryVariableValues
  }

-----------------------------------------------------------------------------------------
-- Extracted condition-group invariants
-----------------------------------------------------------------------------------------

mutual
  theorem traversedConditionGroups_sublist_nodeConditions
      (tree : Tree) (traversal : Traversal)
      : (traversedConditionGroups tree traversal).Sublist tree.nodeConditions := by
    rw [traversedConditionGroups, Tree.nodeConditions]
    exact List.Sublist.cons_cons tree.condition
      (traversedBranchConditionGroups_sublist_branchNodeConditions tree.branches
        traversal)
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem traversedBranchConditionGroups_sublist_branchNodeConditions
      (branches : List (Branch Tree)) (traversal : Traversal)
      : (traversedBranchConditionGroups branches traversal).Sublist
          (branchNodeConditions branches) := by
    cases branches with
    | nil =>
        simp [traversedBranchConditionGroups, branchNodeConditions]
    | cons branch rest =>
        rw [traversedBranchConditionGroups, branchNodeConditions]
        cases hinclude : traversal.includeBranch branch.condition with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
            exact (traversedBranchConditionGroups_sublist_branchNodeConditions rest
                    traversal).trans
                    (List.sublist_append_right branch.body.nodeConditions
                      (branchNodeConditions rest))
        | true =>
            simp only [↓reduceIte]
            exact (traversedConditionGroups_sublist_nodeConditions branch.body
                    traversal).append
                    (traversedBranchConditionGroups_sublist_branchNodeConditions rest
                      traversal)
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

mutual
  theorem visitedSiblingConditionGroupsDisjointInTree_of_nodeConditionsNodup
      (tree : Tree) (traversal : Traversal)
      (hnodup : tree.nodeConditions.Nodup)
      : visitedSiblingConditionGroupsDisjointInTree tree traversal := by
    rw [visitedSiblingConditionGroupsDisjointInTree]
    rw [Tree.nodeConditions] at hnodup
    exact visitedSiblingConditionGroupsDisjoint_of_branchNodeConditionsNodup
      tree.branches traversal (List.nodup_cons.mp hnodup).2
  termination_by 2 * sizeOf tree + 1
  decreasing_by
    cases tree
    simp_all
    omega

  theorem visitedSiblingConditionGroupsDisjoint_of_branchNodeConditionsNodup
      (branches : List (Branch Tree)) (traversal : Traversal)
      (hnodup : (branchNodeConditions branches).Nodup)
      : visitedSiblingConditionGroupsDisjoint branches traversal := by
    cases branches with
    | nil =>
        simp [visitedSiblingConditionGroupsDisjoint]
    | cons branch rest =>
        rw [branchNodeConditions] at hnodup
        rcases List.nodup_append.mp hnodup with
          ⟨hbody, hrest, hbodyRest⟩
        rw [visitedSiblingConditionGroupsDisjoint]
        cases hinclude : traversal.includeBranch branch.condition with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, true_and]
            refine ⟨?_, ?_⟩
            · intro condition hcurrent
              simp at hcurrent
            · exact
                visitedSiblingConditionGroupsDisjoint_of_branchNodeConditionsNodup
                  rest traversal hrest
        | true =>
            simp only [↓reduceIte]
            refine ⟨?_, ?_, ?_⟩
            · intro condition hcurrent hremaining
              have hcurrentNode : condition ∈ branch.body.nodeConditions :=
                (traversedConditionGroups_sublist_nodeConditions branch.body traversal).mem
                  hcurrent
              have hremainingNode : condition ∈ branchNodeConditions rest :=
                (traversedBranchConditionGroups_sublist_branchNodeConditions rest
                    traversal).mem hremaining
              exact hbodyRest condition hcurrentNode condition hremainingNode rfl
            · exact
                visitedSiblingConditionGroupsDisjointInTree_of_nodeConditionsNodup
                  branch.body traversal hbody
            · exact
                visitedSiblingConditionGroupsDisjoint_of_branchNodeConditionsNodup
                  rest traversal hrest
  termination_by 2 * sizeOf branches
  decreasing_by
    all_goals
      try subst branches
      cases branch
      simp_wf
      omega
end

end Syntactic
end TreeSummary
end GraphQL
