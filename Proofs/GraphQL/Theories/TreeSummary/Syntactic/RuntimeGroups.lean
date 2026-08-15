import Proofs.GraphQL.Theories.TreeSummary.Syntactic.RuntimePath

/-! Runtime-selected Syntactic field groups and their algebraic folds. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.Execution
open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open TreeSummary.Measure

universe u v

-----------------------------------------------------------------------------------------
-- Runtime traversal and collected groups
-----------------------------------------------------------------------------------------

def runtimeBooleanDefault (source : VariableValues) (variableName : Name) : Bool :=
  (inputValueBoolean? source (.variable variableName)).getD false

-- A proof-only fixed traversal matching concrete values and choosing `false` for an
-- unknown Boolean. This matches directive execution: an unknown value rejects a
-- positive `@include` literal and selects a negative `@skip` literal.
def Traversal.withRuntimeBooleanDefaults (source : VariableValues)
    (summaryVariableValues : VariableValues := [])
    : Traversal :=
  {
    includeBranch :=
      fun branch =>
        match branch with
        | .typeCondition _typeName => true
        | .booleanLiteral literal =>
            runtimeBooleanDefault source literal.variableName == literal.requiredValue
    summaryVariableValues
  }

mutual
  def traversedCollectedGroups (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (traversal : Traversal)
      : List CollectedFieldGroup :=
    collectFieldGroups inheritedBooleanCondition tree.condition tree.fields
    ++ traversedBranchCollectedGroups parentType inheritedBooleanCondition
        tree.branches traversal
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def traversedBranchCollectedGroups (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree)) (traversal : Traversal)
      : List CollectedFieldGroup :=
    match branches with
    | [] => []
    | branch :: rest =>
        let current :=
          if traversal.includeBranch branch.condition then
            traversedCollectedGroups (branch.condition.parentType parentType)
              inheritedBooleanCondition branch.body traversal
          else
            []
        current
        ++ traversedBranchCollectedGroups parentType inheritedBooleanCondition rest
            traversal
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

def candidateChildGroups (schema : Schema) (childParentType childRuntimeType : Name)
    (traversal : Traversal) (group : CollectedFieldGroup)
    : List CollectedFieldGroup :=
  traversedCollectedGroups childParentType group.childInheritedBooleanCondition
    (group.childTreeWithKnownFalsePruning schema childParentType
      traversal.summaryVariableValues)
    (traversal.atRuntimeType schema childRuntimeType)

def candidateChildGroupsFor (schema : Schema) (childParentType childRuntimeType : Name)
    (traversal : Traversal) (groups : List CollectedFieldGroup)
    : List CollectedFieldGroup :=
  groups.flatMap (candidateChildGroups schema childParentType childRuntimeType traversal)

def groupsWithResponseName (responseName : Name) (groups : List CollectedFieldGroup)
    : List CollectedFieldGroup :=
  groups.filter fun group => group.responseName == responseName

def groupsWithoutResponseName (responseName : Name) (groups : List CollectedFieldGroup)
    : List CollectedFieldGroup :=
  groups.filter fun group => !(group.responseName == responseName)

def activeGroupsWithResponseName (variableValues : VariableValues)
    (runtimeType responseName : Name) (groups : List CollectedFieldGroup)
    : List CollectedFieldGroup :=
  groups.filter
    fun group =>
      group.responseName == responseName
      && group.condition.allows variableValues runtimeType

mutual
  theorem traversedCollectedGroup_shape
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (traversal : Traversal) (group : CollectedFieldGroup)
      (hgroup
        : group
          ∈ traversedCollectedGroups parentType inheritedBooleanCondition tree traversal)
      : group.selections ≠ []
        ∧ ∀ selection,
            selection ∈ group.selections
            -> ∃ field : Field,
                selection = field.toSelection group.responseName
                ∧ (group.condition, selection) ∈ tree.fieldEntries := by
    simp only [traversedCollectedGroups, List.mem_append] at hgroup
    cases hgroup with
    | inl hlocal =>
        rcases List.mem_map.mp hlocal with ⟨fieldGroup, hfieldGroup, rfl⟩
        constructor
        · exact CollectedFieldGroup.selections_ne_nil _
        · intro selection hselection
          rcases List.mem_map.mp hselection with ⟨field, hfield, rfl⟩
          refine ⟨field, rfl, ?_⟩
          rw [Tree.fieldEntries]
          apply List.mem_append_left
          apply List.mem_flatMap.mpr
          refine ⟨fieldGroup, hfieldGroup, ?_⟩
          exact List.mem_map.mpr
            ⟨field.toSelection fieldGroup.responseName,
              List.mem_map.mpr ⟨field, hfield, rfl⟩, rfl⟩
    | inr hbranches =>
        refine ⟨
          (traversedBranchCollectedGroup_shape parentType inheritedBooleanCondition
            tree.branches traversal group hbranches).1, ?_⟩
        intro selection hselection
        have hshape := (traversedBranchCollectedGroup_shape parentType
          inheritedBooleanCondition tree.branches traversal group hbranches).2
          selection hselection
        rcases hshape with ⟨field, heq, hentry⟩
        refine ⟨field, heq, ?_⟩
        rw [Tree.fieldEntries]
        exact List.mem_append_right _ hentry
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem traversedBranchCollectedGroup_shape
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (branches : List (Branch Tree)) (traversal : Traversal)
      (group : CollectedFieldGroup)
      (hgroup
        : group
          ∈ traversedBranchCollectedGroups parentType
              inheritedBooleanCondition branches traversal)
      : group.selections ≠ []
        ∧ ∀ selection,
            selection ∈ group.selections
            -> ∃ field : Field,
                selection = field.toSelection group.responseName
                ∧ (group.condition, selection) ∈ branchFieldEntries branches := by
    cases branches with
    | nil => simp [traversedBranchCollectedGroups] at hgroup
    | cons branch rest =>
        simp only [traversedBranchCollectedGroups, List.mem_append] at hgroup
        cases hgroup with
        | inl hbody =>
            cases hinclude : traversal.includeBranch branch.condition with
            | false => simp [hinclude] at hbody
            | true =>
                have hshape := traversedCollectedGroup_shape
                  (branch.condition.parentType parentType) inheritedBooleanCondition
                  branch.body traversal group (by simpa [hinclude] using hbody)
                refine ⟨hshape.1, ?_⟩
                intro selection hselection
                rcases hshape.2 selection hselection with ⟨field, heq, hentry⟩
                refine ⟨field, heq, ?_⟩
                simp only [branchFieldEntries, List.mem_append]
                exact Or.inl hentry
        | inr hrest =>
            have hshape := traversedBranchCollectedGroup_shape parentType
              inheritedBooleanCondition rest traversal group hrest
            refine ⟨hshape.1, ?_⟩
            intro selection hselection
            rcases hshape.2 selection hselection with ⟨field, heq, hentry⟩
            refine ⟨field, heq, ?_⟩
            simp only [branchFieldEntries, List.mem_append]
            exact Or.inr hentry
  termination_by sizeOf branches
  decreasing_by
    all_goals
      try subst branches
      cases branch
      simp_wf
      omega
end

theorem summarizeCollectedGroups_filter_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (traversal : Traversal)
    (keep : CollectedFieldGroup -> Bool) (groups : List CollectedFieldGroup)
    : lawful.le
        (summarizeCollectedGroups algebra schema traversal (groups.filter keep))
        (summarizeCollectedGroups algebra schema traversal groups) := by
  induction groups with
  | nil => exact lawful.le_refl _
  | cons group rest ih =>
      cases hkeep : keep group with
      | false =>
          simp only [List.filter_cons, hkeep, Bool.false_eq_true, if_false,
            summarizeCollectedGroups]
          apply lawful.le_trans _ _ _ ih
          have hadded := lawful.combine_mono
            algebra.empty
            (summarizedGroup algebra schema traversal group)
            (summarizeCollectedGroups algebra schema traversal rest)
            (summarizeCollectedGroups algebra schema traversal rest)
            (lawful.empty_le _) (lawful.le_refl _)
          simpa only [lawful.empty_combine] using hadded
      | true =>
          simp only [List.filter_cons, hkeep, if_true, summarizeCollectedGroups]
          exact
            _root_.GraphQL.TreeSummary.Algebra.Lawful.combine_right_mono
              lawful _ ih

theorem summarizeCollectedGroups_partition_responseName
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (traversal : Traversal)
    (responseName : Name) (groups : List CollectedFieldGroup)
    : summarizeCollectedGroups algebra schema traversal groups
      = algebra.combine
          (summarizeCollectedGroups algebra schema traversal
            (groupsWithResponseName responseName groups))
          (summarizeCollectedGroups algebra schema traversal
            (groupsWithoutResponseName responseName groups)) := by
  unfold groupsWithResponseName groupsWithoutResponseName
  induction groups with
  | nil =>
      simp [summarizeCollectedGroups, lawful.empty_combine]
  | cons group rest ih =>
      by_cases hname : group.responseName = responseName
      · simp only [List.filter_cons, hname, beq_self_eq_true, Bool.not_true,
          Bool.false_eq_true, if_false, if_true, summarizeCollectedGroups]
        rw [ih]
        exact (lawful.combine_assoc _ _ _).symm
      · have hbeq : (group.responseName == responseName) = false := by
          simp [hname]
        simp only [List.filter_cons, hbeq, Bool.false_eq_true, if_false, Bool.not_false,
          if_true, summarizeCollectedGroups]
        rw [ih]
        calc
          algebra.combine
                (summarizedGroup algebra schema traversal group)
                (algebra.combine
                  (summarizeCollectedGroups algebra schema traversal
                    (List.filter
                      (fun candidate => candidate.responseName == responseName) rest))
                  (summarizeCollectedGroups algebra schema traversal
                    (List.filter
                      (fun candidate => !(candidate.responseName == responseName)) rest)))
              = algebra.combine
                  (algebra.combine
                    (summarizedGroup algebra schema traversal group)
                    (summarizeCollectedGroups algebra schema traversal
                      (List.filter
                        (fun candidate => candidate.responseName == responseName) rest)))
                  (summarizeCollectedGroups algebra schema traversal
                    (List.filter
                      (fun candidate => !(candidate.responseName == responseName))
                      rest)) :=
            (lawful.combine_assoc _ _ _).symm
          _ = algebra.combine
                (algebra.combine
                  (summarizeCollectedGroups algebra schema traversal
                    (List.filter
                      (fun candidate => candidate.responseName == responseName) rest))
                  (summarizedGroup algebra schema traversal group))
                (summarizeCollectedGroups algebra schema traversal
                  (List.filter
                    (fun candidate => !(candidate.responseName == responseName))
                    rest)) := by
            rw [lawful.combine_comm
              (summarizedGroup algebra schema traversal group)]
          _ = algebra.combine
                (summarizeCollectedGroups algebra schema traversal
                  (List.filter
                    (fun candidate => candidate.responseName == responseName) rest))
                (algebra.combine
                  (summarizedGroup algebra schema traversal group)
                  (summarizeCollectedGroups algebra schema traversal
                    (List.filter
                      (fun candidate => !(candidate.responseName == responseName))
                      rest))) :=
            lawful.combine_assoc _ _ _

theorem activeGroupsWithResponseName_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (traversal : Traversal)
    (variableValues : VariableValues) (runtimeType responseName : Name)
    (groups : List CollectedFieldGroup)
    : lawful.le
        (summarizeCollectedGroups algebra schema traversal
          (activeGroupsWithResponseName variableValues runtimeType responseName groups))
        (summarizeCollectedGroups algebra schema traversal
          (groupsWithResponseName responseName groups)) := by
  unfold activeGroupsWithResponseName groupsWithResponseName
  induction groups with
  | nil => exact lawful.le_refl _
  | cons group rest ih =>
      cases hname : group.responseName == responseName with
      | false =>
          simp only [List.filter_cons, hname, Bool.false_and,
            Bool.false_eq_true, if_false]
          exact ih
      | true =>
          cases hcondition : group.condition.allows variableValues runtimeType with
          | false =>
              simp only [List.filter_cons, hname, Bool.true_and, hcondition,
                Bool.false_eq_true, if_false, if_true, summarizeCollectedGroups]
              apply lawful.le_trans _ _ _ ih
              have hadded := lawful.combine_mono
                algebra.empty
                (summarizedGroup algebra schema traversal group)
                (summarizeCollectedGroups algebra schema traversal
                  (List.filter
                    (fun candidate => candidate.responseName == responseName) rest))
                (summarizeCollectedGroups algebra schema traversal
                  (List.filter
                    (fun candidate => candidate.responseName == responseName) rest))
                (lawful.empty_le _) (lawful.le_refl _)
              simpa only [lawful.empty_combine] using hadded
          | true =>
              simp only [List.filter_cons, hname, Bool.true_and, hcondition,
                if_true, summarizeCollectedGroups]
              exact
                _root_.GraphQL.TreeSummary.Algebra.Lawful.combine_right_mono
                  lawful _ ih

end Syntactic
end TreeSummary
end GraphQL
