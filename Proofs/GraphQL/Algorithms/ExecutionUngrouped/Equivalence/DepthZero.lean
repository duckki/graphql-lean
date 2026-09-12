import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Absorption

/-!
Depth-zero facts for ungrouped execution.

At zero completion depth, fresh response names write sentinel `null` values into the
response object and contribute one execution error. Later visits to the same response
name see the sentinel and contribute no new error. The proofs in this file therefore
separate status counting from intermediate response-object shape.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached

open GraphQL.Execution
open Eager

theorem executeCollectedFields_depth_zero_equivalence
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        GraphQL.Execution.executeCollectedFieldsData schema resolvers variableValues
          0 parentType source groups
        = []
  | [] => by
      simp [GraphQL.Execution.executeCollectedFieldsData,
        GraphQL.Execution.executeCollectedFields,
        GraphQL.Execution.Result.getD]
  | (_responseName, fields) :: rest => by
      cases fields with
      | nil =>
          have hrest :=
            executeCollectedFields_depth_zero_equivalence schema resolvers
              variableValues parentType source rest
          cases hresult :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 parentType source rest with
          | error errors =>
                simp [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, hresult]
          | ok result =>
              rcases result with ⟨fields, errors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, hresult] at hrest ⊢
      | cons _head _tail =>
          cases hresult :
              GraphQL.Execution.executeCollectedFields schema resolvers
                variableValues 0 parentType source rest with
          | error errors =>
                simp [GraphQL.Execution.executeCollectedFieldsData,
                  GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.getD, GraphQL.Execution.outOfFuel,
                  hresult]
          | ok result =>
              rcases result with ⟨fields, errors⟩
              simp [GraphQL.Execution.executeCollectedFieldsData,
                GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.getD, GraphQL.Execution.outOfFuel,
                hresult]

theorem executeCollectedFields_depth_zero_nonempty
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (parentType : Name)
    (source : ResolverValue ObjectIdentity)
    : ∀ groups,
        CollectedGroupsFieldsNonempty groups
        -> GraphQL.Execution.executeCollectedFields schema resolvers variableValues
              0 parentType source groups
            = match groups with
              | [] => .ok ([], 0)
              | _group :: _rest => .error groups.length
  | [], _hnonempty => by
      simp [GraphQL.Execution.executeCollectedFields]
  | (_responseName, fields) :: rest, hnonempty => by
      have hfields : fields ≠ [] :=
        hnonempty _responseName fields (by simp)
      have hrest :=
        executeCollectedFields_depth_zero_nonempty schema resolvers
          variableValues parentType source rest
          (CollectedGroupsFieldsNonempty_tail hnonempty)
      cases fields with
      | nil =>
          exact False.elim (hfields rfl)
      | cons _field _tail =>
          cases rest with
          | nil =>
                simp [GraphQL.Execution.executeCollectedFields,
                  GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                  GraphQL.Execution.Result.combine, GraphQL.Execution.outOfFuel]
          | cons _next _more =>
              simp [GraphQL.Execution.executeCollectedFields,
                GraphQL.Execution.executeField, GraphQL.Execution.Result.combine,
                GraphQL.Execution.Result.combine, GraphQL.Execution.outOfFuel]
                at hrest ⊢
              rw [hrest]
              simp [Nat.add_comm, Nat.add_left_comm]

private theorem addExecutableGroup_ne_nil
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : GraphQL.Execution.addExecutableGroup group groups ≠ [] := by
  cases groups with
  | nil =>
      simp [GraphQL.Execution.addExecutableGroup]
  | cons head tail =>
      rcases head with ⟨responseName, fields⟩
      simp only [GraphQL.Execution.addExecutableGroup]
      split <;> simp

private theorem mergeExecutableGroups_eq_nil_iff
    (left right : List (Name × List ExecutableField))
    : GraphQL.Execution.mergeExecutableGroups left right = []
      ↔ left = [] ∧ right = [] := by
  induction right generalizing left with
  | nil =>
      simp [GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        GraphQL.Execution.mergeExecutableGroups
            (GraphQL.Execution.addExecutableGroup group left) rest = []
          ↔ left = [] ∧ group :: rest = []
      rw [ih]
      constructor
      · intro h
        exact False.elim
          (addExecutableGroup_ne_nil group left h.1)
      · intro h
        simp at h

private def DepthZeroVisitMatchesCollection
    (groups : List (Name × List ExecutableField))
    (visited : ResponseValue × VisitStatus)
    : Prop :=
  (groups = [] ∧ visited = (.object [], visitOk))
  ∨ (groups ≠ [] ∧ ∃ output, visited = (output, .error 1))

mutual
  private theorem visitSelection_depth_zero_matches_collectSelection
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ selection,
          DepthZeroVisitMatchesCollection
            (GraphQL.Execution.collectSelection schema variableValues parentType
              source selection)
            (visitSelection schema resolvers variableValues 0 parentType source
              selection (.object []))
    | .field responseName fieldName arguments directives selectionSet => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · right
          constructor
          · simp [GraphQL.Execution.collectSelection, hallowed]
          · refine ⟨.object [(responseName, .null)], ?_⟩
            simp [visitSelection, hallowed, responseObjectField?,
              lookupResponseField?, mergeResponseFieldResult,
              mergeResponseFieldIntoObject, mergeResponseField,
              GraphQL.Execution.outOfFuel, resultValueOrNull, resultStatus]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · exact False.elim (hallowed h)
          left
          simp [GraphQL.Execution.collectSelection, visitSelection, hblocked,
            visitOk]
    | .inlineFragment none directives selectionSet => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · simpa [GraphQL.Execution.collectSelection, visitSelection, hallowed]
            using
              visitSubfields_depth_zero_matches_collectFields schema resolvers
                variableValues parentType source selectionSet
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · exact False.elim (hallowed h)
          left
          simp [GraphQL.Execution.collectSelection, visitSelection, hblocked,
            visitOk]
    | .inlineFragment (some typeCondition) directives selectionSet => by
        by_cases hallowed :
            selectionDirectivesAllowBool variableValues directives = true
        · by_cases happly :
              doesFragmentTypeApplyBool schema parentType source typeCondition =
                true
          · simpa [GraphQL.Execution.collectSelection, visitSelection, hallowed,
              happly]
              using
                visitSubfields_depth_zero_matches_collectFields schema resolvers
                  variableValues parentType source selectionSet
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  false := by
              cases h :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · rfl
              · exact False.elim (happly h)
            left
            simp [GraphQL.Execution.collectSelection, visitSelection, hallowed,
              hnotApply, visitOk]
        · have hblocked :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · exact False.elim (hallowed h)
          left
          simp [GraphQL.Execution.collectSelection, visitSelection, hblocked,
            visitOk]

  private theorem visitSubfields_depth_zero_matches_collectFields
      {ObjectIdentity : Type}
      (schema : Schema) (resolvers : Resolvers ObjectIdentity)
      (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectIdentity)
      : ∀ selectionSet,
          DepthZeroVisitMatchesCollection
            (GraphQL.Execution.collectFields schema variableValues parentType
              source selectionSet)
            (visitSubfields schema resolvers variableValues 0 parentType source
              selectionSet (.object []))
    | [] => by
        left
        simp [GraphQL.Execution.collectFields, visitSubfields, visitOk]
    | selection :: rest => by
        have hhead :=
          visitSelection_depth_zero_matches_collectSelection schema resolvers
            variableValues parentType source selection
        rcases hhead with ⟨hheadCollect, hheadVisit⟩
          | ⟨hheadCollect, output, hheadVisit⟩
        · have htail :=
            visitSubfields_depth_zero_matches_collectFields schema resolvers
              variableValues parentType source rest
          rcases htail with ⟨htailCollect, htailVisit⟩
            | ⟨htailCollect, output, htailVisit⟩
          · left
            constructor
            · simp [GraphQL.Execution.collectFields, hheadCollect, htailCollect,
                GraphQL.Execution.mergeExecutableGroups]
            · simp [visitSubfields, hheadVisit, htailVisit, combineVisitStatus,
                visitOk, GraphQL.Execution.Result.combine]
          · right
            constructor
            · intro hcollect
              have hnil :=
                (mergeExecutableGroups_eq_nil_iff
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType source selection)
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType source rest)).mp
                  (by simpa [GraphQL.Execution.collectFields] using hcollect)
              exact htailCollect hnil.2
            · refine ⟨output, ?_⟩
              simp [visitSubfields, hheadVisit, htailVisit, combineVisitStatus,
                visitOk, GraphQL.Execution.Result.combine]
        · right
          constructor
          · intro hcollect
            have hnil :=
              (mergeExecutableGroups_eq_nil_iff
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source selection)
                (GraphQL.Execution.collectFields schema variableValues
                  parentType source rest)).mp
                (by simpa [GraphQL.Execution.collectFields] using hcollect)
            exact hheadCollect hnil.1
          · refine ⟨output, ?_⟩
            simp [visitSubfields, hheadVisit]
end

theorem executeRootSelectionSet_depth_zero_aligned
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : RootSelectionResultAlignedEquivalent
        (executeRootSelectionSet schema resolvers variableValues 0 parentType
          source selectionSet)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers
          variableValues 0 parentType source selectionSet) := by
  have hvisit :=
    visitSubfields_depth_zero_matches_collectFields schema resolvers
      variableValues parentType source selectionSet
  rcases hvisit with ⟨hcollect, hvisit⟩
    | ⟨hcollect, output, hvisit⟩
  · simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
      hcollect, hvisit, GraphQL.Execution.executeCollectedFields, visitOk,
      RootSelectionResultAlignedEquivalent, ErrorPresenceEquivalent]
  · have hnonempty :
        CollectedGroupsFieldsNonempty
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet) :=
      collectFields_fieldsNonempty schema variableValues parentType source
        selectionSet
    have hspec :=
      executeCollectedFields_depth_zero_nonempty schema resolvers variableValues
        parentType source
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
        hnonempty
    cases hgroups
          : GraphQL.Execution.collectFields schema variableValues parentType source
              selectionSet with
    | nil =>
        exact False.elim (hcollect hgroups)
    | cons group rest =>
        simp [executeRootSelectionSet, GraphQL.Execution.executeRootSelectionSet,
          hvisit, hgroups] at hspec ⊢
        rw [hspec]
        simp [RootSelectionResultAlignedEquivalent, ErrorPresenceEquivalent]

end ExecutionUngroupedUncached
end Algorithms

end GraphQL
