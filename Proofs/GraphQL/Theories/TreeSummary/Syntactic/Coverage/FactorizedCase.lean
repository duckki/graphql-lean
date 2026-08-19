import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Coverage.RuntimeSummary

/-! Factorized-case coverage of each concrete Syntactic runtime summary. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.Execution
open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open TreeSummary.Measure

universe u v
-- One concrete runtime case is covered by the factorized local case circuit. This is
-- the soundness bridge used by the fast backend; it needs neither least joins nor
-- distributivity.
mutual
  theorem summarizeTreeAtRuntimeType_le
      (algebra : Algebra.{v}) (lawful : algebra.Lawful)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (tree : Tree) (typeScope : PossibleTypes) (runtimeType : Name)
      (hcoherent : tree.BranchesCoherent schema inheritedBooleanCondition)
      (hscopeMem : runtimeType ∈ typeScope)
      (htreeMem : runtimeType ∈ tree.condition.possibleTypes)
      (source summaryVariableValues : VariableValues)
      (hvalues : BooleanValuesMatchRuntime source summaryVariableValues)
      : lawful.le
          (summarizeTreeAtRuntimeType algebra schema parentType
            inheritedBooleanCondition runtimeType tree
            (Traversal.withRuntimeBooleanDefaults source summaryVariableValues))
          (summarizeTree algebra schema parentType
            inheritedBooleanCondition tree summaryVariableValues typeScope) := by
    let summaries :=
      summarizeImmediateBranches algebra schema parentType inheritedBooleanCondition
        tree.branches summaryVariableValues typeScope
    have hbranches :=
      summarizeBranchesAtRuntimeType_le_compact algebra lawful schema
        parentType inheritedBooleanCondition tree.condition runtimeType
        tree.branches source summaryVariableValues hvalues typeScope
        (by simpa [Tree.BranchesCoherent] using hcoherent) htreeMem hscopeMem
    have htype : lawful.le
        ((summarizeTypeBranchCase? algebra runtimeType summaries.typeBranches).getD
          algebra.empty)
        (summarizeTypeRuntimeCases algebra typeScope
          summaries.typeBranches) := by
      exact summarizeSelectedTypeBranches_le_runtimeCases algebra lawful
        typeScope runtimeType summaries.typeBranches hscopeMem
    have hbool : lawful.le
        (summarizeSelectedBooleanBranches algebra (runtimeBooleanAssignment source)
          summaries.booleanBranches)
        (summarizeBooleanBranchSummaries algebra summaryVariableValues
          summaries.booleanBranches) := by
      exact summarizeSelectedBooleanBranches_le algebra lawful
        (runtimeBooleanAssignment source) summaryVariableValues
        (runtimeBooleanAssignment_matches source summaryVariableValues hvalues)
        summaries.booleanBranches
    rw [summarizeTreeAtRuntimeType, summarizeTree, summarizeBranches]
    apply lawful.combine_mono
    · exact lawful.le_refl _
    · exact lawful.le_trans _ _ _ hbranches
        (lawful.combine_mono _ _ _ _ htype hbool)
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem summarizeBranchesAtRuntimeType_le_compact
      (algebra : Algebra.{v}) (lawful : algebra.Lawful)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (parentCondition : Condition) (runtimeType : Name)
      (branches : List (Branch Tree)) (source summaryVariableValues : VariableValues)
      (hvalues : BooleanValuesMatchRuntime source summaryVariableValues)
      (typeScope : PossibleTypes)
      (hcoherent
        : branchesCoherent schema inheritedBooleanCondition parentCondition branches)
      (hparentMem : runtimeType ∈ parentCondition.possibleTypes)
      (hscopeMem : runtimeType ∈ typeScope)
      : lawful.le
          (summarizeBranchesAtRuntimeType algebra schema parentType
            inheritedBooleanCondition runtimeType branches
            (Traversal.withRuntimeBooleanDefaults source summaryVariableValues))
          ( let summaries :=
              summarizeImmediateBranches algebra schema parentType
                inheritedBooleanCondition branches summaryVariableValues typeScope
            algebra.combine
              ((summarizeTypeBranchCase? algebra runtimeType summaries.typeBranches).getD
                algebra.empty)
              (summarizeSelectedBooleanBranches algebra (runtimeBooleanAssignment source)
                summaries.booleanBranches)) := by
    cases hbranches : branches with
    | nil =>
        simp [summarizeBranchesAtRuntimeType, summarizeImmediateBranches,
          summarizeTypeBranchCase?, summarizeSelectedBooleanBranches,
          lawful.empty_combine, lawful.le_refl]
    | cons branch rest =>
        rw [hbranches] at hcoherent
        rw [branchesCoherent] at hcoherent
        rcases hcoherent with ⟨htransition, hbodyCoherent, hrestCoherent⟩
        let tailSummaries :=
          summarizeImmediateBranches algebra schema parentType
            inheritedBooleanCondition rest summaryVariableValues typeScope
        let tailTypeSummary :=
          (summarizeTypeBranchCase? algebra runtimeType
            tailSummaries.typeBranches).getD algebra.empty
        let tailBooleanSummary :=
          summarizeSelectedBooleanBranches algebra (runtimeBooleanAssignment source)
            tailSummaries.booleanBranches
        have hrest : lawful.le
            (summarizeBranchesAtRuntimeType algebra schema parentType
              inheritedBooleanCondition runtimeType rest
              (Traversal.withRuntimeBooleanDefaults source summaryVariableValues))
            (algebra.combine tailTypeSummary tailBooleanSummary) := by
          simpa [tailSummaries, tailTypeSummary, tailBooleanSummary] using
            summarizeBranchesAtRuntimeType_le_compact algebra lawful schema parentType
              inheritedBooleanCondition parentCondition runtimeType rest source
              summaryVariableValues hvalues typeScope hrestCoherent hparentMem hscopeMem
        rw [summarizeBranchesAtRuntimeType, summarizeImmediateBranches]
        cases hcondition : branch.condition with
        | typeCondition typeName =>
            let branchScope :=
              intersectPossibleTypes typeScope branch.body.condition.possibleTypes
            have hpossibleTypes := typeBranchBody_possibleTypes_eq schema
              inheritedBooleanCondition parentCondition branch.body.condition typeName
              (by simpa [hcondition] using htransition)
            cases hempty : branchScope.isEmpty with
            | true =>
                have hinclude : schema.typeIncludesObjectBool typeName runtimeType = false := by
                  cases hvalue : schema.typeIncludesObjectBool typeName runtimeType with
                  | false => rfl
                  | true =>
                      have hbodyMem := runtimeType_mem_typeBranchBody schema
                        inheritedBooleanCondition parentCondition branch.body.condition
                        typeName runtimeType (by simpa [hcondition] using htransition)
                        hparentMem hvalue
                      have hbranchScope : runtimeType ∈ branchScope := by
                        exact List.mem_filter.mpr
                          ⟨hscopeMem, List.contains_iff_mem.mpr hbodyMem⟩
                      have hnonempty : branchScope.isEmpty = false :=
                        List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hbranchScope)
                      rw [hempty] at hnonempty
                      contradiction
                simpa [hcondition, branchScope, hempty,
                  Traversal.includeBranchAtRuntimeType, hinclude,
                  tailSummaries, tailTypeSummary, tailBooleanSummary,
                  lawful.empty_combine] using hrest
            | false =>
                cases hinclude : schema.typeIncludesObjectBool typeName runtimeType with
                | false =>
                    have hnotType :
                        runtimeType ∉ schema.getPossibleTypes typeName := by
                      intro hmem
                      have htrue :
                          schema.typeIncludesObjectBool typeName runtimeType = true := by
                        exact List.contains_iff_mem.mpr hmem
                      rw [hinclude] at htrue
                      contradiction
                    have hnotBody : runtimeType ∉ branch.body.condition.possibleTypes := by
                      rw [hpossibleTypes, intersectPossibleTypes]
                      simp [hparentMem, hnotType]
                    have hnotScope : runtimeType ∉ branchScope := by
                      simp [branchScope, intersectPossibleTypes, hscopeMem, hnotBody]
                    have htypeHead :
                        (summarizeTypeBranchCase? algebra runtimeType
                          ({
                            possibleTypes := branchScope
                            summary := summarizeTree algebra schema typeName
                              inheritedBooleanCondition branch.body
                              summaryVariableValues branchScope
                          } :: tailSummaries.typeBranches)).getD algebra.empty
                          = tailTypeSummary := by
                      rw [summarizeTypeBranchCase?_getD_cons algebra lawful runtimeType,
                        if_neg hnotScope]
                    simpa [hcondition, branchScope, hempty,
                      Traversal.includeBranchAtRuntimeType, hinclude,
                      htypeHead,
                      tailSummaries, tailTypeSummary, tailBooleanSummary,
                      lawful.empty_combine] using hrest
                | true =>
                    have hbodyMem := runtimeType_mem_typeBranchBody schema
                      inheritedBooleanCondition parentCondition branch.body.condition
                      typeName runtimeType (by simpa [hcondition] using htransition)
                      hparentMem hinclude
                    have hbranchScope : runtimeType ∈ branchScope := by
                      exact List.mem_filter.mpr
                        ⟨hscopeMem, List.contains_iff_mem.mpr hbodyMem⟩
                    have htypeHead :
                        (summarizeTypeBranchCase? algebra runtimeType
                          ({
                            possibleTypes := branchScope
                            summary := summarizeTree algebra schema typeName
                              inheritedBooleanCondition branch.body
                              summaryVariableValues branchScope
                          } :: tailSummaries.typeBranches)).getD algebra.empty
                          = algebra.combine
                              (summarizeTree algebra schema typeName
                                inheritedBooleanCondition branch.body
                                summaryVariableValues branchScope)
                              tailTypeSummary := by
                      rw [summarizeTypeBranchCase?_getD_cons algebra lawful runtimeType,
                        if_pos hbranchScope]
                    have hrecursive := summarizeTreeAtRuntimeType_le algebra lawful
                      schema typeName inheritedBooleanCondition branch.body branchScope
                      runtimeType hbodyCoherent hbranchScope hbodyMem source
                      summaryVariableValues hvalues
                    have hcombined := lawful.combine_mono _ _ _ _ hrecursive hrest
                    simpa [hcondition, branchScope, hempty,
                      Traversal.includeBranchAtRuntimeType, hinclude,
                      htypeHead,
                      tailSummaries, tailTypeSummary, tailBooleanSummary,
                      lawful.combine_assoc, BranchCondition.parentType] using hcombined
        | booleanLiteral literal =>
            have hbodyMem : runtimeType ∈ branch.body.condition.possibleTypes := by
              rw [booleanBranchBody_possibleTypes schema inheritedBooleanCondition
                parentCondition branch.body.condition literal
                (by simpa [hcondition] using htransition)]
              exact hparentMem
            cases hevaluation : evaluateBooleanLiteral? summaryVariableValues literal with
            | none =>
                cases hinclude
                      : (Traversal.withRuntimeBooleanDefaults source
                          summaryVariableValues).includeBranch
                          (.booleanLiteral literal) with
                | false =>
                    have hselected :
                        runtimeBooleanAssignment source literal.variableName
                          ≠ literal.requiredValue := by
                      cases literal <;>
                        simpa [runtimeBooleanAssignment,
                          Traversal.withRuntimeBooleanDefaults, runtimeBooleanDefault]
                          using hinclude
                    simpa [hcondition, hevaluation,
                      Traversal.includeBranchAtRuntimeType, hinclude, hselected,
                      summarizeSelectedBooleanBranches, tailSummaries, tailTypeSummary,
                      tailBooleanSummary, lawful.empty_combine] using hrest
                | true =>
                    have hselected :
                        runtimeBooleanAssignment source literal.variableName
                          = literal.requiredValue := by
                      cases literal <;>
                        simpa [runtimeBooleanAssignment,
                          Traversal.withRuntimeBooleanDefaults, runtimeBooleanDefault]
                          using hinclude
                    have hrecursive := summarizeTreeAtRuntimeType_le algebra lawful
                      schema parentType inheritedBooleanCondition branch.body typeScope
                      runtimeType hbodyCoherent hscopeMem hbodyMem source
                      summaryVariableValues hvalues
                    have hcombined := lawful.combine_mono _ _ _ _ hrecursive hrest
                    have hreorder : algebra.combine
                        (summarizeTree algebra schema parentType inheritedBooleanCondition
                          branch.body summaryVariableValues typeScope)
                        (algebra.combine tailTypeSummary tailBooleanSummary)
                      = algebra.combine tailTypeSummary
                          (algebra.combine
                            (summarizeTree algebra schema parentType
                              inheritedBooleanCondition branch.body summaryVariableValues
                              typeScope)
                            tailBooleanSummary) := by
                      simpa [lawful.empty_combine] using
                        (_root_.GraphQL.TreeSummary.Algebra.Lawful.combine_interchange
                          lawful algebra.empty
                          (summarizeTree algebra schema parentType
                            inheritedBooleanCondition branch.body summaryVariableValues
                            typeScope)
                          tailTypeSummary tailBooleanSummary)
                    rw [hreorder] at hcombined
                    simpa [hcondition, hevaluation,
                      Traversal.includeBranchAtRuntimeType, hinclude, hselected,
                      summarizeSelectedBooleanBranches, tailSummaries, tailTypeSummary,
                      tailBooleanSummary, BranchCondition.parentType] using hcombined
            | some value =>
                have hinclude := evaluateBooleanLiteral_eq_runtime_of_some source
                  summaryVariableValues hvalues literal value hevaluation
                cases value with
                | false =>
                    simpa [hcondition, hevaluation,
                      Traversal.includeBranchAtRuntimeType, hinclude,
                      tailSummaries, tailTypeSummary, tailBooleanSummary,
                      lawful.empty_combine] using hrest
                | true =>
                    have hselected :
                        runtimeBooleanAssignment source literal.variableName
                          = literal.requiredValue := by
                      cases literal <;>
                        simpa [runtimeBooleanAssignment,
                          Traversal.withRuntimeBooleanDefaults, runtimeBooleanDefault]
                          using hinclude
                    have hrecursive := summarizeTreeAtRuntimeType_le algebra lawful
                      schema parentType inheritedBooleanCondition branch.body typeScope
                      runtimeType hbodyCoherent hscopeMem hbodyMem source
                      summaryVariableValues hvalues
                    have hcombined := lawful.combine_mono _ _ _ _ hrecursive hrest
                    have hreorder : algebra.combine
                        (summarizeTree algebra schema parentType inheritedBooleanCondition
                          branch.body summaryVariableValues typeScope)
                        (algebra.combine tailTypeSummary tailBooleanSummary)
                      = algebra.combine tailTypeSummary
                          (algebra.combine
                            (summarizeTree algebra schema parentType
                              inheritedBooleanCondition branch.body summaryVariableValues
                              typeScope)
                            tailBooleanSummary) := by
                      simpa [lawful.empty_combine] using
                        (_root_.GraphQL.TreeSummary.Algebra.Lawful.combine_interchange
                          lawful algebra.empty
                          (summarizeTree algebra schema parentType
                            inheritedBooleanCondition branch.body summaryVariableValues
                            typeScope)
                          tailTypeSummary tailBooleanSummary)
                    rw [hreorder] at hcombined
                    simpa [hcondition, hevaluation,
                      Traversal.includeBranchAtRuntimeType, hinclude, hselected,
                      summarizeSelectedBooleanBranches, tailSummaries, tailTypeSummary,
                      tailBooleanSummary, BranchCondition.parentType] using hcombined
  termination_by sizeOf branches
  decreasing_by
    all_goals
      rw [hbranches]
      rcases branch with ⟨condition, body⟩
      rcases body with ⟨bodyCondition, fields, childBranches⟩
      simp_wf
      omega
end

theorem summarizeChildParentType_le
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (group : CollectedFieldGroup)
    (parentTypes : TypeNames) (childParentType : Name)
    (hchild : childParentType ∈ parentTypes)
    (variableValues : VariableValues)
    : lawful.le
        (summarizeTree algebra schema childParentType
          group.childInheritedBooleanCondition
          (group.childTreeWithKnownFalsePruning schema childParentType variableValues)
          variableValues)
        (summarizeChildTypes algebra schema group parentTypes variableValues) := by
  cases htypes : parentTypes with
  | nil => simp [htypes] at hchild
  | cons first rest =>
      rw [htypes] at hchild
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hchild
          subst childParentType
          rw [summarizeChildTypes, joinMap]
          exact lawful.le_refl _
      | cons next tail =>
          rw [summarizeChildTypes, joinMap]
          simp only [List.mem_cons] at hchild
          cases hchild with
          | inl hequal =>
              subst childParentType
              exact lawful.le_join_left _ _
          | inr hrest =>
              apply lawful.le_trans _
                (summarizeChildTypes algebra schema group (next :: tail)
                  variableValues)
              · exact summarizeChildParentType_le algebra lawful schema group
                  (next :: tail) childParentType
                  (by simpa only [List.mem_cons] using hrest) variableValues
              · simpa [summarizeChildTypes, joinMap] using
                  (lawful.le_join_right
                    (summarizeTree algebra schema first
                      group.childInheritedBooleanCondition
                      (group.childTreeWithKnownFalsePruning schema first variableValues)
                      variableValues)
                    (summarizeChildTypes algebra schema group (next :: tail)
                      variableValues))
termination_by sizeOf parentTypes
decreasing_by
  rw [htypes]
  simp_wf
  omega

theorem summarizeCollectedGroups_append
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (traversal : Traversal)
    (left right : List CollectedFieldGroup)
    : summarizeCollectedGroups algebra schema traversal (left ++ right)
      = algebra.combine
          (summarizeCollectedGroups algebra schema traversal left)
          (summarizeCollectedGroups algebra schema traversal right) := by
  induction left with
  | nil =>
      simpa [summarizeCollectedGroups] using
        (lawful.empty_combine
          (summarizeCollectedGroups algebra schema traversal right)).symm
  | cons group rest ih =>
      simp only [List.cons_append, summarizeCollectedGroups]
      rw [ih, lawful.combine_assoc]

mutual
  theorem summarize_traversedCollectedGroupsAtRuntimeType
      (algebra : Algebra.{v}) (lawful : algebra.Lawful)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (runtimeType : Name) (tree : Tree) (traversal : Traversal)
      : summarizeCollectedGroups algebra schema traversal
          (traversedCollectedGroups parentType inheritedBooleanCondition tree
            (traversal.atRuntimeType schema runtimeType))
        = summarizeTreeAtRuntimeType algebra schema parentType
            inheritedBooleanCondition runtimeType tree traversal := by
    rw [traversedCollectedGroups, summarizeTreeAtRuntimeType,
      summarizeCollectedGroups_append algebra lawful]
    congr 1
    · induction tree.fields with
      | nil =>
          simp [collectFieldGroups, summarizeCollectedGroups,
            summarizeFieldGroups, combineMap]
      | cons group rest ih =>
          simp only [collectFieldGroups, List.map_cons, summarizeCollectedGroups,
            summarizedGroup, summarizedChildren, summarizeFieldGroups, combineMap]
          simpa [collectFieldGroups, summarizeFieldGroups, combineMap] using congrArg
            (algebra.combine
              (algebra.field
                {
                  inheritedBooleanCondition
                  condition := tree.condition
                  fieldGroup := group
                }
                (summarizeChildTypes algebra schema {
                    inheritedBooleanCondition
                    condition := tree.condition
                    fieldGroup := group
                  }
                  (childParentTypes schema
                    {
                      inheritedBooleanCondition
                      condition := tree.condition
                      fieldGroup := group
                    })
                  traversal.summaryVariableValues))) ih
    · exact summarize_traversedBranchCollectedGroupsAtRuntimeType algebra lawful
        schema parentType inheritedBooleanCondition runtimeType tree.branches
        traversal
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  theorem summarize_traversedBranchCollectedGroupsAtRuntimeType
      (algebra : Algebra.{v}) (lawful : algebra.Lawful)
      (schema : Schema) (parentType : Name)
      (inheritedBooleanCondition : List BooleanLiteral)
      (runtimeType : Name) (branches : List (Branch Tree)) (traversal : Traversal)
      : summarizeCollectedGroups algebra schema traversal
          (traversedBranchCollectedGroups parentType inheritedBooleanCondition branches
            (traversal.atRuntimeType schema runtimeType))
        = summarizeBranchesAtRuntimeType algebra schema parentType
            inheritedBooleanCondition runtimeType branches traversal := by
    cases branches with
    | nil =>
        simp [traversedBranchCollectedGroups, summarizeCollectedGroups,
            summarizeBranchesAtRuntimeType]
    | cons branch rest =>
        rw [traversedBranchCollectedGroups, summarizeBranchesAtRuntimeType,
          summarizeCollectedGroups_append algebra lawful]
        cases hinclude
              : traversal.includeBranchAtRuntimeType schema runtimeType
                  branch.condition with
        | true =>
            simp only [Traversal.atRuntimeType, hinclude, if_true]
            congr 1
            · exact summarize_traversedCollectedGroupsAtRuntimeType algebra lawful schema
                (branch.condition.parentType parentType) inheritedBooleanCondition
                runtimeType branch.body traversal
            · exact summarize_traversedBranchCollectedGroupsAtRuntimeType algebra lawful
                schema parentType inheritedBooleanCondition runtimeType rest traversal
        | false =>
            simp only [Traversal.atRuntimeType, hinclude, Bool.false_eq_true, if_false,
              summarizeCollectedGroups]
            congr 1
            exact summarize_traversedBranchCollectedGroupsAtRuntimeType algebra lawful
              schema parentType inheritedBooleanCondition runtimeType rest traversal
  termination_by sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

theorem candidateChildGroupsFor_le_summarizeCollectedChildren
    (algebra : Algebra.{v}) (lawful : algebra.Lawful)
    (schema : Schema) (childParentType childRuntimeType : Name)
    (source summaryVariableValues : VariableValues) (traversal : Traversal)
    (hvalues : BooleanValuesMatchRuntime source summaryVariableValues)
    (htraversal
      : traversal = Traversal.withRuntimeBooleanDefaults source summaryVariableValues)
    (groups : List CollectedFieldGroup)
    (hpossible : childRuntimeType ∈ schema.getPossibleTypes childParentType)
    (hchild : ∀ group, group ∈ groups -> childParentType ∈ childParentTypes schema group)
    : lawful.le
        (summarizeCollectedGroups algebra schema traversal
          (candidateChildGroupsFor schema childParentType childRuntimeType traversal
            groups))
        (summarizeCollectedChildren algebra schema traversal groups) := by
  subst traversal
  induction groups with
  | nil => exact lawful.le_refl _
  | cons group rest ih =>
      simp only [candidateChildGroupsFor, List.flatMap_cons,
        summarizeCollectedGroups_append algebra lawful,
        summarizeCollectedChildren]
      apply lawful.combine_mono
      · unfold candidateChildGroups summarizedChildren
        change lawful.le
          (summarizeCollectedGroups algebra schema
            (Traversal.withRuntimeBooleanDefaults source summaryVariableValues)
            (traversedCollectedGroups childParentType
              group.childInheritedBooleanCondition
              (group.childTreeWithKnownFalsePruning schema childParentType
                summaryVariableValues)
              ((Traversal.withRuntimeBooleanDefaults source
                summaryVariableValues).atRuntimeType schema childRuntimeType)))
          (summarizeChildTypes algebra schema group (childParentTypes schema group)
            summaryVariableValues)
        rw [summarize_traversedCollectedGroupsAtRuntimeType algebra lawful schema
          childParentType group.childInheritedBooleanCondition childRuntimeType
          (group.childTreeWithKnownFalsePruning schema childParentType summaryVariableValues)
          (Traversal.withRuntimeBooleanDefaults source summaryVariableValues)]
        have hroot :
            (group.childTreeWithKnownFalsePruning schema childParentType
              summaryVariableValues).condition
              = rootCondition schema childParentType := by
          unfold CollectedFieldGroup.childTreeWithKnownFalsePruning
            ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
            ConditionTree.ofSelectionSetInScope
          rw [ConditionTree.Tree.insertSelections_condition]
          rfl
        have hrootMem :
            childRuntimeType
              ∈ (group.childTreeWithKnownFalsePruning schema childParentType
                summaryVariableValues).condition.possibleTypes := by
          rw [hroot]
          simpa [rootCondition] using hpossible
        apply lawful.le_trans _
          (summarizeTree algebra schema childParentType
            group.childInheritedBooleanCondition
            (group.childTreeWithKnownFalsePruning schema childParentType summaryVariableValues)
            summaryVariableValues)
        · exact summarizeTreeAtRuntimeType_le algebra lawful schema
            childParentType group.childInheritedBooleanCondition
            (group.childTreeWithKnownFalsePruning schema childParentType summaryVariableValues)
            (group.childTreeWithKnownFalsePruning schema childParentType
              summaryVariableValues).condition.possibleTypes
            childRuntimeType
            (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent schema
              childParentType group.childInheritedBooleanCondition summaryVariableValues
              group.mergedSelectionSet)
            hrootMem hrootMem source summaryVariableValues hvalues
        · exact summarizeChildParentType_le algebra lawful schema group
            (childParentTypes schema group) childParentType (hchild group (by simp))
            summaryVariableValues
      · exact ih (by
          intro candidate hcandidate
          exact hchild candidate (by simp [hcandidate]))
