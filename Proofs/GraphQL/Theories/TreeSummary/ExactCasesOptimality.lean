import GraphQL.Theories.TreeSummary.ExactCasesOptimality
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.Relation
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.ResolvedContext

/-! Best-bound induction for exact tree-summary traversal.

The public concrete side is an independent derivation relation. This module first proves
that a collecting algebra characterizes those derivations, then uses that algebra only
as a proof device for transporting localized best-transfer obligations.
-/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Execution
open TreeSummary.Measure
open Measure
open Optimality

universe u v

namespace CaseSemantics

-- Proof-only collecting interpretation of the independently defined structural cases.
-- `conditionTreeContextOutcomes_iff_collecting` below proves that the executable fold
-- neither invents nor omits derivations from the public relational semantics. It is
-- reducible so generic algebra folds expose `OutcomeSet` directly to proof elaboration.
@[reducible]
def collectingAlgebra (semantics : CaseSemantics.{u}) : Algebra.{u} :=
  {
    Summary := OutcomeSet semantics.Summary
    empty := OutcomeSet.singleton semantics.empty
    field :=
      fun group children =>
        OutcomeSet.bind children (semantics.fieldOutcomes group)
    combine := OutcomeSet.combine semantics.combine
    join := OutcomeSet.union
  }

end CaseSemantics

namespace BestTransferLaws

-- The local best-transfer laws form an algebra relation. Generic fold lemmas then
-- handle all list structure in the recursive exact-case proof.
def relation {semantics : CaseSemantics.{u}} {abstract : Algebra.{v}}
    (laws : BestTransferLaws semantics abstract)
    : Algebra.Relation semantics.collectingAlgebra abstract :=
  {
    related := BestBound laws.le laws.related
    empty_related := laws.empty_best
    combine_related := fun _ _ _ _ => laws.combine_best _ _ _ _
    field_related := fun group _ _ => laws.field_best group _ _
    join_related := fun _ _ _ _ => laws.join_best _ _ _ _
  }

end BestTransferLaws

namespace CaseForest

private theorem joinMap_collecting_of_mem
    {semantics : CaseSemantics.{u}} {items : List α}
    (summarize : α -> OutcomeSet semantics.Summary)
    {item : α} {outcome : semantics.Summary}
    (hitem : item ∈ items) (houtcome : summarize item outcome)
    : joinMap semantics.collectingAlgebra items
        (fun candidate _hcandidate => summarize candidate) outcome := by
  induction items generalizing item with
  | nil => simp at hitem
  | cons head rest ih =>
      cases rest with
      | nil =>
          simp only [List.mem_singleton] at hitem
          subst head
          rw [joinMap.eq_def]
          exact houtcome
      | cons next tail =>
          simp only [List.mem_cons] at hitem
          simp only [joinMap, CaseSemantics.collectingAlgebra, OutcomeSet.union]
          rcases hitem with rfl | hitem
          · exact Or.inl houtcome
          · exact Or.inr (ih (by simpa using hitem) houtcome)

private theorem combineMap_collecting_cons
    {semantics : CaseSemantics.{u}} (summarize : α -> OutcomeSet semantics.Summary)
    {head : α} {rest : List α} {headOutcome restOutcome : semantics.Summary}
    (hhead : summarize head headOutcome)
    (hrest
      : combineMap semantics.collectingAlgebra rest
          (fun candidate _hcandidate => summarize candidate) restOutcome)
    : combineMap semantics.collectingAlgebra (head :: rest)
        (fun candidate _hcandidate => summarize candidate)
        (semantics.combine headOutcome restOutcome) := by
  simp only [combineMap, CaseSemantics.collectingAlgebra, OutcomeSet.combine]
  exact ⟨headOutcome, restOutcome, hhead, hrest, rfl⟩

private theorem joinMap_collecting_cases
    {semantics : CaseSemantics.{u}} {items : List α}
    (summarize : α -> OutcomeSet semantics.Summary) {outcome : semantics.Summary}
    (houtcome
      : joinMap semantics.collectingAlgebra items
          (fun candidate _hcandidate => summarize candidate) outcome)
    : (items = [] ∧ outcome = semantics.empty)
      ∨ ∃ item, item ∈ items ∧ summarize item outcome := by
  induction items with
  | nil =>
      exact Or.inl ⟨rfl, by
        simpa [joinMap, CaseSemantics.collectingAlgebra,
          OutcomeSet.singleton] using houtcome⟩
  | cons head rest ih =>
      cases rest with
      | nil =>
          rw [joinMap.eq_def] at houtcome
          exact Or.inr ⟨head, by simp, houtcome⟩
      | cons next tail =>
          simp only [joinMap, CaseSemantics.collectingAlgebra,
            OutcomeSet.union] at houtcome
          rcases houtcome with hhead | hrest
          · exact Or.inr ⟨head, by simp, hhead⟩
          · rcases ih hrest with ⟨hempty, _houtcome⟩ | ⟨item, hitem, hitemOutcome⟩
            · simp at hempty
            · exact Or.inr ⟨item, by simp [hitem], hitemOutcome⟩

private theorem combineMap_collecting_cons_cases
    {semantics : CaseSemantics.{u}} (summarize : α -> OutcomeSet semantics.Summary)
    {head : α} {rest : List α} {outcome : semantics.Summary}
    (houtcome
      : combineMap semantics.collectingAlgebra (head :: rest)
          (fun candidate _hcandidate => summarize candidate) outcome)
    : ∃ headOutcome restOutcome,
        summarize head headOutcome
        ∧ combineMap semantics.collectingAlgebra rest
            (fun candidate _hcandidate => summarize candidate) restOutcome
        ∧ outcome = semantics.combine headOutcome restOutcome := by
  simpa only [combineMap, CaseSemantics.collectingAlgebra,
    OutcomeSet.combine] using houtcome

theorem BooleanDecision.collapse_collecting_iff_exists_evaluate
    {semantics : CaseSemantics.{u}}
    {variables : BooleanVariableNames}
    {decision : BooleanDecision (OutcomeSet semantics.Summary)}
    (hdecision : BooleanDecision.UsesOnly variables decision)
    (hvariables : variables.Nodup) (outcome : semantics.Summary)
    : decision.collapse semantics.collectingAlgebra outcome
      ↔ ∃ assignment : BooleanAssignment, decision.evaluate assignment outcome := by
  induction hdecision with
  | leaf variables summary =>
      constructor
      · intro houtcome
        exact ⟨fun _variableName => false, houtcome⟩
      · rintro ⟨_assignment, houtcome⟩
        exact houtcome
  | @split variables variableName onFalse onTrue hvariable hfalse htrue
      ihFalse ihTrue =>
      change (onFalse.collapse semantics.collectingAlgebra outcome
                ∨ onTrue.collapse semantics.collectingAlgebra outcome)
              ↔ ∃ assignment : BooleanAssignment,
                  (if assignment variableName then
                      onTrue.evaluate assignment
                    else
                      onFalse.evaluate assignment)
                    outcome
      constructor
      · intro houtcome
        rcases houtcome with hfalseOutcome | htrueOutcome
        · rcases (ihFalse (hvariables.erase variableName)).mp hfalseOutcome with
            ⟨assignment, hassignment⟩
          refine ⟨BooleanDecision.override assignment variableName false, ?_⟩
          simp only [BooleanDecision.override_self, Bool.false_eq_true, ↓reduceIte]
          rw [hfalse.evaluate_override_of_not_mem assignment variableName false
            hvariables.not_mem_erase]
          exact hassignment
        · rcases (ihTrue (hvariables.erase variableName)).mp htrueOutcome with
            ⟨assignment, hassignment⟩
          refine ⟨BooleanDecision.override assignment variableName true, ?_⟩
          simp only [BooleanDecision.override_self, ↓reduceIte]
          rw [htrue.evaluate_override_of_not_mem assignment variableName true
            hvariables.not_mem_erase]
          exact hassignment
      · rintro ⟨assignment, hassignment⟩
        by_cases hvalue : assignment variableName
        · exact Or.inr ((ihTrue (hvariables.erase variableName)).mpr
            ⟨assignment, by simpa [hvalue] using hassignment⟩)
        · exact Or.inl ((ihFalse (hvariables.erase variableName)).mpr
            ⟨assignment, by simpa [hvalue] using hassignment⟩)

-- Every independently derived lazy-context case is retained by the collecting
-- decision traversal under the same total truth assignment.
theorem ContextOutcome.toCollecting
    {semantics : CaseSemantics.{u}} {schema : Schema}
    {variableOrder remainingVariables : BooleanVariableNames}
    {assignment : BooleanAssignment} {environment : BooleanEnvironment}
    {parentType : Name} {inheritedBooleanCondition : List BooleanLiteral}
    {tree : CaseForest} {possibleTypes : PossibleTypeRegion}
    {outcome : semantics.Summary}
    (h
      : ContextOutcome semantics schema variableOrder remainingVariables assignment
          environment parentType inheritedBooleanCondition tree possibleTypes outcome)
    : (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
        remainingVariables parentType inheritedBooleanCondition tree possibleTypes
        environment).evaluate
        assignment outcome := by
  apply ContextOutcome.rec (semantics := semantics) (schema := schema)
    (motive_1 := fun remainingVariables assignment environment parentType
        inheritedBooleanCondition tree possibleTypes outcome _h =>
      (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
        remainingVariables parentType inheritedBooleanCondition tree possibleTypes
        environment).evaluate assignment outcome)
    (motive_2 := fun remainingVariables assignment environment groups
        outcome _h =>
      (CaseForest.summarizeFieldGroupsDecision semantics.collectingAlgebra schema
        variableOrder remainingVariables groups environment).evaluate assignment outcome)
    (motive_3 := fun remainingVariables assignment environment group
        parentTypes outcome _h =>
      (CaseForest.summarizeChildTypesDecision semantics.collectingAlgebra schema
        variableOrder remainingVariables group parentTypes environment).evaluate
        assignment outcome)
  case split =>
    intro remainingVariables assignment environment parentType
      inheritedBooleanCondition tree possibleTypes variableName outcome hbranches hnext
      _houtcome ih
    rw [CaseForest.summarizeDecision]
    rw [dif_pos hbranches, hnext]
    simp only [BooleanDecision.evaluate]
    by_cases hvalue : assignment variableName
    · simpa [hvalue] using ih
    · simpa [hvalue] using ih
  case noTypeRegion =>
    intro remainingVariables assignment environment parentType
      inheritedBooleanCondition tree possibleTypes hbranches hnext hregions
    rw [CaseForest.summarizeDecision]
    rw [dif_pos hbranches, hnext, CaseForest.summarizeTypeRegionsDecision,
      BooleanDecision.evaluate_joinMap, hregions]
    simp [joinMap, CaseSemantics.collectingAlgebra, OutcomeSet.singleton]
  case resolve =>
    intro remainingVariables assignment environment parentType
      inheritedBooleanCondition tree possibleTypes region outcome hbranches hnext hregion
      _houtcome ih
    rw [CaseForest.summarizeDecision]
    rw [dif_pos hbranches, hnext, CaseForest.summarizeTypeRegionsDecision,
      BooleanDecision.evaluate_joinMap]
    exact joinMap_collecting_of_mem
      (fun candidate =>
        (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
          remainingVariables parentType
          (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
            environment.variableValues)
          (tree.resolveBranches candidate environment.variableValues) candidate
          environment).evaluate assignment)
      hregion ih
  case fields =>
    intro remainingVariables assignment environment parentType
      inheritedBooleanCondition tree possibleTypes outcome hbranches _houtcome ih
    rw [CaseForest.summarizeDecision]
    simpa [hbranches] using ih
  case nil =>
    intro remainingVariables assignment environment
    rw [CaseForest.summarizeFieldGroupsDecision,
      BooleanDecision.evaluate_combineMap]
    simp [combineMap, CaseSemantics.collectingAlgebra, OutcomeSet.singleton]
  case cons =>
    intro remainingVariables assignment environment group rest children
      fieldOutcome restOutcome _hchildren hfield _hrest ihChildren ihRest
    rw [CaseForest.summarizeFieldGroupsDecision,
      BooleanDecision.evaluate_combineMap]
    simp only [BooleanDecision.evaluate_map]
    apply combineMap_collecting_cons
      (summarize := fun candidate =>
        OutcomeSet.bind
          ((CaseForest.summarizeChildTypesDecision semantics.collectingAlgebra schema
            variableOrder remainingVariables candidate (childParentTypes schema candidate)
            environment).evaluate assignment)
          (semantics.fieldOutcomes candidate))
    · exact ⟨children, ihChildren, hfield⟩
    · rw [CaseForest.summarizeFieldGroupsDecision,
        BooleanDecision.evaluate_combineMap] at ihRest
      simp only [BooleanDecision.evaluate_map] at ihRest
      exact ihRest
  case none =>
    intro remainingVariables assignment environment group
    rw [CaseForest.summarizeChildTypesDecision,
      BooleanDecision.evaluate_joinMap]
    simp [joinMap, CaseSemantics.collectingAlgebra, OutcomeSet.singleton]
  case some =>
    intro remainingVariables assignment environment group parentTypes
      childParentType outcome hparentType _houtcome ih
    rw [CaseForest.summarizeChildTypesDecision,
      BooleanDecision.evaluate_joinMap]
    exact joinMap_collecting_of_mem
      (fun candidate =>
        (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
          remainingVariables candidate group.childInheritedBooleanCondition
          (.ofConditionTree
            (group.childTreeWithKnownFalsePruning schema candidate
              environment.fixedVariableValues))
          (group.childTreeWithKnownFalsePruning schema candidate
            environment.fixedVariableValues).condition.possibleTypes
          environment).evaluate
          assignment)
      hparentType ih
  case t => exact h

private def contextCollectingCasePhase : Nat := 3
private def contextCollectingTypeRegionsPhase : Nat := 2
private def contextCollectingFieldGroupsPhase : Nat := 1
private def contextCollectingChildTypesPhase : Nat := 0

private def contextCollectingControlCount (tree : CaseForest)
    (remainingVariables : BooleanVariableNames)
    : Nat :=
  caseForestUnresolvedCount tree + remainingVariables.length

mutual
  theorem ContextOutcome.ofCollecting
      {semantics : CaseSemantics.{u}} {schema : Schema}
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : BooleanAssignment) (environment : BooleanEnvironment)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (outcome : semantics.Summary)
      (houtcome
        : (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
            remainingVariables parentType inheritedBooleanCondition tree possibleTypes
            environment).evaluate
            assignment outcome)
      : ContextOutcome semantics schema variableOrder remainingVariables assignment
          environment parentType inheritedBooleanCondition tree possibleTypes
          outcome := by
    rw [CaseForest.summarizeDecision] at houtcome
    split at houtcome <;> rename_i hbranches
    · cases hnext
            : environment.nextUnresolved remainingVariables tree.booleanVariables with
      | some variableName =>
          rw [hnext] at houtcome
          simp only [BooleanDecision.evaluate] at houtcome
          by_cases hvalue : assignment variableName
          · simp only [hvalue] at houtcome
            exact .split variableOrder remainingVariables assignment environment
              parentType inheritedBooleanCondition tree possibleTypes variableName outcome
              hbranches hnext
              (ContextOutcome.ofCollecting variableOrder
                (remainingVariables.erase variableName) assignment
                (environment.assign variableName (assignment variableName)) parentType
                inheritedBooleanCondition tree possibleTypes outcome
                (by simpa [hvalue] using houtcome))
          · simp only [hvalue] at houtcome
            exact .split variableOrder remainingVariables assignment environment
              parentType inheritedBooleanCondition tree possibleTypes variableName outcome
              hbranches hnext
              (ContextOutcome.ofCollecting variableOrder
                (remainingVariables.erase variableName) assignment
                (environment.assign variableName (assignment variableName)) parentType
                inheritedBooleanCondition tree possibleTypes outcome
                (by simpa [hvalue] using houtcome))
      | none =>
          rw [hnext, CaseForest.summarizeTypeRegionsDecision,
            BooleanDecision.evaluate_joinMap] at houtcome
          rcases contextTypeRegionsOfCollecting variableOrder remainingVariables
              assignment environment parentType inheritedBooleanCondition tree
              possibleTypes (tree.typeRegions possibleTypes) hbranches hnext outcome
              houtcome with
            ⟨hregions, houtcome⟩ | ⟨region, hregion, hregionOutcome⟩
          · subst outcome
            exact .noTypeRegion variableOrder remainingVariables assignment environment
              parentType inheritedBooleanCondition tree possibleTypes hbranches hnext
              hregions
          · exact .resolve variableOrder remainingVariables assignment environment
              parentType inheritedBooleanCondition tree possibleTypes region outcome
              hbranches hnext hregion hregionOutcome
    · exact .fields variableOrder remainingVariables assignment environment parentType
        inheritedBooleanCondition tree possibleTypes outcome (by simpa using hbranches)
        (contextFieldGroupsOfCollecting variableOrder remainingVariables assignment
          environment
          (tree.fieldGroups inheritedBooleanCondition possibleTypes) outcome
          houtcome)
  termination_by
    (
      caseForestResponseDepth tree,
      contextCollectingControlCount tree remainingVariables,
      contextCollectingCasePhase,
      0
    )
  decreasing_by
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact fieldGroupsResponseDepth_le inheritedBooleanCondition
          possibleTypes tree
      · unfold contextCollectingControlCount
        omega
      · decide
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · decide
    · apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_refl _
      · have hmem := List.mem_of_find?_eq_some hnext
        have hlength := List.length_erase_of_mem hmem
        have hpositive : 0 < remainingVariables.length :=
          List.length_pos_of_mem hmem
        unfold contextCollectingControlCount
        rw [hlength]
        omega
    · apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_refl _
      · have hmem := List.mem_of_find?_eq_some hnext
        have hlength := List.length_erase_of_mem hmem
        have hpositive : 0 < remainingVariables.length :=
          List.length_pos_of_mem hmem
        unfold contextCollectingControlCount
        rw [hlength]
        omega

  theorem contextTypeRegionsOfCollecting
      {semantics : CaseSemantics.{u}} {schema : Schema}
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : BooleanAssignment) (environment : BooleanEnvironment)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (_possibleTypes : PossibleTypeRegion)
      (regions : List PossibleTypeRegion)
      (_hbranches : tree.hasUnresolvedBranches = true)
      (_hnext
        : environment.nextUnresolved remainingVariables tree.booleanVariables = none)
      (outcome : semantics.Summary)
      (houtcome
        : joinMap semantics.collectingAlgebra regions
            (fun region _hregion =>
              (CaseForest.summarizeDecision semantics.collectingAlgebra schema
                variableOrder remainingVariables parentType
                (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
                  environment.variableValues)
                (tree.resolveBranches region environment.variableValues) region
                environment).evaluate
                assignment)
            outcome)
      : (regions = [] ∧ outcome = semantics.empty)
        ∨ ∃ region,
            region ∈ regions
            ∧ ContextOutcome semantics schema variableOrder remainingVariables assignment
                environment parentType
                (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
                  environment.variableValues)
                (tree.resolveBranches region environment.variableValues) region
                outcome := by
    rcases joinMap_collecting_cases
        (semantics := semantics)
        (summarize := fun region =>
          (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
            remainingVariables parentType
            (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
              environment.variableValues)
            (tree.resolveBranches region environment.variableValues) region
            environment).evaluate assignment)
        houtcome with
      ⟨hregions, houtcome⟩ | ⟨region, hregion, hregionOutcome⟩
    · exact Or.inl ⟨hregions, houtcome⟩
    · exact Or.inr ⟨region, hregion,
        ContextOutcome.ofCollecting variableOrder remainingVariables assignment
          environment parentType
          (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
            environment.variableValues)
          (tree.resolveBranches region environment.variableValues) region outcome
          hregionOutcome⟩
  termination_by
    (
      caseForestResponseDepth tree,
      contextCollectingControlCount tree remainingVariables,
      contextCollectingTypeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region environment.variableValues tree
    · have hcount := resolveBranches_unresolvedCount_lt region
        environment.variableValues tree _hbranches
      unfold contextCollectingControlCount
      omega

  theorem contextFieldGroupsOfCollecting
      {semantics : CaseSemantics.{u}} {schema : Schema}
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : BooleanAssignment) (environment : BooleanEnvironment)
      (groups : List CollectedFieldGroup) (outcome : semantics.Summary)
      (houtcome
        : (CaseForest.summarizeFieldGroupsDecision semantics.collectingAlgebra schema
            variableOrder remainingVariables groups environment).evaluate
            assignment outcome)
      : ContextFieldGroupsOutcome semantics schema variableOrder remainingVariables
          assignment environment groups outcome := by
    rw [CaseForest.summarizeFieldGroupsDecision,
      BooleanDecision.evaluate_combineMap] at houtcome
    simp only [BooleanDecision.evaluate_map] at houtcome
    cases groups with
    | nil =>
        have houtcome' : outcome = semantics.empty := by
          simpa [combineMap, CaseSemantics.collectingAlgebra,
            OutcomeSet.singleton] using houtcome
        subst outcome
        exact .nil variableOrder remainingVariables assignment environment
    | cons group rest =>
        have hcases := combineMap_collecting_cons_cases
          (semantics := semantics)
          (summarize := fun candidate =>
            OutcomeSet.bind
              ((CaseForest.summarizeChildTypesDecision semantics.collectingAlgebra schema
                variableOrder remainingVariables candidate
                (childParentTypes schema candidate) environment).evaluate assignment)
              (semantics.fieldOutcomes candidate))
          houtcome
        rcases hcases with
          ⟨fieldOutcome, restOutcome, ⟨children, hchildren, hfield⟩, hrest, rfl⟩
        exact .cons variableOrder remainingVariables assignment environment group rest
          children fieldOutcome restOutcome
          (contextChildTypesOfCollecting variableOrder remainingVariables assignment
            environment group (childParentTypes schema group) children hchildren)
          hfield
          (contextFieldGroupsOfCollecting variableOrder remainingVariables assignment
            environment rest restOutcome
            (by
              rw [CaseForest.summarizeFieldGroupsDecision,
                BooleanDecision.evaluate_combineMap]
              simp only [BooleanDecision.evaluate_map]
              exact hrest))
  termination_by
    (
      collectedFieldGroupsResponseDepth groups,
      remainingVariables.length,
      contextCollectingFieldGroupsPhase,
      sizeOf groups
    )
  decreasing_by
    all_goals subst_vars
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
      · decide
    · apply quadruple_lt_of_depth_le_of_tail_lt
      · exact Nat.le_max_right _ _
      · simp_wf
        omega

  theorem contextChildTypesOfCollecting
      {semantics : CaseSemantics.{u}} {schema : Schema}
      (variableOrder remainingVariables : BooleanVariableNames)
      (assignment : BooleanAssignment) (environment : BooleanEnvironment)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (outcome : semantics.Summary)
      (houtcome
        : (CaseForest.summarizeChildTypesDecision semantics.collectingAlgebra schema
            variableOrder remainingVariables group parentTypes environment).evaluate
            assignment outcome)
      : ContextChildTypesOutcome semantics schema variableOrder remainingVariables
          assignment environment group parentTypes outcome := by
    rw [CaseForest.summarizeChildTypesDecision,
      BooleanDecision.evaluate_joinMap] at houtcome
    rcases joinMap_collecting_cases
        (semantics := semantics)
        (summarize := fun childParentType =>
          (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
            remainingVariables childParentType group.childInheritedBooleanCondition
            (.ofConditionTree
              (group.childTreeWithKnownFalsePruning schema childParentType
                environment.fixedVariableValues))
            (group.childTreeWithKnownFalsePruning schema childParentType
              environment.fixedVariableValues).condition.possibleTypes
            environment).evaluate assignment)
        houtcome with
      ⟨hparentTypes, houtcome⟩ | ⟨childParentType, hparentType, hchild⟩
    · subst parentTypes
      subst outcome
      exact .none variableOrder remainingVariables assignment environment group
    · exact .some variableOrder remainingVariables assignment environment group
        parentTypes childParentType outcome hparentType
        (ContextOutcome.ofCollecting variableOrder remainingVariables assignment
          environment childParentType group.childInheritedBooleanCondition
          (.ofConditionTree
            (group.childTreeWithKnownFalsePruning schema childParentType
              environment.fixedVariableValues))
          (group.childTreeWithKnownFalsePruning schema childParentType
            environment.fixedVariableValues).condition.possibleTypes outcome hchild)
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      remainingVariables.length,
      contextCollectingChildTypesPhase,
      sizeOf parentTypes
    )
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition
        environment.fixedVariableValues group.mergedSelectionSet
    simp only [CaseForest.ofConditionTree,
      caseForestResponseDepth, activeTreesResponseDepth, Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

-- The independent lazy case relation exactly characterizes evaluation of the
-- collecting decision under a fixed global assignment.
theorem contextOutcome_iff_evaluate
    {semantics : CaseSemantics.{u}} {schema : Schema}
    (variableOrder remainingVariables : BooleanVariableNames)
    (assignment : BooleanAssignment) (environment : BooleanEnvironment)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (outcome : semantics.Summary)
    : ContextOutcome semantics schema variableOrder remainingVariables assignment
        environment parentType inheritedBooleanCondition tree possibleTypes outcome
      ↔ (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
          remainingVariables parentType inheritedBooleanCondition tree possibleTypes
          environment).evaluate
          assignment outcome :=
  ⟨
    ContextOutcome.toCollecting,
    ContextOutcome.ofCollecting variableOrder remainingVariables assignment environment
      parentType inheritedBooleanCondition tree possibleTypes outcome
  ⟩

-- Collapsing a well-scoped lazy decision collects exactly the independently derived
-- cases for some globally consistent assignment.
theorem contextOutcome_iff_collapse
    {semantics : CaseSemantics.{u}} {schema : Schema}
    (variableOrder remainingVariables : BooleanVariableNames)
    (environment : BooleanEnvironment)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (hremaining : remainingVariables.Nodup) (outcome : semantics.Summary)
    : (∃ assignment,
        ContextOutcome semantics schema variableOrder remainingVariables assignment
          environment parentType inheritedBooleanCondition tree possibleTypes outcome)
      ↔ (CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
          remainingVariables parentType inheritedBooleanCondition tree possibleTypes
          environment).collapse
          semantics.collectingAlgebra outcome := by
  let decision :=
    CaseForest.summarizeDecision semantics.collectingAlgebra schema variableOrder
      remainingVariables parentType inheritedBooleanCondition tree possibleTypes
      environment
  have huses : BooleanDecision.UsesOnly remainingVariables decision :=
    CaseForest.summarizeDecision_usesOnly semantics.collectingAlgebra schema variableOrder
      remainingVariables parentType inheritedBooleanCondition tree possibleTypes
      environment hremaining
  rw [BooleanDecision.collapse_collecting_iff_exists_evaluate huses hremaining outcome]
  exact exists_congr fun assignment =>
    contextOutcome_iff_evaluate variableOrder remainingVariables assignment environment
      parentType inheritedBooleanCondition tree possibleTypes outcome

end CaseForest

theorem BooleanEnvironment.mem_summarizeCompletions_iff
    {semantics : CaseSemantics.{u}}
    (variables : BooleanVariableNames) (initial : BooleanEnvironment)
    (summarize : BooleanEnvironment -> OutcomeSet semantics.Summary)
    (outcome : semantics.Summary)
    : BooleanEnvironment.summarizeCompletions semantics.collectingAlgebra summarize
        variables initial outcome
      ↔ ∃ completed,
          BooleanEnvironment.Completion variables initial completed
          ∧ summarize completed outcome := by
  induction variables generalizing initial with
  | nil =>
      simp [BooleanEnvironment.summarizeCompletions,
        BooleanEnvironment.Completion]
  | cons variableName rest ih =>
      cases hstatus : initial.status? variableName with
      | some status =>
          simpa [BooleanEnvironment.summarizeCompletions,
            BooleanEnvironment.Completion, hstatus] using ih initial
      | none =>
          cases hvalue
                : inputValueBoolean? initial.variableValues (.variable variableName) with
          | some value =>
              simpa [BooleanEnvironment.summarizeCompletions,
                BooleanEnvironment.Completion, hstatus, hvalue] using
                ih (initial.withStatus variableName (.known value))
          | none =>
              cases hlookup
                    : lookupVariableValue? initial.variableValues variableName with
              | some inputValue =>
                  simpa [BooleanEnvironment.summarizeCompletions,
                    BooleanEnvironment.Completion, hstatus, hvalue, hlookup] using
                    ih (initial.withStatus variableName .missing)
              | none =>
                  simp only [BooleanEnvironment.summarizeCompletions,
                    BooleanEnvironment.Completion, hstatus, hvalue, hlookup,
                    CaseSemantics.collectingAlgebra, OutcomeSet.union]
                  constructor
                  · intro hsummary
                    rcases hsummary with hmissing | hunresolved
                    · rcases (ih (initial.withStatus variableName .missing)).mp
                          hmissing with ⟨completed, hcompleted, houtcome⟩
                      exact ⟨completed, Or.inl hcompleted, houtcome⟩
                    · rcases (ih (initial.withStatus variableName .unresolved)).mp
                          hunresolved with ⟨completed, hcompleted, houtcome⟩
                      exact ⟨completed, Or.inr hcompleted, houtcome⟩
                  · rintro ⟨completed, hcompleted, houtcome⟩
                    rcases hcompleted with hmissing | hunresolved
                    · exact Or.inl
                        ((ih (initial.withStatus variableName .missing)).mpr
                          ⟨completed, hmissing, houtcome⟩)
                    · exact Or.inr
                        ((ih (initial.withStatus variableName .unresolved)).mpr
                          ⟨completed, hunresolved, houtcome⟩)

-- The independent feasible-case relation exactly characterizes the collecting
-- interpretation of the lazy condition-tree entry point.
theorem conditionTreeContextOutcomes_iff_collecting
    (semantics : CaseSemantics.{u}) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (initial : BooleanEnvironment) (outcome : semantics.Summary)
    : conditionTreeContextOutcomes semantics schema parentType
        inheritedBooleanCondition tree initial outcome
      ↔ summarizeConditionTree semantics.collectingAlgebra schema parentType
          inheritedBooleanCondition tree initial outcome := by
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  let summarizeCompleted : BooleanEnvironment -> OutcomeSet semantics.Summary :=
    fun completed =>
      (summarizeConditionTreeDecision semantics.collectingAlgebra schema parentType
        inheritedBooleanCondition tree variables completed).collapse
        semantics.collectingAlgebra
  unfold conditionTreeContextOutcomes summarizeConditionTree
  change (∃ completed,
            BooleanEnvironment.Completion variables initial completed
            ∧ ∃ assignment,
                CaseForest.ContextOutcome semantics schema variables variables assignment
                  completed parentType inheritedBooleanCondition (.ofConditionTree tree)
                  tree.condition.possibleTypes outcome)
          ↔ BooleanEnvironment.summarizeCompletions semantics.collectingAlgebra
              summarizeCompleted variables initial outcome
  calc
    _ ↔ ∃ completed,
          BooleanEnvironment.Completion variables initial completed
          ∧ summarizeCompleted completed outcome := by
      apply exists_congr
      intro completed
      apply and_congr_right
      intro _hcompleted
      simpa [summarizeCompleted, summarizeConditionTreeDecision] using
        CaseForest.contextOutcome_iff_collapse variables variables completed parentType
          inheritedBooleanCondition (.ofConditionTree tree)
          tree.condition.possibleTypes (BooleanDecision.eraseDups_nodup _) outcome
    _ ↔ _ :=
      (BooleanEnvironment.mem_summarizeCompletions_iff
        (semantics := semantics) variables initial summarizeCompleted outcome).symm

private theorem bestBound_of_attainable_iff
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

-- The lazy exact-case traversal is the least abstract bound of the independently
-- defined feasible cases under the supplied local best-transfer laws.
theorem summarizeConditionTree_best
    {semantics : CaseSemantics.{u}} {abstract : Algebra.{v}}
    (laws : BestTransferLaws semantics abstract) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (initial : BooleanEnvironment)
    : BestBound laws.le laws.related
        (conditionTreeContextOutcomes semantics schema parentType
          inheritedBooleanCondition tree initial)
        (summarizeConditionTree abstract schema parentType
          inheritedBooleanCondition tree initial) := by
  apply bestBound_of_attainable_iff
    (fun outcome => conditionTreeContextOutcomes_iff_collecting semantics schema
      parentType inheritedBooleanCondition tree initial outcome)
  exact summarizeConditionTree_related laws.relation parentType
    inheritedBooleanCondition tree initial

theorem summarizeSelectionSet_best
    {semantics : CaseSemantics.{u}} {abstract : Algebra.{v}}
    (laws : BestTransferLaws semantics abstract) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (initial : BooleanEnvironment)
    : BestBound laws.le laws.related
        (selectionSetContextOutcomes semantics schema parentType
          inheritedBooleanCondition selectionSet initial)
        (summarizeSelectionSet abstract schema parentType
          inheritedBooleanCondition selectionSet initial) := by
  unfold selectionSetContextOutcomes summarizeSelectionSet
  exact summarizeConditionTree_best laws schema parentType
    inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition initial.fixedVariableValues selectionSet)
    initial

-- Generic witness for the public lazy-operation optimality statement.
theorem operationContextOptimal
    {semantics : CaseSemantics.{u}} {abstract : Algebra.{v}}
    (laws : BestTransferLaws semantics abstract) (schema : Schema)
    (operation : Operation) (initial : BooleanEnvironment)
    : OperationContextOptimal semantics abstract laws.le laws.related schema operation
        initial := by
  unfold OperationContextOptimal operationContextOutcomes
  exact summarizeSelectionSet_best laws schema (operation.rootType schema) []
    operation.selectionSet initial

-- Operation specialization with every Boolean variable initially unknown.
theorem summarizeOperation_best
    {semantics : CaseSemantics.{u}} {abstract : Algebra.{v}}
    {schema : Schema}
    (laws : BestTransferLaws semantics abstract) (operation : Operation)
    : BestBound laws.le laws.related
        (operationOutcomes semantics schema operation)
        (summarizeOperation abstract schema operation) := by
  simpa [operationOutcomes, operationContextOutcomes, summarizeOperation] using
    summarizeSelectionSet_best laws schema (operation.rootType schema) []
      operation.selectionSet
      BooleanEnvironment.unknown

-- Generic witness for the public default-operation optimality statement.
theorem operationOptimal
    {semantics : CaseSemantics.{u}} {abstract : Algebra.{v}}
    {schema : Schema}
    (laws : BestTransferLaws semantics abstract) (operation : Operation)
    : OperationOptimal semantics abstract laws.le laws.related schema operation :=
  summarizeOperation_best laws operation

-- Variable-aware operation specialization. Coerced values are fixed once at the root
-- and shared by every recursive child selection-set case.
theorem summarizeOperationWithVariables_best
    {semantics : CaseSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (variableValues : VariableValues) (operation : Operation)
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)))
    : BestBound laws.le laws.related
        (operationOutcomesWithVariables semantics schema variableValues operation)
        (summarizeOperationWithVariables abstractFor schema variableValues
          operation) := by
  let coercedVariableValues := Execution.coerceVariableValues operation variableValues
  let variables := operationBooleanVariables operation
  let environment :=
    BooleanEnvironment.ofCompleteValues variables coercedVariableValues
  have hbest := summarizeSelectionSet_best laws schema (operation.rootType schema) []
    operation.selectionSet environment
  rw [summarizeOperationSelectionSet_eq_resolved_ofCompleteValues] at hbest
  simpa [operationOutcomesWithVariables, operationContextOutcomes,
    summarizeOperationWithVariables, summarizeSelectionSetResolved,
    summarizeConditionTreeResolved, BooleanEnvironment.ofCompleteValues,
    coercedVariableValues, variables, environment]
    using hbest

-- Generic witness for the public variable-aware operation optimality statement.
theorem operationWithVariablesOptimal
    {semantics : CaseSemantics.{u}}
    (abstractFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (variableValues : VariableValues) (operation : Operation)
    (laws
      : BestTransferLaws semantics
          (abstractFor (Execution.coerceVariableValues operation variableValues)))
    : OperationWithVariablesOptimal semantics abstractFor schema variableValues operation
        laws.le laws.related :=
  summarizeOperationWithVariables_best abstractFor variableValues operation laws

end ExactCases
end TreeSummary
end GraphQL
