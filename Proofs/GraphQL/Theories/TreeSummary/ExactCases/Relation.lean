import GraphQL.Theories.TreeSummary.ExactCases
import Proofs.GraphQL.Theories.TreeSummary.Algebra

/-! Generic algebra-relation transport through exact-case traversal. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open TreeSummary.Measure
open Measure

universe u v

namespace BooleanDecision

@[simp]
theorem evaluate_map (assignment : Name -> Bool) (transform : α -> β)
    (decision : BooleanDecision α)
    : (decision.map transform).evaluate assignment
      = transform (decision.evaluate assignment) := by
  induction decision with
  | leaf => rfl
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [map, evaluate]
      split <;> simp_all

theorem evaluate_restrict_of_eq (assignment : Name -> Bool)
    (selectedVariable : Name) (selectedValue : Bool)
    (decision : BooleanDecision α)
    (hvalue : assignment selectedVariable = selectedValue)
    : (decision.restrict selectedVariable selectedValue).evaluate assignment
      = decision.evaluate assignment := by
  induction decision with
  | leaf => rfl
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [restrict]
      split <;> rename_i hequal
      · subst variableName
        cases selectedValue <;> simp_all [evaluate]
      · simp only [evaluate]
        split <;> simp_all

theorem nodeCount_restrict_le
    (selectedVariable : Name) (selectedValue : Bool)
    (decision : BooleanDecision α)
    : (decision.restrict selectedVariable selectedValue).nodeCount
      ≤ decision.nodeCount := by
  induction decision with
  | leaf => simp [restrict, nodeCount]
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [restrict]
      split
      · cases selectedValue <;> simp_all [nodeCount] <;> omega
      · simp only [nodeCount]
        omega

@[simp]
theorem evaluate_zipWith (variableOrder : BooleanVariableNames)
    (assignment : Name -> Bool) (operation : α -> β -> γ)
    (left : BooleanDecision α) (right : BooleanDecision β)
    : (zipWith variableOrder operation left right).evaluate assignment
      = operation (left.evaluate assignment) (right.evaluate assignment) := by
  cases left with
  | leaf left => simp [zipWith, evaluate]
  | split leftVariable leftFalse leftTrue =>
      cases right with
      | leaf right => simp [zipWith, evaluate]
      | split rightVariable rightFalse rightTrue =>
          simp only [zipWith]
          split
          · subst rightVariable
            simp only [evaluate]
            split
            · exact evaluate_zipWith variableOrder assignment operation
                leftTrue rightTrue
            · exact evaluate_zipWith variableOrder assignment operation
                leftFalse rightFalse
          · split
            · simp only [evaluate]
              split
              · rename_i hvalue
                rw [evaluate_zipWith]
                rw [evaluate_restrict_of_eq assignment leftVariable true _ (by
                  simpa using hvalue)]
                simp [evaluate]
              · rename_i hvalue
                rw [evaluate_zipWith]
                rw [evaluate_restrict_of_eq assignment leftVariable false _ (by
                  simpa using hvalue)]
                simp [evaluate]
            · simp only [evaluate]
              split
              · rename_i hvalue
                rw [evaluate_zipWith]
                rw [evaluate_restrict_of_eq assignment rightVariable true _ (by
                  simpa using hvalue)]
                simp [evaluate]
              · rename_i hvalue
                rw [evaluate_zipWith]
                rw [evaluate_restrict_of_eq assignment rightVariable false _ (by
                  simpa using hvalue)]
                simp [evaluate]
termination_by left.nodeCount + right.nodeCount
decreasing_by
  all_goals
    have hleftFalse := nodeCount_restrict_le rightVariable false
      (BooleanDecision.split leftVariable leftFalse leftTrue)
    have hleftTrue := nodeCount_restrict_le rightVariable true
      (BooleanDecision.split leftVariable leftFalse leftTrue)
    have hrightFalse := nodeCount_restrict_le leftVariable false
      (BooleanDecision.split rightVariable rightFalse rightTrue)
    have hrightTrue := nodeCount_restrict_le leftVariable true
      (BooleanDecision.split rightVariable rightFalse rightTrue)
    simp only [nodeCount] at hleftFalse hleftTrue hrightFalse hrightTrue ⊢
    omega

@[simp]
theorem evaluate_combineMap (algebra : Algebra)
    (variableOrder : BooleanVariableNames) (assignment : Name -> Bool)
    (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    : (combineMap algebra variableOrder items summarize).evaluate assignment
      = TreeSummary.combineMap algebra items
          fun item hitem => (summarize item hitem).evaluate assignment := by
  induction items with
  | nil => simp [combineMap, TreeSummary.combineMap, evaluate]
  | cons item rest ih =>
      simp only [combineMap, TreeSummary.combineMap, evaluate_zipWith]
      exact congrArg (algebra.combine ((summarize item (by simp)).evaluate assignment))
        (ih
          (fun candidate hcandidate => summarize candidate (by simp [hcandidate])))

@[simp]
theorem evaluate_joinMap (algebra : Algebra)
    (variableOrder : BooleanVariableNames) (assignment : Name -> Bool)
    (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    : (joinMap algebra variableOrder items summarize).evaluate assignment
      = TreeSummary.joinMap algebra items
          fun item hitem => (summarize item hitem).evaluate assignment := by
  cases items with
  | nil => simp [joinMap, TreeSummary.joinMap, evaluate]
  | cons item rest =>
      cases rest with
      | nil => simp [joinMap, TreeSummary.joinMap]
      | cons next tail =>
          simp only [joinMap, TreeSummary.joinMap, evaluate_zipWith]
          exact congrArg (algebra.join ((summarize item (by simp)).evaluate assignment))
            (evaluate_joinMap algebra variableOrder assignment (next :: tail)
              (fun candidate hcandidate => summarize candidate (by simp [hcandidate])))
termination_by items.length

-- Pointwise lifting of a summary relation to identically shaped Boolean decisions.
inductive Related (relation : α → β → Prop) : BooleanDecision α → BooleanDecision β → Prop
  | leaf {left right} (hrelated : relation left right)
    : Related relation (.leaf left) (.leaf right)
  | split (variableName) {leftFalse leftTrue rightFalse rightTrue}
    (hfalse : Related relation leftFalse rightFalse)
    (htrue : Related relation leftTrue rightTrue)
    : Related relation (.split variableName leftFalse leftTrue)
        (.split variableName rightFalse rightTrue)

theorem restrict_related
    {relation : α → β → Prop}
    {left : BooleanDecision α} {right : BooleanDecision β}
    (hdecision : Related relation left right)
    (selectedVariable : Name) (selectedValue : Bool)
    : Related relation
        (left.restrict selectedVariable selectedValue)
        (right.restrict selectedVariable selectedValue) := by
  induction hdecision with
  | leaf hrelated => exact .leaf hrelated
  | split variableName hfalse htrue ihFalse ihTrue =>
      simp only [restrict]
      split
      · cases selectedValue
        · exact ihFalse
        · exact ihTrue
      · exact .split variableName ihFalse ihTrue

theorem map_related
    {leftRelation : α → β → Prop} {rightRelation : γ → δ → Prop}
    {left : BooleanDecision α} {right : BooleanDecision β}
    (hdecision : Related leftRelation left right)
    (leftMap : α → γ) (rightMap : β → δ)
    (hmap
      : ∀ leftValue rightValue,
          leftRelation leftValue rightValue
          → rightRelation (leftMap leftValue) (rightMap rightValue))
    : Related rightRelation (left.map leftMap) (right.map rightMap) := by
  induction hdecision with
  | leaf hrelated => exact .leaf (hmap _ _ hrelated)
  | split variableName _ _ hfalse htrue =>
      exact .split variableName hfalse htrue

theorem zipWith_related
    {leftRelation : α → β → Prop} {rightRelation : γ → δ → Prop}
    {resultRelation : ε → ζ → Prop}
    (variableOrder : BooleanVariableNames)
    (leftOperation : α → γ → ε) (rightOperation : β → δ → ζ)
    {leftFirst : BooleanDecision α} {rightFirst : BooleanDecision β}
    {leftSecond : BooleanDecision γ} {rightSecond : BooleanDecision δ}
    (hfirst : Related leftRelation leftFirst rightFirst)
    (hsecond : Related rightRelation leftSecond rightSecond)
    (hoperation
      : ∀ leftFirstValue rightFirstValue leftSecondValue rightSecondValue,
          leftRelation leftFirstValue rightFirstValue
          → rightRelation leftSecondValue rightSecondValue
          → resultRelation
              (leftOperation leftFirstValue leftSecondValue)
              (rightOperation rightFirstValue rightSecondValue))
    : Related resultRelation
        (zipWith variableOrder leftOperation leftFirst leftSecond)
        (zipWith variableOrder rightOperation rightFirst rightSecond) := by
  cases hfirst with
  | leaf hfirst =>
      simp only [zipWith]
      exact map_related hsecond _ _ fun _ _ hsecond =>
        hoperation _ _ _ _ hfirst hsecond
  | @split firstVariable firstLeftFalse firstLeftTrue
      firstRightFalse firstRightTrue hfalse htrue =>
      cases hsecond with
      | leaf hsecond =>
          simp only [zipWith]
          exact map_related (.split firstVariable hfalse htrue) _ _ fun _ _ hfirst =>
            hoperation _ _ _ _ hfirst hsecond
      | @split secondVariable secondLeftFalse secondLeftTrue
          secondRightFalse secondRightTrue hsecondFalse hsecondTrue =>
          simp only [zipWith]
          split
          · exact .split firstVariable
              (zipWith_related variableOrder leftOperation rightOperation
                hfalse hsecondFalse hoperation)
              (zipWith_related variableOrder leftOperation rightOperation
                htrue hsecondTrue hoperation)
          · split
            · exact .split firstVariable
                (zipWith_related variableOrder leftOperation rightOperation
                  hfalse
                  (restrict_related (.split secondVariable hsecondFalse hsecondTrue)
                    firstVariable false)
                  hoperation)
                (zipWith_related variableOrder leftOperation rightOperation
                  htrue
                  (restrict_related (.split secondVariable hsecondFalse hsecondTrue)
                    firstVariable true)
                  hoperation)
            · exact .split secondVariable
                (zipWith_related variableOrder leftOperation rightOperation
                  (restrict_related (.split firstVariable hfalse htrue)
                    secondVariable false)
                  hsecondFalse hoperation)
                (zipWith_related variableOrder leftOperation rightOperation
                  (restrict_related (.split firstVariable hfalse htrue)
                    secondVariable true)
                  hsecondTrue hoperation)
termination_by leftFirst.nodeCount + leftSecond.nodeCount
decreasing_by
  all_goals
    have hfirstFalse := nodeCount_restrict_le secondVariable false
      (BooleanDecision.split firstVariable firstLeftFalse firstLeftTrue)
    have hfirstTrue := nodeCount_restrict_le secondVariable true
      (BooleanDecision.split firstVariable firstLeftFalse firstLeftTrue)
    have hsecondFalse := nodeCount_restrict_le firstVariable false
      (BooleanDecision.split secondVariable secondLeftFalse secondLeftTrue)
    have hsecondTrue := nodeCount_restrict_le firstVariable true
      (BooleanDecision.split secondVariable secondLeftFalse secondLeftTrue)
    simp only [nodeCount] at hfirstFalse hfirstTrue hsecondFalse hsecondTrue ⊢
    omega

theorem collapse_related
    {left : Algebra.{u}} {right : Algebra.{v}}
    (relation : Algebra.Relation left right)
    {leftDecision : BooleanDecision left.Summary}
    {rightDecision : BooleanDecision right.Summary}
    (hdecision : Related relation.related leftDecision rightDecision)
    : relation.related (leftDecision.collapse left) (rightDecision.collapse right) := by
  induction hdecision with
  | leaf hrelated => exact hrelated
  | split _ _ _ hfalse htrue =>
      exact relation.join_related _ _ _ _ hfalse htrue

theorem combineMap_related
    {left : Algebra.{u}} {right : Algebra.{v}}
    (relation : Algebra.Relation left right) (variableOrder : BooleanVariableNames)
    (items : List α)
    (leftSummary : ∀ item, item ∈ items → BooleanDecision left.Summary)
    (rightSummary : ∀ item, item ∈ items → BooleanDecision right.Summary)
    (hitem
      : ∀ item hitem,
          Related relation.related (leftSummary item hitem) (rightSummary item hitem))
    : Related relation.related
        (combineMap left variableOrder items leftSummary)
        (combineMap right variableOrder items rightSummary) := by
  induction items with
  | nil => simpa [combineMap] using Related.leaf relation.empty_related
  | cons item rest ih =>
      simp only [combineMap]
      apply zipWith_related variableOrder left.combine right.combine
      · exact hitem item (by simp)
      · exact ih
          (fun candidate hcandidate => leftSummary candidate (by simp [hcandidate]))
          (fun candidate hcandidate => rightSummary candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hitem candidate (by simp [hcandidate]))
      · exact fun _ _ _ _ => relation.combine_related _ _ _ _

theorem joinMap_related
    {left : Algebra.{u}} {right : Algebra.{v}}
    (relation : Algebra.Relation left right) (variableOrder : BooleanVariableNames)
    (items : List α)
    (leftSummary : ∀ item, item ∈ items → BooleanDecision left.Summary)
    (rightSummary : ∀ item, item ∈ items → BooleanDecision right.Summary)
    (hitem
      : ∀ item hitem,
          Related relation.related (leftSummary item hitem) (rightSummary item hitem))
    : Related relation.related
        (joinMap left variableOrder items leftSummary)
        (joinMap right variableOrder items rightSummary) := by
  cases items with
  | nil => simpa [joinMap] using Related.leaf relation.empty_related
  | cons item rest =>
      cases rest with
      | nil => simpa [joinMap] using hitem item (by simp)
      | cons next tail =>
          simp only [joinMap]
          apply zipWith_related variableOrder left.join right.join
          · exact hitem item (by simp)
          · exact joinMap_related relation variableOrder (next :: tail)
              (fun candidate hcandidate => leftSummary candidate (by simp [hcandidate]))
              (fun candidate hcandidate => rightSummary candidate (by simp [hcandidate]))
              (fun candidate hcandidate => hitem candidate (by simp [hcandidate]))
          · exact fun _ _ _ _ => relation.join_related _ _ _ _
termination_by items.length

end BooleanDecision

namespace CaseForest

private def relationSummarizePhase : Nat := 3
private def relationTypeRegionsPhase : Nat := 2
private def relationFieldGroupsPhase : Nat := 1
private def relationChildTypesPhase : Nat := 0

mutual
  theorem summarize_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (variableValues fixedVariableValues : Execution.VariableValues)
      : relation.related
          (summarize left schema parentType inheritedBooleanCondition tree possibleTypes
            variableValues fixedVariableValues)
          (summarize right schema parentType inheritedBooleanCondition tree possibleTypes
            variableValues fixedVariableValues) := by
    rw [summarize, summarize]
    split <;> rename_i hbranches
    · exact summarizeTypeRegions_related relation parentType inheritedBooleanCondition
        tree (tree.typeRegions possibleTypes) variableValues hbranches
        fixedVariableValues
    · exact summarizeFieldGroups_related relation
        (tree.fieldGroups inheritedBooleanCondition possibleTypes)
        variableValues fixedVariableValues
  termination_by
    (
      caseForestResponseDepth tree,
      caseForestUnresolvedCount tree,
      relationSummarizePhase,
      0
    )
  decreasing_by
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact fieldGroupsResponseDepth_le inheritedBooleanCondition
          possibleTypes tree
      · exact Nat.zero_le _
      · decide
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · decide

  theorem summarizeTypeRegions_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (regions : List PossibleTypeRegion)
      (variableValues : Execution.VariableValues)
      (hbranches : tree.hasUnresolvedBranches = true)
      (fixedVariableValues : Execution.VariableValues)
      : relation.related
          (summarizeTypeRegions left schema parentType inheritedBooleanCondition tree
            regions variableValues hbranches fixedVariableValues)
          (summarizeTypeRegions right schema parentType inheritedBooleanCondition tree
            regions variableValues hbranches fixedVariableValues) := by
    unfold summarizeTypeRegions
    apply Algebra.Relation.joinMap_related relation
    intro region _hregion
    exact summarize_related relation parentType
      (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        variableValues)
      (tree.resolveBranches region variableValues) region variableValues
      fixedVariableValues
  termination_by
    (
      caseForestResponseDepth tree,
      caseForestUnresolvedCount tree,
      relationTypeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le _ _ _
    · apply resolveBranches_unresolvedCount_lt
      assumption

  theorem summarizeFieldGroups_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (groups : List CollectedFieldGroup)
      (variableValues fixedVariableValues : Execution.VariableValues)
      : relation.related
          (summarizeFieldGroups left schema groups variableValues fixedVariableValues)
          (summarizeFieldGroups right schema groups variableValues
            fixedVariableValues) := by
    unfold summarizeFieldGroups
    apply Algebra.Relation.combineMap_related relation
    intro group hgroup
    exact relation.field_related group _ _
      (summarizeChildTypes_related relation group (childParentTypes schema group)
        variableValues fixedVariableValues)
  termination_by
    (collectedFieldGroupsResponseDepth groups, 0, relationFieldGroupsPhase, sizeOf groups)
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups hgroup
    · exact Nat.le_refl _
    · decide

  theorem summarizeChildTypes_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (variableValues fixedVariableValues : Execution.VariableValues)
      : relation.related
          (summarizeChildTypes left schema group parentTypes variableValues
            fixedVariableValues)
          (summarizeChildTypes right schema group parentTypes variableValues
            fixedVariableValues) := by
    unfold summarizeChildTypes
    apply Algebra.Relation.joinMap_related relation
    intro childParentType hchildParentType
    exact summarize_related relation childParentType
      group.childInheritedBooleanCondition
      (.ofConditionTree
        (group.childTreeWithKnownFalsePruning schema childParentType fixedVariableValues))
      (group.childTreeWithKnownFalsePruning schema childParentType
        fixedVariableValues).condition.possibleTypes
      variableValues fixedVariableValues
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      0,
      relationChildTypesPhase,
      sizeOf parentTypes
    )
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition fixedVariableValues
        group.mergedSelectionSet
    simp only [CaseForest.ofConditionTree, caseForestResponseDepth,
      activeTreesResponseDepth, Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

private def decisionRelationSummarizePhase : Nat := 3
private def decisionRelationTypeRegionsPhase : Nat := 2
private def decisionRelationFieldGroupsPhase : Nat := 1
private def decisionRelationChildTypesPhase : Nat := 0

private def decisionRelationControlCount (tree : CaseForest)
    (remainingVariables : BooleanVariableNames)
    : Nat :=
  caseForestUnresolvedCount tree + remainingVariables.length

mutual
  theorem summarizeDecision_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (variableOrder remainingVariables : BooleanVariableNames)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (environment : BooleanEnvironment)
      : BooleanDecision.Related relation.related
          (summarizeDecision left schema variableOrder remainingVariables parentType
            inheritedBooleanCondition tree possibleTypes environment)
          (summarizeDecision right schema variableOrder remainingVariables parentType
            inheritedBooleanCondition tree possibleTypes environment) := by
    rw [summarizeDecision, summarizeDecision]
    split <;> rename_i hbranches
    · cases hnext
            : environment.nextUnresolved remainingVariables tree.booleanVariables with
      | none =>
          exact summarizeTypeRegionsDecision_related relation variableOrder
            remainingVariables parentType inheritedBooleanCondition tree
            (tree.typeRegions possibleTypes) environment hbranches
      | some variableName =>
          exact .split variableName
            (summarizeDecision_related relation variableOrder
              (remainingVariables.erase variableName) parentType
              inheritedBooleanCondition tree possibleTypes
              (environment.assign variableName false))
            (summarizeDecision_related relation variableOrder
              (remainingVariables.erase variableName) parentType
              inheritedBooleanCondition tree possibleTypes
              (environment.assign variableName true))
    · exact summarizeFieldGroupsDecision_related relation variableOrder
        remainingVariables
        (tree.fieldGroups inheritedBooleanCondition possibleTypes) environment
  termination_by
    (
      caseForestResponseDepth tree,
      decisionRelationControlCount tree remainingVariables,
      decisionRelationSummarizePhase,
      0
    )
  decreasing_by
    · apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
      · exact fieldGroupsResponseDepth_le inheritedBooleanCondition
          possibleTypes tree
      · unfold decisionRelationControlCount
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
        unfold decisionRelationControlCount
        rw [hlength]
        omega
    · apply quadruple_lt_of_depth_le_of_control_lt
      · exact Nat.le_refl _
      · have hmem := List.mem_of_find?_eq_some hnext
        have hlength := List.length_erase_of_mem hmem
        have hpositive : 0 < remainingVariables.length :=
          List.length_pos_of_mem hmem
        unfold decisionRelationControlCount
        rw [hlength]
        omega

  theorem summarizeTypeRegionsDecision_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (variableOrder remainingVariables : BooleanVariableNames)
      (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
      (tree : CaseForest) (regions : List PossibleTypeRegion)
      (environment : BooleanEnvironment)
      (hbranches : tree.hasUnresolvedBranches = true)
      : BooleanDecision.Related relation.related
          (summarizeTypeRegionsDecision left schema variableOrder remainingVariables
            parentType inheritedBooleanCondition tree regions environment
            hbranches)
          (summarizeTypeRegionsDecision right schema variableOrder remainingVariables
            parentType inheritedBooleanCondition tree regions environment
            hbranches) := by
    unfold summarizeTypeRegionsDecision
    apply BooleanDecision.joinMap_related relation
    intro region _hregion
    exact summarizeDecision_related relation variableOrder remainingVariables parentType
      (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        environment.variableValues)
      (tree.resolveBranches region environment.variableValues) region environment
  termination_by
    (
      caseForestResponseDepth tree,
      decisionRelationControlCount tree remainingVariables,
      decisionRelationTypeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region environment.variableValues tree
    · have hcount := resolveBranches_unresolvedCount_lt region
        environment.variableValues tree hbranches
      unfold decisionRelationControlCount
      omega

  theorem summarizeFieldGroupsDecision_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (variableOrder remainingVariables : BooleanVariableNames)
      (groups : List CollectedFieldGroup) (environment : BooleanEnvironment)
      : BooleanDecision.Related relation.related
          (summarizeFieldGroupsDecision left schema variableOrder remainingVariables
            groups environment)
          (summarizeFieldGroupsDecision right schema variableOrder remainingVariables
            groups environment) := by
    unfold summarizeFieldGroupsDecision
    apply BooleanDecision.combineMap_related relation
    intro group hgroup
    apply BooleanDecision.map_related
      (summarizeChildTypesDecision_related relation variableOrder remainingVariables group
        (childParentTypes schema group) environment)
    exact fun _ _ hchildren => relation.field_related group _ _ hchildren
  termination_by
    (
      collectedFieldGroupsResponseDepth groups,
      remainingVariables.length,
      decisionRelationFieldGroupsPhase,
      sizeOf groups
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups hgroup
    · exact Nat.le_refl _
    · decide

  theorem summarizeChildTypesDecision_related
      {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
      (relation : Algebra.Relation left right)
      (variableOrder remainingVariables : BooleanVariableNames)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (environment : BooleanEnvironment)
      : BooleanDecision.Related relation.related
          (summarizeChildTypesDecision left schema variableOrder remainingVariables group
            parentTypes environment)
          (summarizeChildTypesDecision right schema variableOrder remainingVariables group
            parentTypes environment) := by
    unfold summarizeChildTypesDecision
    apply BooleanDecision.joinMap_related relation
    intro childParentType _hparentType
    exact summarizeDecision_related relation variableOrder remainingVariables
      childParentType group.childInheritedBooleanCondition
      (.ofConditionTree
        (group.childTreeWithKnownFalsePruning schema childParentType
          environment.fixedVariableValues))
      (group.childTreeWithKnownFalsePruning schema childParentType
        environment.fixedVariableValues).condition.possibleTypes environment
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      remainingVariables.length,
      decisionRelationChildTypesPhase,
      sizeOf parentTypes
    )
  decreasing_by
    apply Prod.Lex.left
    have hchild :=
      conditionTreeResponseDepth_ofSelectionSetInScopeWithKnownFalsePruning schema
        childParentType group.childInheritedBooleanCondition
        environment.fixedVariableValues group.mergedSelectionSet
    simp only [CaseForest.ofConditionTree, caseForestResponseDepth,
      activeTreesResponseDepth, Nat.max_zero]
    exact Nat.lt_of_le_of_lt hchild (Nat.lt_succ_self _)
end

end CaseForest

theorem BooleanEnvironment.summarizeCompletions_related
    {left : Algebra.{u}} {right : Algebra.{v}}
    (relation : Algebra.Relation left right)
    (variables : BooleanVariableNames) (initial : BooleanEnvironment)
    (leftSummary : BooleanEnvironment → left.Summary)
    (rightSummary : BooleanEnvironment → right.Summary)
    (hsummary
      : ∀ environment,
          relation.related (leftSummary environment) (rightSummary environment))
    : relation.related
        (summarizeCompletions left leftSummary variables initial)
        (summarizeCompletions right rightSummary variables initial) := by
  induction variables generalizing initial with
  | nil => simpa [summarizeCompletions] using hsummary initial
  | cons variableName rest ih =>
      cases hstatus : initial.status? variableName with
      | some status =>
          simp only [summarizeCompletions, hstatus]
          exact ih initial
      | none =>
          cases hvalue
                : Execution.inputValueBoolean? initial.variableValues
                    (.variable variableName) with
          | some value =>
              simp only [summarizeCompletions, hstatus, hvalue]
              exact ih (initial.withStatus variableName (.known value))
          | none =>
              cases hlookup
                    : Execution.lookupVariableValue? initial.variableValues
                        variableName with
              | some inputValue =>
                  simp only [summarizeCompletions, hstatus, hvalue, hlookup]
                  exact ih (initial.withStatus variableName .missing)
              | none =>
                  simp only [summarizeCompletions, hstatus, hvalue, hlookup]
                  exact relation.join_related _ _ _ _
                    (ih (initial.withStatus variableName .missing))
                    (ih (initial.withStatus variableName .unresolved))

theorem summarizeConditionTree_related
    {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
    (relation : Algebra.Relation left right)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (environment : BooleanEnvironment)
    : relation.related
        (summarizeConditionTree left schema parentType
          inheritedBooleanCondition tree environment)
        (summarizeConditionTree right schema parentType
          inheritedBooleanCondition tree environment) := by
  unfold summarizeConditionTree summarizeConditionTreeDecision
  apply BooleanEnvironment.summarizeCompletions_related relation
  intro completed
  apply BooleanDecision.collapse_related relation
  exact CaseForest.summarizeDecision_related relation
    (conditionTreeBooleanVariables tree).eraseDups
    (conditionTreeBooleanVariables tree).eraseDups parentType
    inheritedBooleanCondition (.ofConditionTree tree) tree.condition.possibleTypes
    completed

theorem summarizeSelectionSet_related
    {left : Algebra.{u}} {right : Algebra.{v}} {schema : Schema}
    (relation : Algebra.Relation left right)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (environment : BooleanEnvironment)
    : relation.related
        (summarizeSelectionSet left schema parentType
          inheritedBooleanCondition selectionSet environment)
        (summarizeSelectionSet right schema parentType
          inheritedBooleanCondition selectionSet environment) := by
  unfold summarizeSelectionSet
  exact summarizeConditionTree_related relation parentType
    inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition environment.fixedVariableValues selectionSet)
    environment

end ExactCases
end TreeSummary
end GraphQL
