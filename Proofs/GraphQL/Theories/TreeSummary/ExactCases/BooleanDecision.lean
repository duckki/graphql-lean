import GraphQL.Theories.TreeSummary.ExactCases

/-! Structural invariants of lazy Boolean decision trees. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases
namespace BooleanDecision

universe u

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open TreeSummary.Measure
open ExactCases.Measure

-- Every split variable belongs to the available support, and is removed from the
-- support inherited by both children. In particular, a variable occurs at most once
-- along any root-to-leaf path when the initial support has no duplicates.
inductive UsesOnly : BooleanVariableNames -> BooleanDecision α -> Prop
  | leaf (variables : BooleanVariableNames) (summary : α)
    : UsesOnly variables (.leaf summary)
  | split {variables : BooleanVariableNames} {variableName : Name}
    {onFalse onTrue : BooleanDecision α}
    (hvariable : variableName ∈ variables)
    (hfalse : UsesOnly (variables.erase variableName) onFalse)
    (htrue : UsesOnly (variables.erase variableName) onTrue)
    : UsesOnly variables (.split variableName onFalse onTrue)

theorem UsesOnly.map (transform : α -> β)
    {variables : BooleanVariableNames} {decision : BooleanDecision α}
    (hdecision : UsesOnly variables decision)
    : UsesOnly variables (decision.map transform) := by
  induction hdecision with
  | leaf => exact .leaf _ _
  | split hvariable _ _ ihFalse ihTrue =>
      exact .split hvariable ihFalse ihTrue

theorem UsesOnly.restrict
    {variables : BooleanVariableNames} {decision : BooleanDecision α}
    (hdecision : UsesOnly variables decision)
    (hvariables : variables.Nodup)
    (selectedVariable : Name) (selectedValue : Bool)
    : UsesOnly (variables.erase selectedVariable)
        (decision.restrict selectedVariable selectedValue) := by
  induction hdecision with
  | leaf => exact .leaf _ _
  | @split variables variableName onFalse onTrue hvariable hfalse htrue
      ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split <;> rename_i hequal
      · subst variableName
        cases selectedValue
        · have hrestricted := ihFalse (hvariables.erase selectedVariable)
          rw [List.erase_of_not_mem hvariables.not_mem_erase] at hrestricted
          exact hrestricted
        · have hrestricted := ihTrue (hvariables.erase selectedVariable)
          rw [List.erase_of_not_mem hvariables.not_mem_erase] at hrestricted
          exact hrestricted
      · apply UsesOnly.split
        · simp [hequal, hvariable]
        · rw [List.erase_comm]
          exact ihFalse (hvariables.erase variableName)
        · rw [List.erase_comm]
          exact ihTrue (hvariables.erase variableName)

private theorem nodeCount_restrict_le
    (selectedVariable : Name) (selectedValue : Bool)
    (decision : BooleanDecision α)
    : (decision.restrict selectedVariable selectedValue).nodeCount
      ≤ decision.nodeCount := by
  induction decision with
  | leaf => simp [BooleanDecision.restrict, nodeCount]
  | split variableName onFalse onTrue ihFalse ihTrue =>
      simp only [BooleanDecision.restrict]
      split
      · cases selectedValue <;> simp_all [nodeCount] <;> omega
      · simp only [nodeCount]
        omega

theorem UsesOnly.zipWith (variableOrder : BooleanVariableNames)
    (operation : α -> β -> γ)
    {variables : BooleanVariableNames}
    (left : BooleanDecision α) (right : BooleanDecision β)
    (hleft : UsesOnly variables left) (hright : UsesOnly variables right)
    (hvariables : variables.Nodup)
    : UsesOnly variables
        (BooleanDecision.zipWith variableOrder operation left right) := by
  cases left with
  | leaf leftSummary =>
      cases hleft
      simp only [BooleanDecision.zipWith]
      exact hright.map _
  | split leftVariable leftFalse leftTrue =>
      cases hleft with
      | split hleftVariable hleftFalse hleftTrue =>
          cases right with
          | leaf rightSummary =>
              cases hright
              simp only [BooleanDecision.zipWith]
              exact (UsesOnly.split hleftVariable hleftFalse hleftTrue).map _
          | split rightVariable rightFalse rightTrue =>
              cases hright with
              | split hrightVariable hrightFalse hrightTrue =>
                  simp only [BooleanDecision.zipWith]
                  split <;> rename_i hequal
                  · subst rightVariable
                    exact .split hleftVariable
                      (UsesOnly.zipWith variableOrder operation _ _ hleftFalse hrightFalse
                        (hvariables.erase leftVariable))
                      (UsesOnly.zipWith variableOrder operation _ _ hleftTrue hrightTrue
                        (hvariables.erase leftVariable))
                  · split
                    · exact .split hleftVariable
                        (UsesOnly.zipWith variableOrder operation _ _ hleftFalse
                          ((UsesOnly.split hrightVariable hrightFalse hrightTrue).restrict
                            hvariables leftVariable false)
                          (hvariables.erase leftVariable))
                        (UsesOnly.zipWith variableOrder operation _ _ hleftTrue
                          ((UsesOnly.split hrightVariable hrightFalse hrightTrue).restrict
                            hvariables leftVariable true)
                          (hvariables.erase leftVariable))
                    · exact .split hrightVariable
                        (UsesOnly.zipWith variableOrder operation _ _
                          ((UsesOnly.split hleftVariable hleftFalse hleftTrue).restrict
                            hvariables rightVariable false)
                          hrightFalse (hvariables.erase rightVariable))
                        (UsesOnly.zipWith variableOrder operation _ _
                          ((UsesOnly.split hleftVariable hleftFalse hleftTrue).restrict
                            hvariables rightVariable true)
                          hrightTrue (hvariables.erase rightVariable))
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
    subst_vars
    simp only [nodeCount] at *
    omega

theorem UsesOnly.combineMap (algebra : Algebra)
    (variableOrder variables : BooleanVariableNames) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hvariables : variables.Nodup)
    (hsummary : ∀ item hitem, UsesOnly variables (summarize item hitem))
    : UsesOnly variables
        (BooleanDecision.combineMap algebra variableOrder items summarize) := by
  induction items with
  | nil => simpa [BooleanDecision.combineMap] using UsesOnly.leaf variables algebra.empty
  | cons item rest ih =>
      rw [BooleanDecision.combineMap]
      apply UsesOnly.zipWith variableOrder algebra.combine _ _
      · exact hsummary item (by simp)
      · exact ih
          (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
          (fun candidate hcandidate => hsummary candidate (by simp [hcandidate]))
      · exact hvariables

theorem UsesOnly.joinMap (algebra : Algebra)
    (variableOrder variables : BooleanVariableNames) (items : List α)
    (summarize : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (hvariables : variables.Nodup)
    (hsummary : ∀ item hitem, UsesOnly variables (summarize item hitem))
    : UsesOnly variables
        (BooleanDecision.joinMap algebra variableOrder items summarize) := by
  cases items with
  | nil => simpa [BooleanDecision.joinMap] using UsesOnly.leaf variables algebra.empty
  | cons item rest =>
      cases rest with
      | nil => simpa [BooleanDecision.joinMap] using hsummary item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap]
          apply UsesOnly.zipWith variableOrder algebra.join _ _
          · exact hsummary item (by simp)
          · exact UsesOnly.joinMap algebra variableOrder variables (next :: tail)
              (fun candidate hcandidate => summarize candidate (by simp [hcandidate]))
              hvariables
              (fun candidate hcandidate => hsummary candidate (by simp [hcandidate]))
          · exact hvariables
termination_by items.length

theorem combineMap_eq_leaf_of_eq_leaf
    (algebra : Algebra) (variableOrder : BooleanVariableNames)
    (items : List α)
    (decision : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (summary : ∀ item, item ∈ items -> algebra.Summary)
    (hleaf : ∀ item hitem, decision item hitem = .leaf (summary item hitem))
    : BooleanDecision.combineMap algebra variableOrder items decision
      = .leaf (TreeSummary.combineMap algebra items summary) := by
  induction items with
  | nil =>
      rw [BooleanDecision.combineMap, TreeSummary.combineMap]
  | cons item rest ih =>
      rw [BooleanDecision.combineMap, TreeSummary.combineMap,
        hleaf item (by simp)]
      rw [ih
        (decision := fun candidate hcandidate =>
          decision candidate (by simp [hcandidate]))
        (summary := fun candidate hcandidate =>
          summary candidate (by simp [hcandidate]))
        (by
          intro candidate hcandidate
          exact hleaf candidate (by simp [hcandidate]))]
      rw [BooleanDecision.zipWith, BooleanDecision.map]

theorem joinMap_eq_leaf_of_eq_leaf
    (algebra : Algebra) (variableOrder : BooleanVariableNames)
    (items : List α)
    (decision : ∀ item, item ∈ items -> BooleanDecision algebra.Summary)
    (summary : ∀ item, item ∈ items -> algebra.Summary)
    (hleaf : ∀ item hitem, decision item hitem = .leaf (summary item hitem))
    : BooleanDecision.joinMap algebra variableOrder items decision
      = .leaf (TreeSummary.joinMap algebra items summary) := by
  induction items with
  | nil =>
      rw [BooleanDecision.joinMap, TreeSummary.joinMap]
  | cons item rest ih =>
      cases rest with
      | nil =>
          simpa [BooleanDecision.joinMap, TreeSummary.joinMap] using
            hleaf item (by simp)
      | cons next tail =>
          rw [BooleanDecision.joinMap, TreeSummary.joinMap,
            hleaf item (by simp)]
          rw [ih
            (decision := fun candidate hcandidate =>
              decision candidate (by simp [hcandidate]))
            (summary := fun candidate hcandidate =>
              summary candidate (by simp [hcandidate]))
            (by
              intro candidate hcandidate
              exact hleaf candidate (by simp [hcandidate]))]
          rw [BooleanDecision.zipWith, BooleanDecision.map]

def override (assignment : Name -> Bool) (variableName : Name) (value : Bool)
    : Name -> Bool :=
  fun candidate => if candidate = variableName then value else assignment candidate

@[simp]
theorem override_self (assignment : Name -> Bool) (variableName : Name) (value : Bool)
    : override assignment variableName value variableName = value := by
  simp [override]

theorem override_of_ne (assignment : Name -> Bool) (variableName : Name)
    (value : Bool) {candidate : Name} (hne : candidate ≠ variableName)
    : override assignment variableName value candidate = assignment candidate := by
  simp [override, hne]

theorem UsesOnly.evaluate_override_of_not_mem
    {variables : BooleanVariableNames} {decision : BooleanDecision α}
    (hdecision : UsesOnly variables decision)
    (assignment : Name -> Bool) (variableName : Name) (value : Bool)
    (hvariable : variableName ∉ variables)
    : decision.evaluate (override assignment variableName value)
      = decision.evaluate assignment := by
  induction hdecision with
  | leaf => rfl
  | @split variables selectedVariable onFalse onTrue hselected _ _ ihFalse ihTrue =>
      have hne : selectedVariable ≠ variableName := by
        intro hequal
        subst selectedVariable
        exact hvariable hselected
      have hchild : variableName ∉ variables.erase selectedVariable := by
        intro hmem
        exact hvariable (List.mem_of_mem_erase hmem)
      simp only [BooleanDecision.evaluate, override_of_ne _ _ _ hne]
      split
      · exact ihTrue hchild
      · exact ihFalse hchild

theorem eraseDups_nodup (variables : BooleanVariableNames)
    : variables.eraseDups.Nodup := by
  cases variables with
  | nil => simp
  | cons variableName rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (rest.filter fun candidate => !candidate == variableName)
termination_by variables.length
decreasing_by
  subst_vars
  have hlength :=
    List.length_filter_le (fun candidate => !candidate == variableName) rest
  simp only [List.length_cons]
  omega

end BooleanDecision

open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open TreeSummary.Measure
open Measure

private def decisionUsesCasePhase : Nat := 3
private def decisionUsesTypeRegionsPhase : Nat := 2
private def decisionUsesFieldGroupsPhase : Nat := 1
private def decisionUsesChildTypesPhase : Nat := 0

mutual
  theorem CaseForest.summarizeDecision_usesOnly (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (parentType : Name)
      (inheritedBooleanCondition : List ConditionTree.BooleanLiteral)
      (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
      (environment : BooleanEnvironment)
      (hremaining : remainingVariables.Nodup)
      : BooleanDecision.UsesOnly remainingVariables
          (CaseForest.summarizeDecision algebra schema variableOrder remainingVariables
            parentType inheritedBooleanCondition tree possibleTypes environment) := by
    rw [CaseForest.summarizeDecision]
    split <;> rename_i hbranches
    · cases hnext
            : environment.nextUnresolved remainingVariables tree.booleanVariables with
      | some variableName =>
          simp only
          apply BooleanDecision.UsesOnly.split
          · exact List.mem_of_find?_eq_some hnext
          · exact CaseForest.summarizeDecision_usesOnly algebra schema variableOrder
              (remainingVariables.erase variableName) parentType
              inheritedBooleanCondition tree possibleTypes
              (environment.assign variableName false)
              (hremaining.erase variableName)
          · exact CaseForest.summarizeDecision_usesOnly algebra schema variableOrder
              (remainingVariables.erase variableName) parentType
              inheritedBooleanCondition tree possibleTypes
              (environment.assign variableName true)
              (hremaining.erase variableName)
      | none =>
          simp only
          exact CaseForest.summarizeTypeRegionsDecision_usesOnly algebra schema
            variableOrder remainingVariables parentType inheritedBooleanCondition tree
            (tree.typeRegions possibleTypes) environment hbranches hremaining
    · exact CaseForest.summarizeFieldGroupsDecision_usesOnly algebra schema variableOrder
        remainingVariables
        (tree.fieldGroups inheritedBooleanCondition possibleTypes) environment
        hremaining
  termination_by
    (
      caseForestResponseDepth tree,
      caseForestUnresolvedCount tree + remainingVariables.length,
      decisionUsesCasePhase,
      0
    )
  decreasing_by
    all_goals first
      | (apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
         · exact fieldGroupsResponseDepth_le inheritedBooleanCondition
             possibleTypes tree
         · omega
         · decide)
      | (apply quadruple_lt_of_depth_le_of_control_lt
         · exact Nat.le_refl _
         · have hmem := List.mem_of_find?_eq_some hnext
           have hlength := List.length_erase_of_mem hmem
           have hpositive : 0 < remainingVariables.length :=
             List.length_pos_of_mem hmem
           rw [hlength]
           omega)
      | (apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
         · exact Nat.le_refl _
         · omega
         · decide)

  theorem CaseForest.summarizeTypeRegionsDecision_usesOnly
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (parentType : Name)
      (inheritedBooleanCondition : List ConditionTree.BooleanLiteral)
      (tree : CaseForest) (regions : List PossibleTypeRegion)
      (environment : BooleanEnvironment)
      (hbranches : tree.hasUnresolvedBranches = true)
      (hremaining : remainingVariables.Nodup)
      : BooleanDecision.UsesOnly remainingVariables
          (CaseForest.summarizeTypeRegionsDecision algebra schema variableOrder
            remainingVariables parentType inheritedBooleanCondition tree regions
            environment hbranches) := by
    rw [CaseForest.summarizeTypeRegionsDecision]
    apply BooleanDecision.UsesOnly.joinMap algebra variableOrder remainingVariables
      regions _ hremaining
    intro region hregion
    exact CaseForest.summarizeDecision_usesOnly algebra schema variableOrder
      remainingVariables parentType
      (extendBooleanCondition inheritedBooleanCondition tree.booleanVariables
        environment.variableValues)
      (tree.resolveBranches region environment.variableValues) region environment
      hremaining
  termination_by
    (
      caseForestResponseDepth tree,
      caseForestUnresolvedCount tree + remainingVariables.length,
      decisionUsesTypeRegionsPhase,
      sizeOf regions
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_lt
    · exact resolveBranches_responseDepth_le region environment.variableValues tree
    · have hcount := resolveBranches_unresolvedCount_lt region
        environment.variableValues tree hbranches
      omega

  theorem CaseForest.summarizeFieldGroupsDecision_usesOnly
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (groups : List CollectedFieldGroup) (environment : BooleanEnvironment)
      (hremaining : remainingVariables.Nodup)
      : BooleanDecision.UsesOnly remainingVariables
          (CaseForest.summarizeFieldGroupsDecision algebra schema variableOrder
            remainingVariables groups environment) := by
    rw [CaseForest.summarizeFieldGroupsDecision]
    apply BooleanDecision.UsesOnly.combineMap algebra variableOrder remainingVariables
      groups _ hremaining
    intro group hgroup
    apply BooleanDecision.UsesOnly.map
    exact CaseForest.summarizeChildTypesDecision_usesOnly algebra schema variableOrder
      remainingVariables group (childParentTypes schema group) environment hremaining
  termination_by
    (
      collectedFieldGroupsResponseDepth groups,
      remainingVariables.length,
      decisionUsesFieldGroupsPhase,
      sizeOf groups
    )
  decreasing_by
    apply quadruple_lt_of_depth_le_of_control_le_of_phase_lt
    · exact collectedFieldGroupResponseDepth_le_of_mem group groups hgroup
    · exact Nat.le_refl _
    · decide

  theorem CaseForest.summarizeChildTypesDecision_usesOnly
      (algebra : Algebra) (schema : Schema)
      (variableOrder remainingVariables : BooleanVariableNames)
      (group : CollectedFieldGroup) (parentTypes : TypeNames)
      (environment : BooleanEnvironment)
      (hremaining : remainingVariables.Nodup)
      : BooleanDecision.UsesOnly remainingVariables
          (CaseForest.summarizeChildTypesDecision algebra schema variableOrder
            remainingVariables group parentTypes environment) := by
    rw [CaseForest.summarizeChildTypesDecision]
    apply BooleanDecision.UsesOnly.joinMap algebra variableOrder remainingVariables
      parentTypes _ hremaining
    intro childParentType hparentType
    exact CaseForest.summarizeDecision_usesOnly algebra schema variableOrder
      remainingVariables childParentType group.childInheritedBooleanCondition
      (.ofConditionTree
        (group.childTreeWithKnownFalsePruning schema childParentType
          environment.fixedVariableValues))
      (group.childTreeWithKnownFalsePruning schema childParentType
        environment.fixedVariableValues).condition.possibleTypes environment
      hremaining
  termination_by
    (
      collectedFieldGroupResponseDepth group,
      remainingVariables.length,
      decisionUsesChildTypesPhase,
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

end ExactCases
end TreeSummary
end GraphQL
