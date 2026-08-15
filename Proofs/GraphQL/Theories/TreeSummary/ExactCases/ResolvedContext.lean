import Proofs.GraphQL.Theories.ConditionTree.BooleanVariables
import Proofs.GraphQL.Theories.ConditionTree.KnownFalsePruning
import Proofs.GraphQL.Theories.TreeSummary.ExactCases.BooleanDecision

/-! Reduction of lazy exact-case traversal under a fully resolved Boolean context. -/

namespace GraphQL
namespace TreeSummary
namespace ExactCases

open GraphQL.ConditionTree
open GraphQL.Execution

-- Reference fold for one fixed Boolean environment. Soundness uses this resolved form
-- to relate concrete execution to one path through the lazy decision traversal. All
-- recursive calls operate on `CaseForest`, including cases composed from several
-- simultaneously active syntactic subtrees.
def summarizeConditionTreeResolved (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : Tree) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  CaseForest.summarize algebra schema parentType inheritedBooleanCondition
    (.ofConditionTree tree) tree.condition.possibleTypes variableValues
    fixedVariableValues

-- Selection-set specialization of the fixed-environment reference fold.
def summarizeSelectionSetResolved (algebra : Algebra) (schema : Schema)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (variableValues : VariableValues)
    (fixedVariableValues : VariableValues := variableValues)
    : algebra.Summary :=
  let tree :=
    ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition fixedVariableValues selectionSet
  summarizeConditionTreeResolved algebra schema parentType inheritedBooleanCondition tree
    variableValues fixedVariableValues

theorem BooleanEnvironment.ofCompleteValues_resolvedFor
    (variables : BooleanVariableNames) (values : VariableValues)
    : (BooleanEnvironment.ofCompleteValues variables values).ResolvedFor variables := by
  intro variableName hvariable
  induction variables with
  | nil => simp at hvariable
  | cons head rest ih =>
      by_cases heq : variableName = head
      · subst head
        simp only [BooleanEnvironment.ofCompleteValues, BooleanEnvironment.status?,
          List.map_cons, List.lookup_cons_self]
        cases hvalue : inputValueBoolean? values (.variable variableName) with
        | none => exact Or.inr rfl
        | some value => exact Or.inl ⟨value, rfl⟩
      · simp only [BooleanEnvironment.ofCompleteValues, BooleanEnvironment.status?,
          List.map_cons, List.lookup]
        rw [show (variableName == head) = false by simp [heq]]
        exact ih (by simpa [heq] using hvariable)

theorem CaseForest.summarizeDecision_eq_leaf_of_resolved
    (algebra : Algebra) (schema : Schema)
    (variableOrder remainingVariables : BooleanVariableNames)
    (parentType : Name) (inheritedBooleanCondition : List BooleanLiteral)
    (tree : CaseForest) (possibleTypes : PossibleTypeRegion)
    (environment : BooleanEnvironment)
    (hresolved
      : ∀ localVariables,
          environment.nextUnresolved remainingVariables localVariables = none)
    : CaseForest.summarizeDecision algebra schema variableOrder remainingVariables
        parentType inheritedBooleanCondition tree possibleTypes environment
      = .leaf
          (CaseForest.summarize algebra schema parentType inheritedBooleanCondition tree
            possibleTypes environment.variableValues
            environment.fixedVariableValues) := by
  revert hresolved
  apply CaseForest.summarizeDecision.induct schema
    (motive1 := fun remainingVariables parentType inheritedBooleanCondition tree
        possibleTypes environment =>
      (∀ localVariables,
          environment.nextUnresolved remainingVariables localVariables = none)
      -> CaseForest.summarizeDecision algebra schema variableOrder remainingVariables
          parentType inheritedBooleanCondition tree possibleTypes environment
        = .leaf
            (CaseForest.summarize algebra schema parentType inheritedBooleanCondition tree
              possibleTypes environment.variableValues
              environment.fixedVariableValues))
    (motive2 := fun remainingVariables groups environment =>
      (∀ localVariables,
          environment.nextUnresolved remainingVariables localVariables = none)
      -> CaseForest.summarizeFieldGroupsDecision algebra schema variableOrder
          remainingVariables groups environment
        = .leaf
            (CaseForest.summarizeFieldGroups algebra schema groups
              environment.variableValues environment.fixedVariableValues))
    (motive3 := fun remainingVariables group parentTypes environment =>
      (∀ localVariables,
          environment.nextUnresolved remainingVariables localVariables = none)
      -> CaseForest.summarizeChildTypesDecision algebra schema variableOrder
          remainingVariables group parentTypes environment
        = .leaf
            (CaseForest.summarizeChildTypes algebra schema group parentTypes
              environment.variableValues environment.fixedVariableValues))
    (motive4 := fun remainingVariables parentType inheritedBooleanCondition tree
        regions environment hbranches =>
      (∀ localVariables,
          environment.nextUnresolved remainingVariables localVariables = none)
      -> CaseForest.summarizeTypeRegionsDecision algebra schema variableOrder
          remainingVariables parentType inheritedBooleanCondition tree regions
          environment hbranches
        = .leaf
            (CaseForest.summarizeTypeRegions algebra schema parentType
              inheritedBooleanCondition tree regions environment.variableValues
              hbranches environment.fixedVariableValues))
  case case1 =>
    intro remainingVariables parentType inheritedBooleanCondition tree possibleTypes
      environment hbranches variableName hnext _ihFalse _ihTrue hresolved
    rw [hresolved tree.booleanVariables] at hnext
    contradiction
  case case2 =>
    intro remainingVariables parentType inheritedBooleanCondition tree possibleTypes
      environment hbranches _hnext ih hresolved
    rw [CaseForest.summarizeDecision, CaseForest.summarize]
    simp only [hbranches, ↓reduceDIte]
    rw [hresolved tree.booleanVariables]
    exact ih hresolved
  case case3 =>
    intro remainingVariables parentType inheritedBooleanCondition tree possibleTypes
      environment hbranches ih hresolved
    rw [CaseForest.summarizeDecision, CaseForest.summarize]
    simp only [hbranches, Bool.false_eq_true, ↓reduceDIte]
    exact ih hresolved
  case case4 =>
    intro remainingVariables groups environment ih hresolved
    rw [CaseForest.summarizeFieldGroupsDecision, CaseForest.summarizeFieldGroups]
    apply BooleanDecision.combineMap_eq_leaf_of_eq_leaf
    intro group hgroup
    rw [ih group hgroup hresolved]
    rfl
  case case5 =>
    intro remainingVariables group parentTypes environment ih hresolved
    rw [CaseForest.summarizeChildTypesDecision, CaseForest.summarizeChildTypes]
    apply BooleanDecision.joinMap_eq_leaf_of_eq_leaf
    intro childParentType _hparentType
    exact ih childParentType hresolved
  case case6 =>
    intro remainingVariables parentType inheritedBooleanCondition tree regions
      environment hbranches ih hresolved
    rw [CaseForest.summarizeTypeRegionsDecision, CaseForest.summarizeTypeRegions]
    apply BooleanDecision.joinMap_eq_leaf_of_eq_leaf
    intro region _hregion
    exact ih region hresolved

theorem BooleanEnvironment.summarizeCompletions_eq_of_resolvedFor
    (algebra : Algebra) (summarize : BooleanEnvironment -> algebra.Summary)
    (environment : BooleanEnvironment) (variables : BooleanVariableNames)
    (hresolved : environment.ResolvedFor variables)
    : environment.summarizeCompletions algebra summarize variables
      = summarize environment := by
  induction variables with
  | nil => simp [BooleanEnvironment.summarizeCompletions]
  | cons variableName rest ih =>
      rcases hresolved variableName (by simp) with ⟨value, hstatus⟩ | hstatus
      · rw [BooleanEnvironment.summarizeCompletions, hstatus]
        exact ih fun candidate hcandidate =>
          hresolved candidate (by simp [hcandidate])
      · rw [BooleanEnvironment.summarizeCompletions, hstatus]
        exact ih fun candidate hcandidate =>
          hresolved candidate (by simp [hcandidate])

theorem BooleanEnvironment.nextUnresolved_eq_none_of_resolvedFor
    (environment : BooleanEnvironment) (variables localVariables : BooleanVariableNames)
    (hresolved : environment.ResolvedFor variables)
    : environment.nextUnresolved variables localVariables = none := by
  unfold BooleanEnvironment.nextUnresolved
  apply List.find?_eq_none.mpr
  intro variableName hvariable
  rcases hresolved variableName hvariable with ⟨value, hstatus⟩ | hstatus
  · simp [hstatus]
  · simp [hstatus]

theorem summarizeConditionTree_eq_resolved_of_resolvedFor
    (algebra : Algebra) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (environment : BooleanEnvironment)
    (hresolved : environment.ResolvedFor (conditionTreeBooleanVariables tree).eraseDups)
    : summarizeConditionTree algebra schema parentType
        inheritedBooleanCondition tree environment
      = summarizeConditionTreeResolved algebra schema parentType
          inheritedBooleanCondition tree environment.variableValues
          environment.fixedVariableValues := by
  let variables := (conditionTreeBooleanVariables tree).eraseDups
  have hnext : ∀ localVariables,
      environment.nextUnresolved variables localVariables = none :=
    fun localVariables =>
      environment.nextUnresolved_eq_none_of_resolvedFor variables localVariables hresolved
  have hdecision :=
    CaseForest.summarizeDecision_eq_leaf_of_resolved algebra schema variables variables
      parentType inheritedBooleanCondition (.ofConditionTree tree)
      tree.condition.possibleTypes environment hnext
  unfold summarizeConditionTree summarizeConditionTreeDecision
    summarizeConditionTreeResolved
  change BooleanEnvironment.summarizeCompletions algebra
      (fun completed =>
        (CaseForest.summarizeDecision algebra schema variables variables parentType
          inheritedBooleanCondition (.ofConditionTree tree)
          tree.condition.possibleTypes completed).collapse algebra)
      variables environment
    = CaseForest.summarize algebra schema parentType inheritedBooleanCondition
        (.ofConditionTree tree) tree.condition.possibleTypes environment.variableValues
        environment.fixedVariableValues
  rw [environment.summarizeCompletions_eq_of_resolvedFor algebra _ variables hresolved]
  rw [hdecision]
  rfl

theorem summarizeSelectionSet_eq_resolved_of_resolvedFor
    (algebra : Algebra) (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection) (environment : BooleanEnvironment)
    (hresolved
      : environment.ResolvedFor
          (conditionTreeBooleanVariables
            (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
              inheritedBooleanCondition environment.fixedVariableValues
              selectionSet)).eraseDups)
    : summarizeSelectionSet algebra schema parentType
        inheritedBooleanCondition selectionSet environment
      = summarizeSelectionSetResolved algebra schema parentType
          inheritedBooleanCondition selectionSet environment.variableValues
          environment.fixedVariableValues := by
  unfold summarizeSelectionSet summarizeSelectionSetResolved
  exact summarizeConditionTree_eq_resolved_of_resolvedFor algebra schema
    parentType inheritedBooleanCondition
    (ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema parentType
      inheritedBooleanCondition environment.fixedVariableValues selectionSet)
    environment hresolved

-- Operation specialization for the canonical total context built from coerced request
-- values. This is the semantic bridge for the variable-aware resolved fast path.
theorem summarizeOperationSelectionSet_eq_resolved_ofCompleteValues
    (algebra : Algebra) (schema : Schema) (operation : Operation)
    (variableValues : VariableValues)
    : summarizeSelectionSet algebra schema (operation.rootType schema) []
        operation.selectionSet
        (BooleanEnvironment.ofCompleteValues
          (operationBooleanVariables operation) variableValues)
      = summarizeSelectionSetResolved algebra schema (operation.rootType schema) []
          operation.selectionSet variableValues := by
  let tree := ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning schema
    (operation.rootType schema) [] variableValues operation.selectionSet
  apply summarizeSelectionSet_eq_resolved_of_resolvedFor
  intro variableName hvariable
  apply BooleanEnvironment.ofCompleteValues_resolvedFor
    (operationBooleanVariables operation) variableValues variableName
  simp only [operationBooleanVariables, List.mem_eraseDups]
  apply ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning_booleanVariablesWithin schema
    (operation.rootType schema) [] variableValues operation.selectionSet variableName
  simpa only [tree, BooleanEnvironment.ofCompleteValues, List.mem_eraseDups] using
    hvariable

end ExactCases
end TreeSummary
end GraphQL
