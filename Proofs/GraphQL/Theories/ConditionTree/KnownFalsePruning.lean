import Proofs.GraphQL.Theories.ConditionTree.BooleanVariables
import Proofs.GraphQL.Theories.ConditionTree.ExtractionCoherence
import Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction

/-! Structural witnesses for known-false condition-tree pruning. -/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution
open Execution.FieldGroups

-- Every Boolean known by the pruning environment agrees with the runtime request.
-- Missing runtime values use the modeled directive default (`false`); this is enough
-- because pruning consults only values that it knows.
def BooleanValuesMatchForPruning (runtimeValues pruningValues : VariableValues) : Prop :=
  ∀ variableName value,
    inputValueBoolean? pruningValues (.variable variableName) = some value
    -> value = (inputValueBoolean? runtimeValues (.variable variableName)).getD false

-- Variable-specialized extraction removes only selections known inactive under this
-- already-coerced environment. Unlike `ExtractionSound`, the environment is fixed:
-- asking the pruned tree to cover a different request would be unsound. Its theorem
-- witness is `ConditionTree.knownFalsePruning_sound` below.
def KnownFalsePruningSound (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (runtimeValues pruningValues : VariableValues) (selectionSet : List Selection)
    : Prop :=
  BooleanValuesMatchForPruning runtimeValues pruningValues
  -> ∀ {ObjectRef : Type} (executionParentType runtimeType : Name) (ref : ObjectRef),
      booleanConditionAllows runtimeValues inheritedBooleanCondition = true
      -> (schema.getPossibleTypes parentType).contains runtimeType = true
      -> ∀ field,
          field
            ∈ (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
                inheritedBooleanCondition pruningValues
                selectionSet).collectRuntimeFields
                runtimeValues executionParentType runtimeType
          ↔ field
            ∈ flattenCollectedFields
                (Execution.collectFields schema runtimeValues executionParentType
                  (.object runtimeType ref) selectionSet)

theorem pruneKnownFalseSelections_booleanVariables_subset
    (variableValues : VariableValues) (selectionSet : List Selection)
    (variableName : Name)
    : variableName
        ∈ selectionSetBooleanVariables
            (pruneKnownFalseSelections variableValues selectionSet)
      -> variableName ∈ selectionSetBooleanVariables selectionSet := by
  cases selectionSet with
  | nil => simp [pruneKnownFalseSelections, selectionSetBooleanVariables]
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          rw [pruneKnownFalseSelections]
          split
          · intro hvariable
            apply List.mem_append.mpr
            exact Or.inr
              (pruneKnownFalseSelections_booleanVariables_subset variableValues rest
                variableName hvariable)
          · simp only [selectionSetBooleanVariables, selectionBooleanVariables,
              List.mem_append]
            intro hvariable
            rcases hvariable with hhead | hrest
            · exact Or.inl hhead
            · exact Or.inr
                (pruneKnownFalseSelections_booleanVariables_subset variableValues rest
                  variableName hrest)
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [pruneKnownFalseSelections]
          split
          · intro hvariable
            apply List.mem_append.mpr
            exact Or.inr
              (pruneKnownFalseSelections_booleanVariables_subset variableValues rest
                variableName hvariable)
          · simp only [selectionSetBooleanVariables, selectionBooleanVariables]
            intro hvariable
            rcases List.mem_append.mp hvariable with hhead | hrest
            · apply List.mem_append.mpr
              apply Or.inl
              rcases List.mem_append.mp hhead with hdirectives | hchild
              · exact List.mem_append.mpr (Or.inl hdirectives)
              · exact List.mem_append.mpr <| Or.inr
                  (pruneKnownFalseSelections_booleanVariables_subset variableValues
                    childSelectionSet variableName hchild)
            · apply List.mem_append.mpr
              exact Or.inr
                (pruneKnownFalseSelections_booleanVariables_subset variableValues rest
                  variableName hrest)
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem ofSelectionSetInScopeWithKnownFalsePruning_booleanVariablesWithin
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (selectionSet : List Selection)
    (variableName : Name)
    (hvariable
      : variableName
        ∈ conditionTreeBooleanVariables
            (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
              inheritedBooleanCondition variableValues selectionSet))
    : variableName ∈ selectionSetBooleanVariables selectionSet := by
  apply pruneKnownFalseSelections_booleanVariables_subset variableValues selectionSet
  exact ofSelectionSetInScope_booleanVariablesWithin schema parentType
    inheritedBooleanCondition (pruneKnownFalseSelections variableValues selectionSet)
    variableName hvariable

theorem ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (selectionSet : List Selection)
    : Tree.BranchesCoherent schema inheritedBooleanCondition
        (ofSelectionSetInScopeWithKnownFalsePruning schema parentType
          inheritedBooleanCondition variableValues selectionSet) := by
  unfold ofSelectionSetInScopeWithKnownFalsePruning
  exact ofSelectionSetInScope_branchesCoherent schema parentType
    inheritedBooleanCondition (pruneKnownFalseSelections variableValues selectionSet)

theorem DirectiveApplication.allows_eq_false_of_knownFalse
    (runtimeValues pruningValues : VariableValues)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues)
    (directive : DirectiveApplication)
    (hfalse : directiveKnownFalse pruningValues directive = true)
    : directiveAllowsSelectionBool runtimeValues directive = false := by
  cases directive with
  | skip input =>
      cases input <;>
        simp [directiveKnownFalse] at hfalse
      case «variable» variableName =>
        cases hvalue : inputValueBoolean? pruningValues (.variable variableName) with
        | none =>
            simp [hvalue] at hfalse
        | some actual =>
            have hactual := hmatch variableName actual hvalue
            cases hruntime
                  : inputValueBoolean? runtimeValues (.variable variableName) <;>
              cases actual <;>
              simp [directiveAllowsSelectionBool,
                hvalue, hruntime] at hfalse hactual ⊢ <;> assumption
  | «include» input =>
      cases input <;>
        simp [directiveKnownFalse] at hfalse
      case «variable» variableName =>
        cases hvalue : inputValueBoolean? pruningValues (.variable variableName) with
        | none =>
            simp [hvalue] at hfalse
        | some actual =>
            have hactual := hmatch variableName actual hvalue
            cases hruntime
                  : inputValueBoolean? runtimeValues (.variable variableName) <;>
              cases actual <;>
              simp [directiveAllowsSelectionBool,
                hvalue, hruntime] at hfalse hactual ⊢ <;> assumption

theorem selectionDirectivesAllowBool_eq_false_of_any_knownFalse
    (runtimeValues pruningValues : VariableValues)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues)
    (directives : List DirectiveApplication)
    (hfalse : directives.any (directiveKnownFalse pruningValues) = true)
    : selectionDirectivesAllowBool runtimeValues directives = false := by
  induction directives with
  | nil => simp at hfalse
  | cons head rest ih =>
      simp only [List.any_cons, Bool.or_eq_true] at hfalse
      rw [selectionDirectivesAllowBool, List.all_cons]
      rcases hfalse with hhead | hrest
      · rw [DirectiveApplication.allows_eq_false_of_knownFalse runtimeValues
          pruningValues hmatch head hhead]
        rfl
      · have htail := ih hrest
        simp only [selectionDirectivesAllowBool] at htail
        rw [htail]
        simp

theorem collectFlatFields_pruneKnownFalseSelections
    {ObjectRef : Type} (schema : Schema)
    (runtimeValues pruningValues : VariableValues)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues)
    (executionParentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : collectFlatFields schema runtimeValues executionParentType source
        (pruneKnownFalseSelections pruningValues selectionSet)
      = collectFlatFields schema runtimeValues executionParentType source
          selectionSet := by
  cases selectionSet with
  | nil => simp [pruneKnownFalseSelections, collectFlatFields]
  | cons selection rest =>
      cases selection with
      | field responseName fieldName arguments directives childSelectionSet =>
          rw [pruneKnownFalseSelections]
          split <;> rename_i hknownFalse
          · have hdirectives :=
              selectionDirectivesAllowBool_eq_false_of_any_knownFalse runtimeValues
                pruningValues hmatch directives (by
                  simpa [directivesKnownFalse] using hknownFalse)
            simp [collectFlatFields, collectFlatSelection, hdirectives,
              collectFlatFields_pruneKnownFalseSelections schema runtimeValues
                pruningValues hmatch executionParentType source rest]
          · simp [collectFlatFields,
              collectFlatFields_pruneKnownFalseSelections schema runtimeValues
                pruningValues hmatch executionParentType source rest]
      | inlineFragment typeCondition directives childSelectionSet =>
          rw [pruneKnownFalseSelections]
          split <;> rename_i hknownFalse
          · have hdirectives :=
              selectionDirectivesAllowBool_eq_false_of_any_knownFalse runtimeValues
                pruningValues hmatch directives (by
                  simpa [directivesKnownFalse] using hknownFalse)
            cases typeCondition <;>
              simp [collectFlatFields, collectFlatSelection, hdirectives,
                collectFlatFields_pruneKnownFalseSelections schema runtimeValues
                  pruningValues hmatch executionParentType source rest]
          · cases typeCondition <;>
              simp [collectFlatFields, collectFlatSelection,
                collectFlatFields_pruneKnownFalseSelections schema runtimeValues
                  pruningValues hmatch executionParentType source childSelectionSet,
                collectFlatFields_pruneKnownFalseSelections schema runtimeValues
                  pruningValues hmatch executionParentType source rest]
termination_by SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

theorem knownFalsePruning_sound
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (runtimeValues pruningValues : VariableValues) (selectionSet : List Selection)
    : KnownFalsePruningSound schema parentType inheritedBooleanCondition
        runtimeValues pruningValues selectionSet := by
  intro hmatch ObjectRef executionParentType runtimeType ref hinherited hpossible field
  let pruned := pruneKnownFalseSelections pruningValues selectionSet
  have hcanonical :=
    (extraction_sound schema parentType inheritedBooleanCondition pruned
      (ObjectRef := ObjectRef) runtimeValues executionParentType runtimeType ref
      hinherited hpossible field)
  rw [ofSelectionSetInScopeWithKnownFalsePruning]
  rw [hcanonical]
  rw [← collectFlatFields_mem_collectFields schema runtimeValues executionParentType
    (.object runtimeType ref) pruned field]
  rw [collectFlatFields_pruneKnownFalseSelections schema runtimeValues pruningValues
    hmatch executionParentType (.object runtimeType ref) selectionSet]
  exact collectFlatFields_mem_collectFields schema runtimeValues executionParentType
    (.object runtimeType ref) selectionSet field

theorem knownFalsePruning_runtimeGroups_occurrence_equivalent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (runtimeValues pruningValues : VariableValues)
    (selectionSet : List Selection)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues)
    {ObjectRef : Type} (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows runtimeValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : (flattenCollectedFields
        ((ofSelectionSetInScopeWithKnownFalsePruning schema parentType
            inheritedBooleanCondition pruningValues
            selectionSet).collectRuntimeFieldGroups
          runtimeValues executionParentType runtimeType)).Perm
        (flattenCollectedFields
          (collectFields schema runtimeValues executionParentType
            (.object runtimeType ref) selectionSet)) := by
  let pruned := pruneKnownFalseSelections pruningValues selectionSet
  have hcanonical :=
    RuntimeExtraction.extraction_runtimeGroups_occurrence_equivalent schema parentType
      inheritedBooleanCondition pruned runtimeValues executionParentType runtimeType ref
      hinherited hpossible
  rw [ofSelectionSetInScopeWithKnownFalsePruning]
  apply hcanonical.trans
  apply (RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema runtimeValues
    executionParentType (.object runtimeType ref) pruned).symm.trans
  rw [collectFlatFields_pruneKnownFalseSelections schema runtimeValues pruningValues
    hmatch executionParentType (.object runtimeType ref) selectionSet]
  exact RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema runtimeValues
    executionParentType (.object runtimeType ref) selectionSet

theorem knownFalsePruning_runtimeGroups_permutationEquivalent
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (runtimeValues pruningValues : VariableValues)
    (selectionSet : List Selection)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues)
    {ObjectRef : Type} (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows runtimeValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : RuntimeGroupsPermutationEquivalent
        ((ofSelectionSetInScopeWithKnownFalsePruning schema parentType
            inheritedBooleanCondition pruningValues
            selectionSet).collectRuntimeFieldGroups
          runtimeValues executionParentType runtimeType)
        (collectFields schema runtimeValues executionParentType
          (.object runtimeType ref) selectionSet) := by
  constructor
  · exact Tree.collectRuntimeFieldGroups_wellFormed runtimeValues executionParentType
      runtimeType _
  · exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      runtimeValues executionParentType (.object runtimeType ref) selectionSet
  · exact (Tree.collectRuntimeFieldGroups_exact runtimeValues executionParentType
      runtimeType _).1
  · exact (executableGroupNamesNodup_iff_map_fst_nodup _).mp
            (NormalForm.collectFields_namesNodup schema runtimeValues executionParentType
              (.object runtimeType ref) selectionSet)
  · exact knownFalsePruning_runtimeGroups_occurrence_equivalent schema parentType
      inheritedBooleanCondition runtimeValues pruningValues selectionSet hmatch
      executionParentType runtimeType ref hinherited hpossible

theorem knownFalsePruning_runtimeGroups_permutationEquivalent_toPermutedSelectionSet
    (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (runtimeValues pruningValues : VariableValues)
    {leftSelectionSet rightSelectionSet : List Selection}
    (hselectionSet : leftSelectionSet.Perm rightSelectionSet)
    (hmatch : BooleanValuesMatchForPruning runtimeValues pruningValues) {ObjectRef : Type}
    (executionParentType runtimeType : Name) (ref : ObjectRef)
    (hinherited : booleanConditionAllows runtimeValues inheritedBooleanCondition = true)
    (hpossible : (schema.getPossibleTypes parentType).contains runtimeType = true)
    : RuntimeGroupsPermutationEquivalent
        ((ofSelectionSetInScopeWithKnownFalsePruning schema parentType
            inheritedBooleanCondition pruningValues
            leftSelectionSet).collectRuntimeFieldGroups
          runtimeValues executionParentType runtimeType)
        (collectFields schema runtimeValues executionParentType
          (.object runtimeType ref) rightSelectionSet) := by
  constructor
  · exact Tree.collectRuntimeFieldGroups_wellFormed runtimeValues executionParentType
      runtimeType _
  · exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
      runtimeValues executionParentType (.object runtimeType ref) rightSelectionSet
  · exact (Tree.collectRuntimeFieldGroups_exact runtimeValues executionParentType
      runtimeType _).1
  · exact (executableGroupNamesNodup_iff_map_fst_nodup _).mp
            (NormalForm.collectFields_namesNodup schema runtimeValues executionParentType
              (.object runtimeType ref) rightSelectionSet)
  · apply (knownFalsePruning_runtimeGroups_occurrence_equivalent schema parentType
      inheritedBooleanCondition runtimeValues pruningValues leftSelectionSet hmatch
      executionParentType runtimeType ref hinherited hpossible).trans
    apply (RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema
      runtimeValues executionParentType (.object runtimeType ref)
      leftSelectionSet).symm.trans
    apply (RuntimeExtraction.collectFlatFields_perm_of_selectionSet_perm schema
      runtimeValues executionParentType (.object runtimeType ref) hselectionSet).trans
    exact RuntimeExtraction.collectFlatFields_perm_flatten_collectFields schema
      runtimeValues executionParentType (.object runtimeType ref) rightSelectionSet

end ConditionTree
end GraphQL
