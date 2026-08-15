import Proofs.GraphQL.Theories.QueryInclusion.GuardedFieldGroup.Extraction

/-! Type-region and Boolean-region invariance for guarded field groups. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open SelectionConditions

theorem guardedFieldGroupTypeRegions_cover
    (parentRegion : List Name) (left right : GuardedFieldGroup)
    {runtimeType : Name} (hruntime : runtimeType ∈ parentRegion)
    : ∃ region,
        region ∈ guardedFieldGroupTypeRegions parentRegion left right
        ∧ runtimeType ∈ region := by
  have hnonempty : parentRegion.isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr fun hempty => by
      rw [hempty] at hruntime
      simp at hruntime
  unfold guardedFieldGroupTypeRegions
  apply foldRefinePossibleTypeRegions_cover
  exact ⟨parentRegion, by simp [hnonempty], hruntime⟩

theorem guardedFieldGroupTypeRegions_subset
    (parentRegion : List Name) (left right : GuardedFieldGroup)
    {region : List Name}
    (hregion : region ∈ guardedFieldGroupTypeRegions parentRegion left right)
    {runtimeType : Name} (hruntime : runtimeType ∈ region)
    : runtimeType ∈ parentRegion := by
  unfold guardedFieldGroupTypeRegions at hregion
  rcases foldRefinePossibleTypeRegions_subset
      (guardedFieldGroupConditions left ++ guardedFieldGroupConditions right)
      (if parentRegion.isEmpty then [] else [parentRegion]) hregion hruntime with
    ⟨source, hsource, hruntime⟩
  cases hempty : parentRegion.isEmpty <;> simp [hempty] at hsource
  subst source
  exact hruntime

theorem guardedFieldGroupTypeRegions_uniform_left
    (parentRegion : List Name) (left right : GuardedFieldGroup)
    {entry : SelectionConditions.ConditionedField} (hentry : entry ∈ left.entries)
    : RegionsUniformForPossibleTypes
        (guardedFieldGroupTypeRegions parentRegion left right)
        entry.condition.possibleTypes := by
  unfold guardedFieldGroupTypeRegions
  apply foldRefinePossibleTypeRegions_uniform_of_mem
  exact List.mem_append.mpr
    (Or.inl (List.mem_map.mpr ⟨entry, hentry, rfl⟩))

theorem guardedFieldGroupTypeRegions_uniform_right
    (parentRegion : List Name) (left right : GuardedFieldGroup)
    {entry : SelectionConditions.ConditionedField} (hentry : entry ∈ right.entries)
    : RegionsUniformForPossibleTypes
        (guardedFieldGroupTypeRegions parentRegion left right)
        entry.condition.possibleTypes := by
  unfold guardedFieldGroupTypeRegions
  apply foldRefinePossibleTypeRegions_uniform_of_mem
  exact List.mem_append.mpr
    (Or.inr (List.mem_map.mpr ⟨entry, hentry, rfl⟩))

theorem guardedFieldGroupBooleanVariables_mem_left
    (left right : GuardedFieldGroup)
    {entry : SelectionConditions.ConditionedField}
    (hentry : entry ∈ left.entries) {literal : SelectionConditions.BooleanLiteral}
    (hliteral : literal ∈ entry.condition.booleanCondition)
    : literal.variableName ∈ guardedFieldGroupBooleanVariables left right := by
  unfold guardedFieldGroupBooleanVariables
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨entry, List.mem_append.mpr (Or.inl hentry), ?_⟩
  exact List.mem_map.mpr ⟨literal, hliteral, rfl⟩

theorem guardedFieldGroupBooleanVariables_mem_right
    (left right : GuardedFieldGroup)
    {entry : SelectionConditions.ConditionedField}
    (hentry : entry ∈ right.entries) {literal : SelectionConditions.BooleanLiteral}
    (hliteral : literal ∈ entry.condition.booleanCondition)
    : literal.variableName ∈ guardedFieldGroupBooleanVariables left right := by
  unfold guardedFieldGroupBooleanVariables
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨entry, List.mem_append.mpr (Or.inr hentry), ?_⟩
  exact List.mem_map.mpr ⟨literal, hliteral, rfl⟩

theorem booleanLiteral_allows_eq_of_boolean_input_eq
    {leftValues rightValues : VariableValues}
    (literal : SelectionConditions.BooleanLiteral)
    (hagrees
      : inputValueBoolean? leftValues (.variable literal.variableName)
        = inputValueBoolean? rightValues (.variable literal.variableName))
    : literal.allows leftValues = literal.allows rightValues := by
  cases literal <;>
    simp only [SelectionConditions.BooleanLiteral.variableName] at hagrees <;>
    simp only [SelectionConditions.BooleanLiteral.allows,
      SelectionConditions.BooleanLiteral.toDirective,
      Execution.directiveAllowsSelectionBool] <;>
    rw [hagrees]

theorem booleanConditionAllows_eq_of_variables_agree
    {leftValues rightValues : VariableValues}
    {variables : List Name} {condition : List SelectionConditions.BooleanLiteral}
    (hvariables : ∀ literal, literal ∈ condition -> literal.variableName ∈ variables)
    (hagrees
      : ∀ variableName,
          variableName ∈ variables
          -> inputValueBoolean? leftValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
    : SelectionConditions.booleanConditionAllows leftValues condition
      = SelectionConditions.booleanConditionAllows rightValues condition := by
  induction condition with
  | nil => rfl
  | cons literal rest ih =>
      rw [SelectionConditions.booleanConditionAllows,
        SelectionConditions.booleanConditionAllows,
        booleanLiteral_allows_eq_of_boolean_input_eq literal
          (hagrees literal.variableName (hvariables literal (by simp))),
        ih]
      intro candidate hcandidate
      exact hvariables candidate (by simp [hcandidate])

theorem guardedFieldCondition_allows_eq_of_region_and_variables
    (parentRegion : List Name) (left right : GuardedFieldGroup)
    {entry : SelectionConditions.ConditionedField}
    (hentry : entry ∈ left.entries ∨ entry ∈ right.entries)
    {region : List Name}
    (hregion : region ∈ guardedFieldGroupTypeRegions parentRegion left right)
    {leftRuntimeType rightRuntimeType : Name}
    (hleftRuntime : leftRuntimeType ∈ region)
    (hrightRuntime : rightRuntimeType ∈ region)
    {leftValues rightValues : VariableValues}
    (hagrees
      : ∀ variableName,
          variableName ∈ guardedFieldGroupBooleanVariables left right
          -> inputValueBoolean? leftValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
    : entry.condition.allows leftValues leftRuntimeType
      = entry.condition.allows rightValues rightRuntimeType := by
  unfold SelectionConditions.Condition.allows
  have htype : entry.condition.possibleTypes.contains leftRuntimeType
      = entry.condition.possibleTypes.contains rightRuntimeType := by
    rcases hentry with hleft | hright
    · exact (guardedFieldGroupTypeRegions_uniform_left parentRegion left right hleft)
        region hregion leftRuntimeType hleftRuntime rightRuntimeType hrightRuntime
    · exact (guardedFieldGroupTypeRegions_uniform_right parentRegion left right hright)
        region hregion leftRuntimeType hleftRuntime rightRuntimeType hrightRuntime
  rw [htype]
  congr 1
  apply booleanConditionAllows_eq_of_variables_agree
  · intro literal hliteral
    rcases hentry with hleft | hright
    · exact guardedFieldGroupBooleanVariables_mem_left left right hleft hliteral
    · exact guardedFieldGroupBooleanVariables_mem_right left right hright hliteral
  · exact hagrees

theorem guardedFieldExecutableFields_eq_of_region_and_variables
    (parentRegion : List Name) (left right group : GuardedFieldGroup)
    (hgroup : group = left ∨ group = right)
    {region : List Name}
    (hregion : region ∈ guardedFieldGroupTypeRegions parentRegion left right)
    {leftRuntimeType rightRuntimeType : Name}
    (hleftRuntime : leftRuntimeType ∈ region)
    (hrightRuntime : rightRuntimeType ∈ region)
    {leftValues rightValues : VariableValues}
    (hagrees
      : ∀ variableName,
          variableName ∈ guardedFieldGroupBooleanVariables left right
          -> inputValueBoolean? leftValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
    (executionParentType : Name)
    : guardedFieldExecutableFields leftValues executionParentType leftRuntimeType
        group.responseName group.entries
      = guardedFieldExecutableFields rightValues executionParentType rightRuntimeType
          group.responseName group.entries := by
  unfold guardedFieldExecutableFields
  apply congrArg List.flatten
  apply List.map_congr_left
  intro entry hentry
  have hentry' : entry ∈ left.entries ∨ entry ∈ right.entries := by
    rcases hgroup with rfl | rfl
    · exact Or.inl hentry
    · exact Or.inr hentry
  rw [guardedFieldCondition_allows_eq_of_region_and_variables parentRegion
    left right hentry' hregion hleftRuntime hrightRuntime hagrees]

theorem guardedFieldExecutableFields_withParentType (variableValues : VariableValues)
    (sourceParentType targetParentType runtimeType : Name) (responseName : Name)
    (entries : List SelectionConditions.ConditionedField)
    : (guardedFieldExecutableFields variableValues sourceParentType runtimeType
        responseName entries).map
        (executableFieldWithParentType targetParentType)
      = guardedFieldExecutableFields variableValues targetParentType runtimeType
          responseName entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      change ((if entry.condition.allows variableValues runtimeType then
                  [({
                      parentType := sourceParentType
                      responseName
                      fieldName := entry.field.fieldName
                      arguments := entry.field.arguments
                      selectionSet := entry.field.selectionSet
                    }
                    : ExecutableField)]
                else
                  [])
                ++ guardedFieldExecutableFields variableValues sourceParentType
                    runtimeType responseName rest).map
                (executableFieldWithParentType targetParentType)
              = (if entry.condition.allows variableValues runtimeType then
                    [({
                        parentType := targetParentType
                        responseName
                        fieldName := entry.field.fieldName
                        arguments := entry.field.arguments
                        selectionSet := entry.field.selectionSet
                      }
                      : ExecutableField)]
                  else
                    [])
                ++ guardedFieldExecutableFields variableValues targetParentType
                    runtimeType responseName rest
      rw [List.map_append, ih]
      cases hcondition : entry.condition.allows variableValues runtimeType <;>
        simp [executableFieldWithParentType]

theorem executableFieldsAsGroup_withParentType
    (sourceParentType targetParentType runtimeType responseName : Name)
    (variableValues : VariableValues)
    (entries : List SelectionConditions.ConditionedField)
    : executableGroupsWithParentType targetParentType
        (executableFieldsAsGroup responseName
          (guardedFieldExecutableFields variableValues sourceParentType runtimeType
            responseName entries))
      = executableFieldsAsGroup responseName
          (guardedFieldExecutableFields variableValues targetParentType runtimeType
            responseName entries) := by
  unfold executableGroupsWithParentType
  cases hfields
        : guardedFieldExecutableFields variableValues sourceParentType
            runtimeType responseName entries with
  | nil =>
      have htarget : guardedFieldExecutableFields variableValues targetParentType
          runtimeType responseName entries = [] := by
        have hmap := guardedFieldExecutableFields_withParentType variableValues
          sourceParentType targetParentType runtimeType responseName entries
        rw [hfields] at hmap
        simpa using hmap.symm
      simp [executableFieldsAsGroup, htarget]
  | cons field rest =>
      have htarget : guardedFieldExecutableFields variableValues targetParentType
          runtimeType responseName entries
        = (field :: rest).map (executableFieldWithParentType targetParentType) := by
        have hmap := guardedFieldExecutableFields_withParentType variableValues
          sourceParentType targetParentType runtimeType responseName entries
        rw [hfields] at hmap
        exact hmap.symm
      simp [executableFieldsAsGroup, htarget, executableGroupWithParentType]

end QueryInclusion
end GraphQL
