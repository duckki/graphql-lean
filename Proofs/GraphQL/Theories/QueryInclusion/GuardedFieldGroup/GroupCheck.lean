import Proofs.GraphQL.Theories.QueryInclusion.GuardedFieldGroup.Regions
import Proofs.GraphQL.Theories.SelectionConditions.BooleanCoverage

/-! Soundness and completeness of response-local guarded group checking. -/

namespace GraphQL
namespace QueryInclusion

open Execution
open Execution.FieldGroups
open SelectionConditions

def guardedFieldChildIncludesBool (schema : Schema) (responseFuel : Nat)
    (variableValues : VariableValues) (possibleTypes : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    : Bool :=
  selectionSetSyntacticInclusionShortcutBool responseFuel leftSelectionSet
    rightSelectionSet
  ||  let leftEntries :=
        SelectionConditions.ofTypeRegion schema possibleTypes leftSelectionSet
      let rightEntries :=
        SelectionConditions.ofTypeRegion schema possibleTypes rightSelectionSet
      guardedFieldGroupsIncludeWithFuel schema responseFuel none variableValues
        (guardedFieldGroups leftEntries) (guardedFieldGroups rightEntries)

def guardedFieldGroupCaseIncludesBool (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (fieldValues : VariableValues) (runtimeType : Name)
    (left right : GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    : Bool :=
  let executionParentType := fixedExecutionParentType.getD runtimeType
  let leftFields :=
    guardedFieldExecutableFields fieldValues executionParentType runtimeType
      left.responseName left.entries
  let rightFields :=
    guardedFieldExecutableFields fieldValues executionParentType runtimeType
      right.responseName right.entries
  match responseFuel with
  | 0 => rightFields.isEmpty
  | _responseFuel + 1 =>
      executableGroupsIncludeBool schema
        (fun outputType leftSelectionSet rightSelectionSet =>
          childIncludes (schema.getPossibleTypes outputType.namedType)
            leftSelectionSet rightSelectionSet)
        (executableFieldsAsGroup left.responseName leftFields)
        (executableFieldsAsGroup right.responseName rightFields)

theorem guardedFieldExecutableFields_origin (variableValues : VariableValues)
    (executionParentType runtimeType responseName : Name)
    (entries : List SelectionConditions.ConditionedField) (field : ExecutableField)
    (hfield
      : field
        ∈ guardedFieldExecutableFields variableValues executionParentType
            runtimeType responseName entries)
    : ∃ entry,
        entry ∈ entries
        ∧ entry.condition.allows variableValues runtimeType = true
        ∧ field
          = {
            parentType := executionParentType
            responseName
            fieldName := entry.field.fieldName
            arguments := entry.field.arguments
            selectionSet := entry.field.selectionSet
          } := by
  unfold guardedFieldExecutableFields at hfield
  rcases List.mem_flatMap.mp hfield with ⟨entry, hentry, hactive⟩
  split at hactive
  · rename_i hallows
    simp only [List.mem_singleton] at hactive
    exact ⟨entry, hentry, hallows, hactive⟩
  · simp at hactive

theorem guardedFieldExecutableFields_empty_of_no_runtime_entries
    (variableValues : VariableValues)
    (executionParentType runtimeType responseName : Name)
    (entries : List SelectionConditions.ConditionedField)
    (hempty : guardedFieldEntriesAtRuntimeType runtimeType entries = [])
    : guardedFieldExecutableFields variableValues executionParentType runtimeType
        responseName entries
      = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro field hfield
  rcases guardedFieldExecutableFields_origin variableValues executionParentType
      runtimeType responseName entries field hfield with
    ⟨entry, hentry, hallows, _hfield⟩
  have hpossible : runtimeType ∈ entry.condition.possibleTypes := by
    have hparts : entry.condition.possibleTypes.contains runtimeType = true
        ∧ SelectionConditions.booleanConditionAllows variableValues
          entry.condition.booleanCondition = true := by
      simpa [SelectionConditions.Condition.allows, Bool.and_eq_true] using hallows
    exact List.contains_iff_mem.mp hparts.1
  have hfiltered : entry ∈ guardedFieldEntriesAtRuntimeType runtimeType entries := by
    simp [guardedFieldEntriesAtRuntimeType, hentry, hpossible]
  rw [hempty] at hfiltered
  simp at hfiltered

theorem guardedFieldExecutableFields_runtime_entries (variableValues : VariableValues)
    (executionParentType runtimeType responseName : Name)
    (entries : List SelectionConditions.ConditionedField)
    : guardedFieldExecutableFields variableValues executionParentType runtimeType
        responseName entries
      = guardedFieldExecutableFields variableValues executionParentType runtimeType
          responseName (guardedFieldEntriesAtRuntimeType runtimeType entries) := by
  induction entries with
  | nil => simp [guardedFieldExecutableFields,
      guardedFieldEntriesAtRuntimeType]
  | cons entry rest ih =>
      rw [guardedFieldEntriesAtRuntimeType, List.filter_cons]
      by_cases hpossible : runtimeType ∈ entry.condition.possibleTypes
      · have hcontains : entry.condition.possibleTypes.contains runtimeType = true :=
          List.contains_iff_mem.mpr hpossible
        simp only [hcontains, if_true]
        change (if entry.condition.allows variableValues runtimeType then
                    [{
                      parentType := executionParentType
                      responseName
                      fieldName := entry.field.fieldName
                      arguments := entry.field.arguments
                      selectionSet := entry.field.selectionSet
                    }]
                  else
                    [])
                  ++ guardedFieldExecutableFields variableValues executionParentType
                      runtimeType responseName rest
                = (if entry.condition.allows variableValues runtimeType then
                      [{
                        parentType := executionParentType
                        responseName
                        fieldName := entry.field.fieldName
                        arguments := entry.field.arguments
                        selectionSet := entry.field.selectionSet
                      }]
                    else
                      [])
                  ++ guardedFieldExecutableFields variableValues executionParentType
                      runtimeType responseName
                      (guardedFieldEntriesAtRuntimeType runtimeType rest)
        rw [ih]
      · have hcontains : entry.condition.possibleTypes.contains runtimeType = false := by
          cases hvalue : entry.condition.possibleTypes.contains runtimeType with
          | false => rfl
          | true => exact False.elim (hpossible (List.contains_iff_mem.mp hvalue))
        have hinactive : entry.condition.allows variableValues runtimeType = false := by
          simp [Condition.allows, hpossible]
        simp only [hcontains, Bool.false_eq_true, if_false]
        rw [guardedFieldExecutableFields, List.flatMap_cons]
        simp only [hinactive]
        exact ih

theorem guardedScalarFieldIncludesAtRuntimeTypeBool_sound
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name) (variableValues : VariableValues)
    (runtimeType : Name) (left right : GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hcheck
      : guardedScalarFieldIncludesAtRuntimeTypeBool schema
          fixedExecutionParentType runtimeType left right
        = true)
    (hcomplete
      : boolVarsComplete (guardedFieldGroupBooleanVariables left right) variableValues)
    : guardedFieldGroupCaseIncludesBool schema (responseFuel + 1)
        fixedExecutionParentType variableValues runtimeType left right childIncludes
      = true := by
  let executionParentType := fixedExecutionParentType.getD runtimeType
  let leftEntries := guardedFieldEntriesAtRuntimeType runtimeType left.entries
  let rightEntries := guardedFieldEntriesAtRuntimeType runtimeType right.entries
  cases hrightEntries : rightEntries with
  | nil =>
      have hrightFields : guardedFieldExecutableFields variableValues
          executionParentType runtimeType right.responseName right.entries = [] :=
        guardedFieldExecutableFields_empty_of_no_runtime_entries variableValues
          executionParentType runtimeType right.responseName right.entries
          (by simpa [rightEntries] using hrightEntries)
      simp [guardedFieldGroupCaseIncludesBool, executionParentType, hrightFields,
        executableFieldsAsGroup, executableGroupsIncludeBool]
  | cons rightHead rightRest =>
      simp only [guardedScalarFieldIncludesAtRuntimeTypeBool, rightEntries,
        hrightEntries, Bool.and_eq_true] at hcheck
      have hresponseName := hcheck.1
      have hcheck := hcheck.2
      cases hdefinition
            : schema.lookupField executionParentType rightHead.field.fieldName with
      | none => simp [executionParentType, hdefinition] at hcheck
      | some definition =>
          simp only [executionParentType, hdefinition, Bool.and_eq_true] at hcheck
          have hcoverage := hcheck.2
          have hhead := hcheck.1
          have hrightCalls := hhead.2
          have hhead := hhead.1
          have hleftCalls := hhead.2
          have hleaf : definition.outputType.isCompositeBool schema = false := by
            simpa using hhead.1
          let leftFields := guardedFieldExecutableFields variableValues
            executionParentType runtimeType left.responseName left.entries
          let rightFields := guardedFieldExecutableFields variableValues
            executionParentType runtimeType right.responseName right.entries
          cases hrightFields : rightFields with
          | nil =>
              simp [guardedFieldGroupCaseIncludesBool, executionParentType,
                rightFields, hrightFields, executableFieldsAsGroup,
                executableGroupsIncludeBool]
          | cons rightField rightFieldsRest =>
              have hrightField : rightField ∈ guardedFieldExecutableFields
                  variableValues executionParentType runtimeType right.responseName
                  right.entries := by
                simp [rightFields, hrightFields]
              rcases guardedFieldExecutableFields_origin variableValues
                  executionParentType runtimeType right.responseName right.entries
                  rightField hrightField with
                ⟨rightEntry, hrightEntry, hrightAllows, hrightFieldEq⟩
              have hrightPossible : runtimeType ∈ rightEntry.condition.possibleTypes := by
                have hparts : rightEntry.condition.possibleTypes.contains runtimeType = true
                    ∧ booleanConditionAllows variableValues
                      rightEntry.condition.booleanCondition = true := by
                  simpa [Condition.allows, Bool.and_eq_true] using hrightAllows
                exact List.contains_iff_mem.mp hparts.1
              have hrightEntryAt : rightEntry ∈ rightEntries := by
                simp [rightEntries, guardedFieldEntriesAtRuntimeType,
                  hrightEntry, hrightPossible]
              have hrightBooleanAllows : booleanConditionAllows variableValues
                  rightEntry.condition.booleanCondition = true := by
                have hparts : rightEntry.condition.possibleTypes.contains runtimeType
                      = true
                    ∧ booleanConditionAllows variableValues
                      rightEntry.condition.booleanCondition = true := by
                  simpa [Condition.allows, Bool.and_eq_true] using hrightAllows
                exact hparts.2
              have hrightEntryAt' : rightEntry ∈ rightHead :: rightRest := by
                rw [← hrightEntries]
                exact hrightEntryAt
              have hentryCoverage := List.all_eq_true.mp hcoverage rightEntry
                hrightEntryAt'
              have hcoverComplete : boolVarsComplete
                  (SelectionConditions.booleanConditionsVariables
                    (leftEntries.map fun leftEntry =>
                      leftEntry.condition.booleanCondition)) variableValues := by
                intro variableName hvariable
                apply hcomplete variableName
                unfold SelectionConditions.booleanConditionsVariables at hvariable
                have hvariable := List.mem_eraseDups.mp hvariable
                rcases List.mem_flatMap.mp hvariable with
                  ⟨condition, hcondition, hvariable⟩
                rcases List.mem_map.mp hcondition with
                  ⟨leftEntry, hleftEntryAt, rfl⟩
                rcases List.mem_map.mp hvariable with
                  ⟨literal, hliteral, hname⟩
                rw [← hname]
                exact guardedFieldGroupBooleanVariables_mem_left left right
                  (List.mem_filter.mp hleftEntryAt).1 hliteral
              rcases SelectionConditions.booleanConditionCoveredByBool_sound
                  rightEntry.condition.booleanCondition
                  (leftEntries.map fun leftEntry =>
                    leftEntry.condition.booleanCondition)
                  hentryCoverage variableValues hcoverComplete hrightBooleanAllows with
                ⟨cover, hcover, hcoverAllows⟩
              rcases List.mem_map.mp hcover with
                ⟨leftEntry, hleftEntryAt, hleftCondition⟩
              subst cover
              have hleftEntry := (List.mem_filter.mp hleftEntryAt).1
              have hleftPossible := (List.mem_filter.mp hleftEntryAt).2
              have hleftPossible' : runtimeType ∈
                  leftEntry.condition.possibleTypes :=
                List.contains_iff_mem.mp hleftPossible
              have hleftAllows : leftEntry.condition.allows variableValues runtimeType
                  = true := by
                simp [Condition.allows, hleftPossible', hcoverAllows]
              let leftField : ExecutableField := {
                parentType := executionParentType
                responseName := left.responseName
                fieldName := leftEntry.field.fieldName
                arguments := leftEntry.field.arguments
                selectionSet := leftEntry.field.selectionSet
              }
              have hleftField : leftField ∈ guardedFieldExecutableFields
                  variableValues executionParentType runtimeType left.responseName
                  left.entries := by
                unfold guardedFieldExecutableFields
                apply List.mem_flatMap.mpr
                refine ⟨leftEntry, hleftEntry, ?_⟩
                simp [hleftAllows, leftField]
              cases hleftFields : leftFields with
              | nil =>
                  have : leftField ∈ leftFields := by
                    simpa [leftFields] using hleftField
                  simp [hleftFields] at this
              | cons leftFieldHead leftFieldsRest =>
                  have hleftFieldHead : leftFieldHead ∈
                      guardedFieldExecutableFields variableValues executionParentType
                        runtimeType left.responseName left.entries := by
                    simp [leftFields, hleftFields]
                  rcases guardedFieldExecutableFields_origin variableValues
                      executionParentType runtimeType left.responseName left.entries
                      leftFieldHead hleftFieldHead with
                    ⟨leftHeadEntry, hleftHeadEntry, hleftHeadAllows,
                      hleftFieldHeadEq⟩
                  have hleftHeadPossible : runtimeType ∈
                      leftHeadEntry.condition.possibleTypes := by
                    have hparts : leftHeadEntry.condition.possibleTypes.contains
                          runtimeType = true
                        ∧ booleanConditionAllows variableValues
                          leftHeadEntry.condition.booleanCondition = true := by
                      simpa [Condition.allows, Bool.and_eq_true] using hleftHeadAllows
                    exact List.contains_iff_mem.mp hparts.1
                  have hleftHeadAt : leftHeadEntry ∈ leftEntries := by
                    simp [leftEntries, guardedFieldEntriesAtRuntimeType,
                      hleftHeadEntry, hleftHeadPossible]
                  have hleftCall := List.all_eq_true.mp hleftCalls leftHeadEntry
                    hleftHeadAt
                  have hrightCall := List.all_eq_true.mp hrightCalls rightEntry
                    hrightEntryAt'
                  simp only [conditionedFieldResolverCallEqBool,
                    Bool.and_eq_true] at hleftCall hrightCall
                  have hfieldName : leftHeadEntry.field.fieldName
                      = rightEntry.field.fieldName :=
                    (beq_iff_eq.mp hleftCall.1).trans
                      (beq_iff_eq.mp hrightCall.1).symm
                  have hrightFieldName : rightEntry.field.fieldName
                      = rightHead.field.fieldName :=
                    beq_iff_eq.mp hrightCall.1
                  have harguments : Argument.argumentsEquivalent
                      leftHeadEntry.field.arguments rightEntry.field.arguments :=
                    argumentsEquivalent_trans
                      ((argumentsSyntacticallyEquivalentBool_iff _ _).mp
                        hleftCall.2)
                      (FieldMerge.argumentsEquivalent_symm
                        ((argumentsSyntacticallyEquivalentBool_iff _ _).mp
                          hrightCall.2))
                  have hargumentsBool :
                      Argument.argumentsSyntacticallyEquivalentBool
                        leftHeadEntry.field.arguments rightEntry.field.arguments = true :=
                    (argumentsSyntacticallyEquivalentBool_iff _ _).mpr harguments
                  subst rightField
                  subst leftFieldHead
                  simp [guardedFieldGroupCaseIncludesBool,
                    executionParentType, leftFields, rightFields, hleftFields,
                    hrightFields, executableFieldsAsGroup,
                    executableGroupsIncludeBool, executableGroupIncludedBool,
                    hresponseName, hfieldName, hrightFieldName, hargumentsBool,
                    hdefinition, hleaf]

theorem guardedCompositeFieldIncludesAtRuntimeTypeBool_sound
    (schema : Schema) (childFuel : Nat)
    (fixedExecutionParentType : Option Name) (variableValues : VariableValues)
    (runtimeType : Name) (left right : GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hcheck
      : guardedCompositeFieldIncludesAtRuntimeTypeBool schema childFuel
          fixedExecutionParentType runtimeType left right
        = true)
    (hcomplete
      : boolVarsComplete (guardedFieldGroupBooleanVariables left right) variableValues)
    (hchildSound
      : ∀ possibleTypes leftSelectionSet rightSelectionSet,
          guardedFieldChildIncludesBool schema childFuel variableValues
              possibleTypes leftSelectionSet rightSelectionSet
            = true
          -> childIncludes possibleTypes leftSelectionSet rightSelectionSet = true)
    : guardedFieldGroupCaseIncludesBool schema (childFuel + 1)
        fixedExecutionParentType variableValues runtimeType left right childIncludes
      = true := by
  let executionParentType := fixedExecutionParentType.getD runtimeType
  let leftEntries := guardedFieldEntriesAtRuntimeType runtimeType left.entries
  let rightEntries := guardedFieldEntriesAtRuntimeType runtimeType right.entries
  cases hrightEntries : rightEntries with
  | nil =>
      have hrightFields : guardedFieldExecutableFields variableValues
          executionParentType runtimeType right.responseName right.entries = [] :=
        guardedFieldExecutableFields_empty_of_no_runtime_entries variableValues
          executionParentType runtimeType right.responseName right.entries
          (by simpa [rightEntries] using hrightEntries)
      simp [guardedFieldGroupCaseIncludesBool, executionParentType, hrightFields,
        executableFieldsAsGroup, executableGroupsIncludeBool]
  | cons rightEntry rightRest =>
      cases rightRest with
      | cons next rest =>
          simp [guardedCompositeFieldIncludesAtRuntimeTypeBool, rightEntries,
            hrightEntries] at hcheck
      | nil =>
          cases hleftEntries : leftEntries with
          | nil =>
              simp [guardedCompositeFieldIncludesAtRuntimeTypeBool, leftEntries,
                rightEntries, hleftEntries, hrightEntries] at hcheck
          | cons leftEntry leftRest =>
              cases leftRest with
              | cons next rest =>
                  simp [guardedCompositeFieldIncludesAtRuntimeTypeBool, leftEntries,
                    rightEntries, hleftEntries, hrightEntries] at hcheck
              | nil =>
                  simp only [guardedCompositeFieldIncludesAtRuntimeTypeBool,
                    leftEntries, rightEntries, hleftEntries, hrightEntries,
                    Bool.and_eq_true] at hcheck
                  have hresponseName := hcheck.1
                  have hcheck := hcheck.2
                  cases hdefinition
                        : schema.lookupField executionParentType
                            rightEntry.field.fieldName with
                  | none => simp [executionParentType, hdefinition] at hcheck
                  | some definition =>
                      simp only [executionParentType, hdefinition,
                        Bool.and_eq_true] at hcheck
                      have hsyntax := hcheck.2.2
                      have hcomposite := hcheck.2.1
                      have hcoverage := hcheck.1.2
                      have hcall := hcheck.1.1
                      have hrightPossible : runtimeType ∈
                          rightEntry.condition.possibleTypes := by
                        have : rightEntry ∈ rightEntries := by
                          simp [rightEntries, hrightEntries]
                        exact List.contains_iff_mem.mp (List.mem_filter.mp this).2
                      have hleftPossible : runtimeType ∈
                          leftEntry.condition.possibleTypes := by
                        have : leftEntry ∈ leftEntries := by
                          simp [leftEntries, hleftEntries]
                        exact List.contains_iff_mem.mp (List.mem_filter.mp this).2
                      cases hrightAllows
                            : rightEntry.condition.allows variableValues runtimeType with
                      | false =>
                          have hrightFields : guardedFieldExecutableFields
                              variableValues executionParentType runtimeType
                              right.responseName right.entries = [] := by
                            rw [guardedFieldExecutableFields_runtime_entries]
                            simp [rightEntries, hrightEntries,
                              guardedFieldExecutableFields, hrightAllows]
                          simp [guardedFieldGroupCaseIncludesBool,
                            executionParentType, hrightFields, executableFieldsAsGroup,
                            executableGroupsIncludeBool]
                      | true =>
                          have hrightBooleanAllows : booleanConditionAllows variableValues
                              rightEntry.condition.booleanCondition = true := by
                            have hparts :
                                rightEntry.condition.possibleTypes.contains runtimeType
                                    = true
                                ∧ booleanConditionAllows variableValues
                                  rightEntry.condition.booleanCondition = true := by
                              simpa [Condition.allows, Bool.and_eq_true] using
                                hrightAllows
                            exact hparts.2
                          have hcoverComplete : boolVarsComplete
                              (SelectionConditions.booleanConditionsVariables
                                [leftEntry.condition.booleanCondition]) variableValues := by
                            intro variableName hvariable
                            apply hcomplete variableName
                            unfold SelectionConditions.booleanConditionsVariables
                              at hvariable
                            simp only [List.mem_eraseDups, List.flatMap_cons,
                              List.flatMap_nil, List.append_nil, List.mem_map]
                              at hvariable
                            rcases hvariable with ⟨literal, hliteral, hname⟩
                            rw [← hname]
                            exact guardedFieldGroupBooleanVariables_mem_left left right
                              (List.mem_filter.mp (by
                                show leftEntry ∈ leftEntries
                                simp [leftEntries, hleftEntries])).1 hliteral
                          rcases SelectionConditions.booleanConditionCoveredByBool_sound
                              rightEntry.condition.booleanCondition
                              [leftEntry.condition.booleanCondition] hcoverage
                              variableValues hcoverComplete hrightBooleanAllows with
                            ⟨cover, hcover, hcoverAllows⟩
                          have hleftBooleanAllows : booleanConditionAllows variableValues
                              leftEntry.condition.booleanCondition = true := by
                            have hcoverEq : cover
                                = leftEntry.condition.booleanCondition := by
                              simpa using hcover
                            rw [← hcoverEq]
                            exact hcoverAllows
                          have hleftAllows : leftEntry.condition.allows variableValues
                              runtimeType = true := by
                            simp [Condition.allows, hleftPossible,
                              hleftBooleanAllows]
                          have hleftFields : guardedFieldExecutableFields
                              variableValues executionParentType runtimeType
                              left.responseName left.entries =
                                [{
                                  parentType := executionParentType
                                  responseName := left.responseName
                                  fieldName := leftEntry.field.fieldName
                                  arguments := leftEntry.field.arguments
                                  selectionSet := leftEntry.field.selectionSet
                                }] := by
                            rw [guardedFieldExecutableFields_runtime_entries]
                            simp [leftEntries, hleftEntries,
                              guardedFieldExecutableFields, hleftAllows]
                          have hrightFields : guardedFieldExecutableFields
                              variableValues executionParentType runtimeType
                              right.responseName right.entries =
                                [{
                                  parentType := executionParentType
                                  responseName := right.responseName
                                  fieldName := rightEntry.field.fieldName
                                  arguments := rightEntry.field.arguments
                                  selectionSet := rightEntry.field.selectionSet
                                }] := by
                            rw [guardedFieldExecutableFields_runtime_entries]
                            simp [rightEntries, hrightEntries,
                              guardedFieldExecutableFields, hrightAllows]
                          have hchildCheck : childIncludes
                              (schema.getPossibleTypes definition.outputType.namedType)
                              leftEntry.field.selectionSet
                              rightEntry.field.selectionSet = true := by
                            apply hchildSound
                            simp [guardedFieldChildIncludesBool, hsyntax]
                          simp only [conditionedFieldResolverCallEqBool,
                            Bool.and_eq_true] at hcall
                          simp [guardedFieldGroupCaseIncludesBool,
                            executionParentType, hleftFields, hrightFields,
                            executableFieldsAsGroup, executableGroupsIncludeBool,
                            executableGroupIncludedBool, hresponseName, hcall.1,
                            hcall.2, hdefinition, hcomposite, hchildCheck]

theorem executableGroupIncludedBool_mono_child
    (schema : Schema)
    (sourceChildIncludes targetChildIncludes
      : TypeRef -> List Selection -> List Selection -> Bool)
    (hmono
      : ∀ outputType leftSelectionSet rightSelectionSet,
          sourceChildIncludes outputType leftSelectionSet rightSelectionSet = true
          -> targetChildIncludes outputType leftSelectionSet rightSelectionSet = true)
    (leftGroups : List (Name × List ExecutableField))
    (rightGroup : Name × List ExecutableField)
    (hcheck
      : executableGroupIncludedBool schema sourceChildIncludes leftGroups rightGroup
        = true)
    : executableGroupIncludedBool schema targetChildIncludes leftGroups rightGroup
      = true := by
  unfold executableGroupIncludedBool at hcheck ⊢
  rcases List.any_eq_true.mp hcheck with ⟨leftGroup, hleftGroup, hmatch⟩
  apply List.any_eq_true.mpr
  refine ⟨leftGroup, hleftGroup, ?_⟩
  rcases leftGroup with ⟨leftName, leftFields⟩
  rcases rightGroup with ⟨rightName, rightFields⟩
  simp only [Bool.and_eq_true] at hmatch ⊢
  refine ⟨hmatch.1, ?_⟩
  cases leftFields with
  | nil => simp at hmatch
  | cons leftField leftRest =>
      cases rightFields with
      | nil => simp at hmatch
      | cons rightField rightRest =>
          simp only [Bool.and_eq_true] at hmatch ⊢
          refine ⟨hmatch.2.1, ?_⟩
          cases hdefinition
                : schema.lookupField rightField.parentType rightField.fieldName with
          | none => simp [hdefinition] at hmatch
          | some definition =>
              cases hcomposite : definition.outputType.isCompositeBool schema with
              | false => simp [hcomposite]
              | true =>
                  simp only [hdefinition, hcomposite, if_true] at hmatch ⊢
                  exact hmono definition.outputType
                    (executableFieldsMergedSelectionSet (leftField :: leftRest))
                    (executableFieldsMergedSelectionSet (rightField :: rightRest))
                    hmatch.2.2

theorem executableGroupsIncludeBool_mono_child
    (schema : Schema)
    (sourceChildIncludes targetChildIncludes
      : TypeRef -> List Selection -> List Selection -> Bool)
    (hmono
      : ∀ outputType leftSelectionSet rightSelectionSet,
          sourceChildIncludes outputType leftSelectionSet rightSelectionSet = true
          -> targetChildIncludes outputType leftSelectionSet rightSelectionSet = true)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    (hcheck
      : executableGroupsIncludeBool schema sourceChildIncludes leftGroups rightGroups
        = true)
    : executableGroupsIncludeBool schema targetChildIncludes leftGroups rightGroups
      = true := by
  apply List.all_eq_true.mpr
  intro rightGroup hrightGroup
  exact executableGroupIncludedBool_mono_child schema sourceChildIncludes
    targetChildIncludes hmono leftGroups rightGroup
    (List.all_eq_true.mp hcheck rightGroup hrightGroup)

theorem executableFieldsAsGroup_keysNodup (responseName : Name)
    (fields : List ExecutableField)
    : ((executableFieldsAsGroup responseName fields).map Prod.fst).Nodup := by
  cases fields <;> simp [executableFieldsAsGroup]

theorem guardedFieldGroupIncludesWithFuel_sound
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (checkValues targetValues : VariableValues)
    (remainingBooleanVariables parentRegion : List Name)
    (left right : GuardedFieldGroup) (region : List Name) (runtimeType : Name)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hcheck
      : guardedFieldGroupIncludesWithFuel schema responseFuel
          fixedExecutionParentType checkValues remainingBooleanVariables left right
          (guardedFieldGroupTypeRegions parentRegion left right)
        = true)
    (hagrees : BooleanAssignmentsAgree checkValues targetValues)
    (hcovered
      : BooleanVariablesCovered checkValues remainingBooleanVariables
          (guardedFieldGroupBooleanVariables left right))
    (hremainingWithin
      : ∀ variableName,
          variableName ∈ remainingBooleanVariables
          -> variableName ∈ guardedFieldGroupBooleanVariables left right)
    (hcomplete
      : boolVarsComplete (guardedFieldGroupBooleanVariables left right) targetValues)
    (hchildSound
      : ∀ childFuel,
          responseFuel = childFuel + 1
          -> ∀ knownValues,
              BooleanAssignmentsAgree knownValues targetValues
              -> ∀ possibleTypes leftSelectionSet rightSelectionSet,
                  guardedFieldChildIncludesBool schema childFuel knownValues
                      possibleTypes leftSelectionSet rightSelectionSet
                    = true
                  -> childIncludes possibleTypes leftSelectionSet rightSelectionSet
                      = true)
    (hregion : region ∈ guardedFieldGroupTypeRegions parentRegion left right)
    (hruntime : runtimeType ∈ region)
    : guardedFieldGroupCaseIncludesBool schema responseFuel
        fixedExecutionParentType targetValues runtimeType left right childIncludes
      = true := by
  cases hremaining : remainingBooleanVariables with
  | cons variableName rest =>
      have hrestSmaller : rest.length < remainingBooleanVariables.length := by
        rw [hremaining]
        simp
      simp only [hremaining] at hcovered hremainingWithin
      rw [guardedFieldGroupIncludesWithFuel.eq_def] at hcheck
      simp only [hremaining] at hcheck
      cases hvalue : inputValueBoolean? checkValues (.variable variableName) with
      | none =>
          have htarget := hcomplete variableName
            (hremainingWithin variableName (by simp))
          rcases htarget with ⟨value, htarget⟩
          have hbranches :
              guardedFieldGroupIncludesWithFuel schema responseFuel
                    fixedExecutionParentType
                    ((variableName, .boolean false) :: checkValues) rest left right
                    (guardedFieldGroupTypeRegions parentRegion left right) = true
                ∧ guardedFieldGroupIncludesWithFuel schema responseFuel
                    fixedExecutionParentType
                    ((variableName, .boolean true) :: checkValues) rest left right
                    (guardedFieldGroupTypeRegions parentRegion left right) = true := by
            simpa [hvalue, Bool.and_eq_true] using hcheck
          cases value with
          | false =>
              exact guardedFieldGroupIncludesWithFuel_sound schema responseFuel
                fixedExecutionParentType
                ((variableName, .boolean false) :: checkValues) targetValues rest
                parentRegion left right region runtimeType childIncludes hbranches.1
                (booleanAssignmentsAgree_cons hagrees htarget)
                (booleanVariablesCovered_tail_of_cons hcovered)
                (by
                  intro candidate hcandidate
                  exact hremainingWithin candidate (by simp [hcandidate]))
                hcomplete hchildSound hregion hruntime
          | true =>
              exact guardedFieldGroupIncludesWithFuel_sound schema responseFuel
                fixedExecutionParentType
                ((variableName, .boolean true) :: checkValues) targetValues rest
                parentRegion left right region runtimeType childIncludes hbranches.2
                (booleanAssignmentsAgree_cons hagrees htarget)
                (booleanVariablesCovered_tail_of_cons hcovered)
                (by
                  intro candidate hcandidate
                  exact hremainingWithin candidate (by simp [hcandidate]))
                hcomplete hchildSound hregion hruntime
      | some value =>
          exact guardedFieldGroupIncludesWithFuel_sound schema responseFuel
            fixedExecutionParentType checkValues targetValues rest parentRegion left
            right region runtimeType childIncludes (by simpa [hvalue] using hcheck) hagrees
            (booleanVariablesCovered_tail_of_known hcovered ⟨value, hvalue⟩)
            (by
              intro candidate hcandidate
              exact hremainingWithin candidate (by simp [hcandidate]))
            hcomplete hchildSound hregion hruntime
  | nil =>
      simp only [hremaining] at hcovered hremainingWithin
      rw [guardedFieldGroupIncludesWithFuel.eq_def] at hcheck
      simp only [hremaining] at hcheck
      rw [guardedFieldGroupIncludesForRegionsWithFuel] at hcheck
      have hregionCheck := List.all_eq_true.mp hcheck region hregion
      cases region with
      | nil => simp at hruntime
      | cons representativeRuntimeType rest =>
          let representativeExecutionParentType :=
            fixedExecutionParentType.getD representativeRuntimeType
          let targetExecutionParentType := fixedExecutionParentType.getD runtimeType
          let baseLeftFields :=
            guardedFieldExecutableFields checkValues
              representativeExecutionParentType representativeRuntimeType
              left.responseName left.entries
          let baseRightFields :=
            guardedFieldExecutableFields checkValues
              representativeExecutionParentType representativeRuntimeType
              right.responseName right.entries
          let baseLeftGroups := executableFieldsAsGroup left.responseName baseLeftFields
          let baseRightGroups :=
            executableFieldsAsGroup right.responseName baseRightFields
          let targetLeftFields :=
            guardedFieldExecutableFields targetValues targetExecutionParentType
              runtimeType left.responseName left.entries
          let targetRightFields :=
            guardedFieldExecutableFields targetValues targetExecutionParentType
              runtimeType right.responseName right.entries
          let targetLeftGroups :=
            executableFieldsAsGroup left.responseName targetLeftFields
          let targetRightGroups :=
            executableFieldsAsGroup right.responseName targetRightFields
          have hvariableAgreement : ∀ variableName,
              variableName ∈ guardedFieldGroupBooleanVariables left right
              -> inputValueBoolean? checkValues (.variable variableName)
                  = inputValueBoolean? targetValues (.variable variableName) := by
            intro variableName hvariable
            rcases hcovered variableName hvariable with hremaining | hknown
            · simp at hremaining
            · rcases hknown with ⟨value, hvalue⟩
              exact hvalue.trans (hagrees variableName value hvalue).symm
          have hleftGroups : executableGroupsWithParentType targetExecutionParentType
                baseLeftGroups
              = targetLeftGroups := by
            rw [show baseLeftGroups = executableFieldsAsGroup left.responseName
                (guardedFieldExecutableFields checkValues
                  representativeExecutionParentType representativeRuntimeType
                  left.responseName left.entries) by rfl,
              executableFieldsAsGroup_withParentType representativeExecutionParentType
                targetExecutionParentType representativeRuntimeType left.responseName
                checkValues left.entries]
            unfold targetLeftGroups targetLeftFields
            rw [guardedFieldExecutableFields_eq_of_region_and_variables
              parentRegion left right left (Or.inl rfl) hregion (by simp) hruntime
              hvariableAgreement targetExecutionParentType]
          have hrightGroups : executableGroupsWithParentType targetExecutionParentType
                baseRightGroups
              = targetRightGroups := by
            rw [show baseRightGroups = executableFieldsAsGroup right.responseName
                (guardedFieldExecutableFields checkValues
                  representativeExecutionParentType representativeRuntimeType
                  right.responseName right.entries) by rfl,
              executableFieldsAsGroup_withParentType representativeExecutionParentType
                targetExecutionParentType representativeRuntimeType right.responseName
                checkValues right.entries]
            unfold targetRightGroups targetRightFields
            rw [guardedFieldExecutableFields_eq_of_region_and_variables
              parentRegion left right right (Or.inr rfl) hregion (by simp) hruntime
              hvariableAgreement targetExecutionParentType]
          cases responseFuel with
          | zero =>
              change baseRightFields.isEmpty = true at hregionCheck
              change targetRightFields.isEmpty = true
              cases hbase : baseRightFields with
              | nil =>
                  cases htarget : targetRightFields with
                  | nil => simp
                  | cons field fields =>
                      have hgroupEq := hrightGroups
                      unfold baseRightGroups targetRightGroups at hgroupEq
                      simp [executableGroupsWithParentType, executableFieldsAsGroup,
                        hbase, htarget] at hgroupEq
              | cons field fields => simp [hbase] at hregionCheck
          | succ responseFuel =>
              let parentTypes :=
                match fixedExecutionParentType with
                | some parentType => [parentType]
                | none => representativeRuntimeType :: rest
              change
                (match inclusionChildTasksForParentTypes? schema baseLeftGroups
                    baseRightGroups parentTypes with
                  | none => false
                  | some tasks => tasks.all fun task =>
                      guardedFieldChildIncludesBool schema responseFuel checkValues
                        task.possibleTypes task.leftSelectionSet
                        task.rightSelectionSet) = true at hregionCheck
              cases htasks
                    : inclusionChildTasksForParentTypes? schema baseLeftGroups
                        baseRightGroups parentTypes with
              | none => simp [htasks] at hregionCheck
              | some tasks =>
                  have htaskChecks : tasks.all fun task =>
                      guardedFieldChildIncludesBool schema responseFuel checkValues
                        task.possibleTypes task.leftSelectionSet
                        task.rightSelectionSet := by
                    simpa [htasks] using hregionCheck
                  have hparent : targetExecutionParentType ∈ parentTypes := by
                    cases fixedExecutionParentType with
                    | none =>
                        simpa [parentTypes, targetExecutionParentType] using hruntime
                    | some parentType => simp [parentTypes, targetExecutionParentType]
                  rcases inclusionChildTasksForParentTypes?_contains schema baseLeftGroups
                      baseRightGroups htasks hparent with
                    ⟨targetTasks, htargetTasks, htargetCovered⟩
                  have htargetChecks : targetTasks.all fun task =>
                      guardedFieldChildIncludesBool schema responseFuel checkValues
                        task.possibleTypes task.leftSelectionSet
                        task.rightSelectionSet := by
                    apply List.all_eq_true.mpr
                    intro task htask
                    exact List.all_eq_true.mp htaskChecks task
                      (htargetCovered task htask)
                  have hchildChecks : targetTasks.all fun task =>
                      childIncludes task.possibleTypes task.leftSelectionSet
                        task.rightSelectionSet := by
                    apply List.all_eq_true.mpr
                    intro task htask
                    exact hchildSound responseFuel rfl checkValues hagrees
                      task.possibleTypes task.leftSelectionSet task.rightSelectionSet
                      (List.all_eq_true.mp htargetChecks task htask)
                  have hinclude := inclusionChildTasks?_sound schema
                    childIncludes
                    (executableGroupsWithParentType targetExecutionParentType
                      baseLeftGroups)
                    (executableGroupsWithParentType targetExecutionParentType
                      baseRightGroups)
                    targetTasks htargetTasks hchildChecks
                  rw [hleftGroups, hrightGroups] at hinclude
                  exact hinclude
termination_by (responseFuel, remainingBooleanVariables.length)
decreasing_by
  all_goals simp_wf
  all_goals first | exact hrestSmaller | omega

set_option maxRecDepth 10000 in
theorem booleanAssignmentsAgree_cons_target_of_unknown
    {baseValues checkValues : VariableValues} {variableName : Name} {value : Bool}
    (hagrees : BooleanAssignmentsAgree baseValues checkValues)
    (hunknown : inputValueBoolean? checkValues (.variable variableName) = none)
    : BooleanAssignmentsAgree baseValues
        ((variableName, .boolean value) :: checkValues) := by
  intro candidate candidateValue hcandidate
  by_cases heq : variableName = candidate
  · subst candidate
    have hcontradiction := hagrees variableName candidateValue hcandidate
    rw [hunknown] at hcontradiction
    simp at hcontradiction
  · simpa [inputValueBoolean?, lookupVariableValue?, heq] using
      hagrees candidate candidateValue hcandidate

set_option maxRecDepth 10000 in
theorem guardedFieldGroupIncludesWithFuel_complete
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (baseValues checkValues : VariableValues)
    (remainingBooleanVariables parentRegion : List Name)
    (left right : GuardedFieldGroup)
    (availableBooleanVariables : List Name)
    (childIncludes
      : VariableValues -> List Name -> List Selection -> List Selection -> Bool)
    (hbaseAgrees : BooleanAssignmentsAgree baseValues checkValues)
    (hknown : KnownBooleanVariablesWithin checkValues availableBooleanVariables)
    (hcovered
      : BooleanVariablesCovered checkValues remainingBooleanVariables
          (guardedFieldGroupBooleanVariables left right))
    (hremainingWithin
      : ∀ variableName,
          variableName ∈ remainingBooleanVariables
          -> variableName ∈ guardedFieldGroupBooleanVariables left right)
    (hwithin
      : ∀ variableName,
          variableName ∈ guardedFieldGroupBooleanVariables left right
          -> variableName ∈ availableBooleanVariables)
    (hchildComplete
      : ∀ childFuel,
          responseFuel = childFuel + 1
          -> ∀ knownValues,
              KnownBooleanVariablesWithin knownValues availableBooleanVariables
              -> BooleanAssignmentsAgree baseValues knownValues
              -> ∀ possibleTypes leftSelectionSet rightSelectionSet,
                  childIncludes knownValues possibleTypes leftSelectionSet
                      rightSelectionSet
                    = true
                  -> guardedFieldChildIncludesBool schema childFuel knownValues
                        possibleTypes leftSelectionSet rightSelectionSet
                      = true)
    (hcases
      : ∀ knownValues,
          KnownBooleanVariablesWithin knownValues availableBooleanVariables
          -> BooleanAssignmentsAgree baseValues knownValues
          -> (∀ variableName,
                variableName ∈ guardedFieldGroupBooleanVariables left right
                -> ∃ value,
                    inputValueBoolean? knownValues (.variable variableName) = some value)
          -> ∀ targetValues,
              boolVarsComplete availableBooleanVariables targetValues
              -> BooleanAssignmentsAgree knownValues targetValues
              -> ∀ region,
                  region ∈ guardedFieldGroupTypeRegions parentRegion left right
                  -> ∀ runtimeType,
                      runtimeType ∈ region
                      -> guardedFieldGroupCaseIncludesBool schema responseFuel
                            fixedExecutionParentType targetValues runtimeType left right
                            (childIncludes knownValues)
                          = true)
    : guardedFieldGroupIncludesWithFuel schema responseFuel
        fixedExecutionParentType checkValues remainingBooleanVariables left right
        (guardedFieldGroupTypeRegions parentRegion left right)
      = true := by
  cases hremaining : remainingBooleanVariables with
  | cons variableName rest =>
      simp only [hremaining] at hcovered hremainingWithin
      have hrestSmaller : rest.length < remainingBooleanVariables.length := by
        rw [hremaining]
        simp
      have hvariableAvailable : variableName ∈ availableBooleanVariables :=
        hwithin variableName (hremainingWithin variableName (by simp))
      rw [guardedFieldGroupIncludesWithFuel.eq_def]
      simp only
      cases hvalue : inputValueBoolean? checkValues (.variable variableName) with
      | some value =>
          apply guardedFieldGroupIncludesWithFuel_complete schema responseFuel
            fixedExecutionParentType baseValues checkValues rest parentRegion left right
            availableBooleanVariables childIncludes hbaseAgrees hknown
          · exact booleanVariablesCovered_tail_of_known hcovered ⟨value, hvalue⟩
          · intro candidate hcandidate
            exact hremainingWithin candidate (by simp [hcandidate])
          · exact hwithin
          · exact hchildComplete
          · exact hcases
      | none =>
          simp only [Bool.and_eq_true]
          constructor
          · apply guardedFieldGroupIncludesWithFuel_complete schema responseFuel
              fixedExecutionParentType baseValues
              ((variableName, .boolean false) :: checkValues) rest parentRegion left
              right availableBooleanVariables childIncludes
            · exact booleanAssignmentsAgree_cons_target_of_unknown hbaseAgrees hvalue
            · exact knownBooleanVariablesWithin_cons hknown hvariableAvailable
            · exact booleanVariablesCovered_tail_of_cons hcovered
            · intro candidate hcandidate
              exact hremainingWithin candidate (by simp [hcandidate])
            · exact hwithin
            · exact hchildComplete
            · exact hcases
          · apply guardedFieldGroupIncludesWithFuel_complete schema responseFuel
              fixedExecutionParentType baseValues
              ((variableName, .boolean true) :: checkValues) rest parentRegion left
              right availableBooleanVariables childIncludes
            · exact booleanAssignmentsAgree_cons_target_of_unknown hbaseAgrees hvalue
            · exact knownBooleanVariablesWithin_cons hknown hvariableAvailable
            · exact booleanVariablesCovered_tail_of_cons hcovered
            · intro candidate hcandidate
              exact hremainingWithin candidate (by simp [hcandidate])
            · exact hwithin
            · exact hchildComplete
            · exact hcases
  | nil =>
      simp only [hremaining] at hcovered hremainingWithin
      rw [guardedFieldGroupIncludesWithFuel.eq_def]
      simp only
      rw [guardedFieldGroupIncludesForRegionsWithFuel]
      apply List.all_eq_true.mpr
      intro region hregion
      cases region with
      | nil => simp
      | cons representativeRuntimeType rest =>
          let targetValues :=
            representativeBooleanValues availableBooleanVariables checkValues
          have htargetComplete : boolVarsComplete availableBooleanVariables
              targetValues := representativeBooleanValues_complete _ _
          have htargetAgrees : BooleanAssignmentsAgree checkValues targetValues :=
            representativeBooleanValues_agree hknown
          have hcase := hcases checkValues hknown hbaseAgrees (by
            intro variableName hvariable
            rcases hcovered variableName hvariable with hremaining | hvalue
            · simp at hremaining
            · exact hvalue) targetValues
            htargetComplete htargetAgrees
          let representativeExecutionParentType :=
            fixedExecutionParentType.getD representativeRuntimeType
          let baseLeftFields :=
            guardedFieldExecutableFields checkValues
              representativeExecutionParentType representativeRuntimeType
              left.responseName left.entries
          let baseRightFields :=
            guardedFieldExecutableFields checkValues
              representativeExecutionParentType representativeRuntimeType
              right.responseName right.entries
          let baseLeftGroups := executableFieldsAsGroup left.responseName baseLeftFields
          let baseRightGroups :=
            executableFieldsAsGroup right.responseName baseRightFields
          let parentTypes :=
            match fixedExecutionParentType with
            | some parentType => [parentType]
            | none => representativeRuntimeType :: rest
          have hvariableAgreement : ∀ variableName,
              variableName ∈ guardedFieldGroupBooleanVariables left right
              -> inputValueBoolean? checkValues (.variable variableName)
                  = inputValueBoolean? targetValues (.variable variableName) := by
            intro variableName hvariable
            rcases hcovered variableName hvariable with hremaining | hknownValue
            · simp at hremaining
            · rcases hknownValue with ⟨value, hvalue⟩
              exact hvalue.trans (htargetAgrees variableName value hvalue).symm
          cases responseFuel with
          | zero =>
              change baseRightFields.isEmpty = true
              have hrepresentative := hcase (representativeRuntimeType :: rest)
                hregion representativeRuntimeType (by simp)
              change
                (guardedFieldExecutableFields targetValues
                  representativeExecutionParentType representativeRuntimeType
                  right.responseName right.entries).isEmpty = true
                at hrepresentative
              have hfields :=
                guardedFieldExecutableFields_eq_of_region_and_variables
                  parentRegion left right right (Or.inr rfl) hregion
                  (leftRuntimeType := representativeRuntimeType)
                  (rightRuntimeType := representativeRuntimeType)
                  (by simp) (by simp) hvariableAgreement
                  representativeExecutionParentType
              rw [← hfields] at hrepresentative
              exact hrepresentative
          | succ responseFuel =>
              change (match inclusionChildTasksForParentTypes? schema baseLeftGroups
                              baseRightGroups parentTypes with
                      | none => false
                      | some tasks =>
                          tasks.all
                            fun task =>
                              guardedFieldChildIncludesBool schema responseFuel
                                checkValues task.possibleTypes task.leftSelectionSet
                                task.rightSelectionSet)
                      = true
              have hnodup : ∀ parentType,
                  parentType ∈ parentTypes
                  -> ((executableGroupsWithParentType parentType baseLeftGroups).map
                      Prod.fst).Nodup := by
                intro parentType _hparent
                unfold baseLeftGroups
                rw [executableFieldsAsGroup_withParentType
                  representativeExecutionParentType parentType representativeRuntimeType
                  left.responseName checkValues left.entries]
                exact executableFieldsAsGroup_keysNodup _ _
              have hinclude : ∀ parentType,
                  parentType ∈ parentTypes
                  -> executableGroupsIncludeBool schema
                      (fun outputType leftSelectionSet rightSelectionSet =>
                        guardedFieldChildIncludesBool schema responseFuel checkValues
                          (schema.getPossibleTypes outputType.namedType)
                          leftSelectionSet rightSelectionSet)
                      (executableGroupsWithParentType parentType baseLeftGroups)
                      (executableGroupsWithParentType parentType baseRightGroups)
                    = true := by
                intro parentType hparent
                obtain ⟨runtimeType, hruntime, hexecutionParent⟩ :
                    ∃ runtimeType,
                      runtimeType ∈ representativeRuntimeType :: rest
                      ∧ fixedExecutionParentType.getD runtimeType = parentType := by
                  cases fixedExecutionParentType with
                  | none => exact ⟨parentType, hparent, rfl⟩
                  | some fixedParentType =>
                      have heq : parentType = fixedParentType := by
                        simpa [parentTypes] using hparent
                      subst parentType
                      exact ⟨representativeRuntimeType, by simp, rfl⟩
                have htargetCase := hcase (representativeRuntimeType :: rest) hregion
                  runtimeType hruntime
                let targetLeftFields :=
                  guardedFieldExecutableFields targetValues parentType runtimeType
                    left.responseName left.entries
                let targetRightFields :=
                  guardedFieldExecutableFields targetValues parentType runtimeType
                    right.responseName right.entries
                let targetLeftGroups :=
                  executableFieldsAsGroup left.responseName targetLeftFields
                let targetRightGroups :=
                  executableFieldsAsGroup right.responseName targetRightFields
                have hleftGroups : executableGroupsWithParentType parentType
                      baseLeftGroups
                    = targetLeftGroups := by
                  rw [show baseLeftGroups = executableFieldsAsGroup left.responseName
                      (guardedFieldExecutableFields checkValues
                        representativeExecutionParentType representativeRuntimeType
                        left.responseName left.entries) by rfl,
                    executableFieldsAsGroup_withParentType
                      representativeExecutionParentType parentType
                      representativeRuntimeType left.responseName checkValues left.entries]
                  unfold targetLeftGroups targetLeftFields
                  rw [guardedFieldExecutableFields_eq_of_region_and_variables
                    parentRegion left right left (Or.inl rfl) hregion (by simp) hruntime
                    hvariableAgreement parentType]
                have hrightGroups : executableGroupsWithParentType parentType
                      baseRightGroups
                    = targetRightGroups := by
                  rw [show baseRightGroups = executableFieldsAsGroup right.responseName
                      (guardedFieldExecutableFields checkValues
                        representativeExecutionParentType representativeRuntimeType
                        right.responseName right.entries) by rfl,
                    executableFieldsAsGroup_withParentType
                      representativeExecutionParentType parentType
                      representativeRuntimeType right.responseName checkValues
                      right.entries]
                  unfold targetRightGroups targetRightFields
                  rw [guardedFieldExecutableFields_eq_of_region_and_variables
                    parentRegion left right right (Or.inr rfl) hregion (by simp) hruntime
                    hvariableAgreement parentType]
                simp only [guardedFieldGroupCaseIncludesBool] at htargetCase
                rw [hexecutionParent] at htargetCase
                change executableGroupsIncludeBool schema
                  (fun outputType leftSelectionSet rightSelectionSet =>
                    childIncludes checkValues
                      (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                      rightSelectionSet)
                  targetLeftGroups targetRightGroups = true at htargetCase
                have hconverted := executableGroupsIncludeBool_mono_child schema
                  (fun outputType leftSelectionSet rightSelectionSet =>
                    childIncludes checkValues
                      (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                      rightSelectionSet)
                  (fun outputType leftSelectionSet rightSelectionSet =>
                    guardedFieldChildIncludesBool schema responseFuel checkValues
                      (schema.getPossibleTypes outputType.namedType)
                      leftSelectionSet rightSelectionSet)
                  (by
                    intro outputType leftSelectionSet rightSelectionSet hchild
                    exact hchildComplete responseFuel rfl checkValues hknown hbaseAgrees
                      (schema.getPossibleTypes outputType.namedType) leftSelectionSet
                      rightSelectionSet hchild)
                  targetLeftGroups targetRightGroups htargetCase
                rw [hleftGroups, hrightGroups]
                exact hconverted
              rcases inclusionChildTasksForParentTypes?_exists_of_include schema
                  (fun possibleTypes leftSelectionSet rightSelectionSet =>
                    guardedFieldChildIncludesBool schema responseFuel checkValues
                      possibleTypes leftSelectionSet rightSelectionSet)
                  baseLeftGroups baseRightGroups parentTypes hnodup hinclude with
                ⟨tasks, htasks, hchildren⟩
              simp [htasks, hchildren]
termination_by (responseFuel, remainingBooleanVariables.length)
decreasing_by
  all_goals simp_wf
  all_goals first | exact hrestSmaller | omega

def guardedFieldGroupFor (leftGroups : List GuardedFieldGroup) (right : GuardedFieldGroup)
    : GuardedFieldGroup :=
  (findGuardedFieldGroup? right.responseName leftGroups).getD
    { responseName := right.responseName, entries := [] }

def guardedFieldParentRegion (schema : Schema)
    (fixedExecutionParentType : Option Name)
    (left right : GuardedFieldGroup)
    : List Name :=
  match fixedExecutionParentType with
  | some parentType => schema.getPossibleTypes parentType
  | none =>
      (guardedFieldGroupConditions left ++ guardedFieldGroupConditions right)
      |>.flatMap SelectionConditions.Condition.possibleTypes
      |>.eraseDups

theorem guardedFieldGroupFor_booleanVariablesWithin
    (schema : Schema) (region : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (leftGroups : List GuardedFieldGroup)
    (hleftGroups
      : leftGroups
        = guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region leftSelectionSet))
    (right : GuardedFieldGroup)
    (hright
      : right
        ∈ guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region rightSelectionSet))
    {variableName : Name}
    (hvariable
      : variableName
        ∈ guardedFieldGroupBooleanVariables (guardedFieldGroupFor leftGroups right) right)
    : variableName ∈ SelectionConditions.selectionSetBooleanVariables leftSelectionSet
      ∨ variableName
        ∈ SelectionConditions.selectionSetBooleanVariables rightSelectionSet := by
  unfold guardedFieldGroupBooleanVariables at hvariable
  have hflat := List.mem_eraseDups.mp hvariable
  rcases List.mem_flatMap.mp hflat with ⟨entry, hentry, hliteral⟩
  rcases List.mem_append.mp hentry with hleft | hrightEntry
  · apply Or.inl
    cases hfind : findGuardedFieldGroup? right.responseName leftGroups with
    | none =>
        unfold guardedFieldGroupFor at hleft
        simp [hfind] at hleft
    | some left =>
        have hmember := (findGuardedFieldGroup?_some_mem hfind).1
        rw [hleftGroups] at hmember
        apply guardedFieldGroupBooleanVariablesWithinSelectionSet schema region
          leftSelectionSet
          left hmember
        apply List.mem_flatMap.mpr
        unfold guardedFieldGroupFor at hleft
        simp only [hfind, Option.getD_some] at hleft
        exact ⟨entry, hleft, hliteral⟩
  · apply Or.inr
    apply guardedFieldGroupBooleanVariablesWithinSelectionSet schema region
      rightSelectionSet
      right hright
    exact List.mem_flatMap.mpr ⟨entry, hrightEntry, hliteral⟩

theorem guardedFieldGroupFor_parentRegion_subset
    (schema : Schema) (region : List Name)
    (leftSelectionSet rightSelectionSet : List Selection)
    (leftGroups : List GuardedFieldGroup)
    (hleftGroups
      : leftGroups
        = guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region leftSelectionSet))
    (right : GuardedFieldGroup)
    (hright
      : right
        ∈ guardedFieldGroups
            (SelectionConditions.ofTypeRegion schema region rightSelectionSet))
    {runtimeType : Name}
    (hruntime
      : runtimeType
        ∈ guardedFieldParentRegion schema none
            (guardedFieldGroupFor leftGroups right) right)
    : runtimeType ∈ region := by
  unfold guardedFieldParentRegion at hruntime
  have hflat := List.mem_eraseDups.mp hruntime
  rcases List.mem_flatMap.mp hflat with ⟨condition, hcondition, hpossible⟩
  rcases List.mem_append.mp hcondition with hleft | hrightCondition
  · unfold guardedFieldGroupConditions at hleft
    rcases List.mem_map.mp hleft with ⟨entry, hentry, heq⟩
    subst condition
    cases hfind : findGuardedFieldGroup? right.responseName leftGroups with
    | none =>
        unfold guardedFieldGroupFor at hentry
        simp [hfind] at hentry
    | some left =>
        have hmember := (findGuardedFieldGroup?_some_mem hfind).1
        rw [hleftGroups] at hmember
        apply guardedFieldGroupPossibleTypesWithin schema region leftSelectionSet
          left hmember entry
        · unfold guardedFieldGroupFor at hentry
          simpa [hfind] using hentry
        · exact hpossible
  · unfold guardedFieldGroupConditions at hrightCondition
    rcases List.mem_map.mp hrightCondition with ⟨entry, hentry, heq⟩
    subst condition
    exact guardedFieldGroupPossibleTypesWithin schema region rightSelectionSet
      right hright entry hentry hpossible

theorem executableGroupIncludedBool_mono_left
    (schema : Schema)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (sourceLeftGroups targetLeftGroups : List (Name × List ExecutableField))
    (rightGroup : Name × List ExecutableField)
    (hsubset : ∀ group, group ∈ sourceLeftGroups -> group ∈ targetLeftGroups)
    (hcheck
      : executableGroupIncludedBool schema childIncludes sourceLeftGroups rightGroup
        = true)
    : executableGroupIncludedBool schema childIncludes targetLeftGroups rightGroup
      = true := by
  unfold executableGroupIncludedBool at hcheck ⊢
  rcases List.any_eq_true.mp hcheck with ⟨leftGroup, hleftGroup, hmatch⟩
  exact List.any_eq_true.mpr ⟨leftGroup, hsubset leftGroup hleftGroup, hmatch⟩

theorem guardedFieldGroupFor_runtimeGroups_subset
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (leftGroups : List GuardedFieldGroup) (right : GuardedFieldGroup)
    : ∀ group,
        group
          ∈ executableFieldsAsGroup
              (guardedFieldGroupFor leftGroups right).responseName
              (guardedFieldExecutableFields variableValues executionParentType
                runtimeType (guardedFieldGroupFor leftGroups right).responseName
                (guardedFieldGroupFor leftGroups right).entries)
        -> group
            ∈ guardedFieldRuntimeGroups variableValues executionParentType
                runtimeType leftGroups := by
  intro group hgroup
  unfold guardedFieldGroupFor at hgroup
  cases hfind : findGuardedFieldGroup? right.responseName leftGroups with
  | none =>
      simp [hfind, guardedFieldExecutableFields, executableFieldsAsGroup] at hgroup
  | some left =>
      have hleft := (findGuardedFieldGroup?_some_mem hfind).1
      apply List.mem_flatMap.mpr
      refine ⟨left, hleft, ?_⟩
      simpa [hfind] using hgroup

theorem guardedFieldGroupFor_runtimeGroup_mem
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (leftGroups : List GuardedFieldGroup) (right : GuardedFieldGroup)
    (hnodup : (leftGroups.map GuardedFieldGroup.responseName).Nodup)
    (group : Name × List ExecutableField)
    (hgroup
      : group
        ∈ guardedFieldRuntimeGroups variableValues executionParentType
            runtimeType leftGroups)
    (hname : group.1 = right.responseName)
    : group
      ∈ executableFieldsAsGroup
          (guardedFieldGroupFor leftGroups right).responseName
          (guardedFieldExecutableFields variableValues executionParentType
            runtimeType (guardedFieldGroupFor leftGroups right).responseName
            (guardedFieldGroupFor leftGroups right).entries) := by
  rcases List.mem_flatMap.mp hgroup with ⟨left, hleft, hlocal⟩
  cases hfields
        : guardedFieldExecutableFields variableValues executionParentType
            runtimeType left.responseName left.entries with
  | nil => simp [executableFieldsAsGroup, hfields] at hlocal
  | cons field rest =>
      have hlocalEq : group = (left.responseName, field :: rest) := by
        simpa [executableFieldsAsGroup, hfields] using hlocal
      subst group
      have hfind := findGuardedFieldGroup?_eq_some_of_mem_of_nodup hnodup hleft
      unfold guardedFieldGroupFor
      rw [← hname, hfind]
      simp [executableFieldsAsGroup, hfields]

theorem executableGroupIncludedBool_restrict_left
    (schema : Schema)
    (childIncludes : TypeRef -> List Selection -> List Selection -> Bool)
    (sourceLeftGroups targetLeftGroups : List (Name × List ExecutableField))
    (rightGroup : Name × List ExecutableField)
    (hmatching
      : ∀ leftGroup,
          leftGroup ∈ sourceLeftGroups
          -> leftGroup.1 = rightGroup.1
          -> leftGroup ∈ targetLeftGroups)
    (hcheck
      : executableGroupIncludedBool schema childIncludes sourceLeftGroups rightGroup
        = true)
    : executableGroupIncludedBool schema childIncludes targetLeftGroups rightGroup
      = true := by
  unfold executableGroupIncludedBool at hcheck ⊢
  rcases List.any_eq_true.mp hcheck with ⟨leftGroup, hleftGroup, hmatch⟩
  have hname : leftGroup.1 = rightGroup.1 := by
    rcases leftGroup with ⟨leftName, leftFields⟩
    rcases rightGroup with ⟨rightName, rightFields⟩
    simp only [Bool.and_eq_true] at hmatch
    exact beq_iff_eq.mp hmatch.1
  exact List.any_eq_true.mpr
    ⟨leftGroup, hmatching leftGroup hleftGroup hname, hmatch⟩

theorem guardedFieldRuntimeGroup_component_mem
    (variableValues : VariableValues) (executionParentType runtimeType : Name)
    (groups : List GuardedFieldGroup) (guardedGroup : GuardedFieldGroup)
    (hguardedGroup : guardedGroup ∈ groups)
    : ∀ group,
        group
          ∈ executableFieldsAsGroup guardedGroup.responseName
              (guardedFieldExecutableFields variableValues executionParentType
                runtimeType guardedGroup.responseName guardedGroup.entries)
        -> group
            ∈ guardedFieldRuntimeGroups variableValues executionParentType
                runtimeType groups := by
  intro group hgroup
  apply List.mem_flatMap.mpr
  exact ⟨guardedGroup, hguardedGroup, hgroup⟩

def guardedFieldRuntimeGroupsIncludeBool
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (variableValues : VariableValues) (runtimeType : Name)
    (leftGroups rightGroups : List GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    : Bool :=
  let executionParentType := fixedExecutionParentType.getD runtimeType
  let leftRuntimeGroups :=
    guardedFieldRuntimeGroups variableValues executionParentType runtimeType leftGroups
  let rightRuntimeGroups :=
    guardedFieldRuntimeGroups variableValues executionParentType runtimeType rightGroups
  match responseFuel with
  | 0 => rightRuntimeGroups.isEmpty
  | _responseFuel + 1 =>
      executableGroupsIncludeBool schema
        (fun outputType leftSelectionSet rightSelectionSet =>
          childIncludes (schema.getPossibleTypes outputType.namedType)
            leftSelectionSet rightSelectionSet)
        leftRuntimeGroups rightRuntimeGroups

theorem guardedFieldGroupCases_sound_runtime
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (variableValues : VariableValues) (runtimeType : Name)
    (leftGroups rightGroups : List GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hcases
      : ∀ right,
          right ∈ rightGroups
          -> guardedFieldGroupCaseIncludesBool schema responseFuel
                fixedExecutionParentType variableValues runtimeType
                (guardedFieldGroupFor leftGroups right) right childIncludes
              = true)
    : guardedFieldRuntimeGroupsIncludeBool schema responseFuel
        fixedExecutionParentType variableValues runtimeType leftGroups rightGroups
        childIncludes
      = true := by
  cases responseFuel with
  | zero =>
      unfold guardedFieldRuntimeGroupsIncludeBool
      have hempty : guardedFieldRuntimeGroups variableValues
          (fixedExecutionParentType.getD runtimeType) runtimeType rightGroups = [] := by
        unfold guardedFieldRuntimeGroups
        apply List.flatMap_eq_nil_iff.mpr
        intro right hright
        have hcase := hcases right hright
        unfold guardedFieldGroupCaseIncludesBool at hcase
        cases hfields
              : guardedFieldExecutableFields variableValues
                  (fixedExecutionParentType.getD runtimeType) runtimeType
                  right.responseName right.entries with
        | nil => simp [executableFieldsAsGroup]
        | cons field rest => simp [hfields] at hcase
      simp [hempty]
  | succ responseFuel =>
      unfold guardedFieldRuntimeGroupsIncludeBool
      apply List.all_eq_true.mpr
      intro rightRuntimeGroup hrightRuntimeGroup
      rcases List.mem_flatMap.mp hrightRuntimeGroup with
        ⟨right, hright, hrightLocal⟩
      have hcase := hcases right hright
      unfold guardedFieldGroupCaseIncludesBool at hcase
      simp only at hcase
      have hlocalIncluded := List.all_eq_true.mp hcase rightRuntimeGroup hrightLocal
      exact executableGroupIncludedBool_mono_left schema
        (fun outputType leftSelectionSet rightSelectionSet =>
          childIncludes (schema.getPossibleTypes outputType.namedType)
            leftSelectionSet rightSelectionSet)
        (executableFieldsAsGroup
          (guardedFieldGroupFor leftGroups right).responseName
          (guardedFieldExecutableFields variableValues
            (fixedExecutionParentType.getD runtimeType) runtimeType
            (guardedFieldGroupFor leftGroups right).responseName
            (guardedFieldGroupFor leftGroups right).entries))
        (guardedFieldRuntimeGroups variableValues
          (fixedExecutionParentType.getD runtimeType) runtimeType leftGroups)
        rightRuntimeGroup
        (guardedFieldGroupFor_runtimeGroups_subset variableValues
          (fixedExecutionParentType.getD runtimeType) runtimeType leftGroups right)
        hlocalIncluded

theorem guardedFieldGroupCases_complete_runtime
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (variableValues : VariableValues) (runtimeType : Name)
    (leftGroups rightGroups : List GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hleftNodup : (leftGroups.map GuardedFieldGroup.responseName).Nodup)
    (hinclude
      : guardedFieldRuntimeGroupsIncludeBool schema responseFuel
          fixedExecutionParentType variableValues runtimeType leftGroups rightGroups
          childIncludes
        = true)
    : ∀ right,
        right ∈ rightGroups
        -> guardedFieldGroupCaseIncludesBool schema responseFuel
              fixedExecutionParentType variableValues runtimeType
              (guardedFieldGroupFor leftGroups right) right childIncludes
            = true := by
  intro right hright
  cases responseFuel with
  | zero =>
      unfold guardedFieldRuntimeGroupsIncludeBool at hinclude
      unfold guardedFieldGroupCaseIncludesBool
      cases hfields
            : guardedFieldExecutableFields variableValues
                (fixedExecutionParentType.getD runtimeType) runtimeType
                right.responseName right.entries with
      | nil => simp [hfields]
      | cons head rest =>
          have hcomponent : (right.responseName, head :: rest)
              ∈ guardedFieldRuntimeGroups variableValues
                (fixedExecutionParentType.getD runtimeType) runtimeType
                rightGroups := by
            apply guardedFieldRuntimeGroup_component_mem variableValues
              (fixedExecutionParentType.getD runtimeType) runtimeType rightGroups
              right hright
            simp [executableFieldsAsGroup, hfields]
          have hempty : guardedFieldRuntimeGroups variableValues
              (fixedExecutionParentType.getD runtimeType) runtimeType rightGroups
              = [] := by
            cases hgroups
                  : guardedFieldRuntimeGroups variableValues
                      (fixedExecutionParentType.getD runtimeType) runtimeType
                      rightGroups with
            | nil => rfl
            | cons group groups => simp [hgroups] at hinclude
          rw [hempty] at hcomponent
          simp at hcomponent
  | succ responseFuel =>
      unfold guardedFieldRuntimeGroupsIncludeBool at hinclude
      unfold guardedFieldGroupCaseIncludesBool
      simp only
      apply List.all_eq_true.mpr
      intro rightRuntimeGroup hrightLocal
      have hrightRuntime := guardedFieldRuntimeGroup_component_mem variableValues
        (fixedExecutionParentType.getD runtimeType) runtimeType rightGroups right
        hright rightRuntimeGroup hrightLocal
      have hfullIncluded := List.all_eq_true.mp hinclude rightRuntimeGroup hrightRuntime
      have hrightName : rightRuntimeGroup.1 = right.responseName := by
        cases hfields
              : guardedFieldExecutableFields variableValues
                  (fixedExecutionParentType.getD runtimeType) runtimeType
                  right.responseName right.entries with
        | nil => simp [executableFieldsAsGroup, hfields] at hrightLocal
        | cons field rest =>
            simp [executableFieldsAsGroup, hfields] at hrightLocal
            subst rightRuntimeGroup
            rfl
      exact executableGroupIncludedBool_restrict_left schema
        (fun outputType leftSelectionSet rightSelectionSet =>
          childIncludes (schema.getPossibleTypes outputType.namedType)
            leftSelectionSet rightSelectionSet)
        (guardedFieldRuntimeGroups variableValues
          (fixedExecutionParentType.getD runtimeType) runtimeType leftGroups)
        (executableFieldsAsGroup
          (guardedFieldGroupFor leftGroups right).responseName
          (guardedFieldExecutableFields variableValues
            (fixedExecutionParentType.getD runtimeType) runtimeType
            (guardedFieldGroupFor leftGroups right).responseName
            (guardedFieldGroupFor leftGroups right).entries))
        rightRuntimeGroup
        (by
          intro leftRuntimeGroup hleftRuntime hname
          exact guardedFieldGroupFor_runtimeGroup_mem variableValues
            (fixedExecutionParentType.getD runtimeType) runtimeType leftGroups right
            hleftNodup leftRuntimeGroup hleftRuntime (hname.trans hrightName))
        hfullIncluded

theorem guardedFieldGroupCase_of_region_cases
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (variableValues : VariableValues) (runtimeType : Name)
    (left right : GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hfixedRuntime
      : ∀ parentType,
          fixedExecutionParentType = some parentType
          -> runtimeType ∈ schema.getPossibleTypes parentType)
    (hcases
      : ∀ region,
          region
            ∈ guardedFieldGroupTypeRegions
                (guardedFieldParentRegion schema fixedExecutionParentType left right)
                left right
          -> ∀ candidate,
              candidate ∈ region
              -> guardedFieldGroupCaseIncludesBool schema responseFuel
                    fixedExecutionParentType variableValues candidate left right
                    childIncludes
                  = true)
    : guardedFieldGroupCaseIncludesBool schema responseFuel
        fixedExecutionParentType variableValues runtimeType left right childIncludes
      = true := by
  let executionParentType := fixedExecutionParentType.getD runtimeType
  cases hrightFields
        : guardedFieldExecutableFields variableValues
            executionParentType runtimeType right.responseName right.entries with
  | nil =>
      cases responseFuel with
      | zero =>
          simp [guardedFieldGroupCaseIncludesBool, executionParentType,
            hrightFields]
      | succ responseFuel =>
          simp [guardedFieldGroupCaseIncludesBool, executionParentType,
            hrightFields, executableFieldsAsGroup, executableGroupsIncludeBool]
  | cons field rest =>
      have hparent : runtimeType ∈
          guardedFieldParentRegion schema fixedExecutionParentType left right := by
        cases hfixed : fixedExecutionParentType with
        | some parentType =>
            simpa [guardedFieldParentRegion, hfixed] using
              hfixedRuntime parentType hfixed
        | none =>
            have hfield : field ∈ guardedFieldExecutableFields variableValues
                executionParentType runtimeType right.responseName right.entries := by
              simp [hrightFields]
            unfold guardedFieldExecutableFields at hfield
            rcases List.mem_flatMap.mp hfield with ⟨entry, hentry, hactive⟩
            split at hactive
            · rename_i hallows
              have hpossible : runtimeType ∈ entry.condition.possibleTypes := by
                have hparts : entry.condition.possibleTypes.contains runtimeType = true
                    ∧ SelectionConditions.booleanConditionAllows variableValues
                      entry.condition.booleanCondition = true := by
                  simpa [SelectionConditions.Condition.allows, Bool.and_eq_true] using hallows
                exact List.contains_iff_mem.mp hparts.1
              unfold guardedFieldParentRegion
              apply List.mem_eraseDups.mpr
              apply List.mem_flatMap.mpr
              refine ⟨entry.condition, ?_, hpossible⟩
              exact List.mem_append.mpr
                (Or.inr (List.mem_map.mpr ⟨entry, hentry, rfl⟩))
            · simp at hactive
      rcases guardedFieldGroupTypeRegions_cover
          (guardedFieldParentRegion schema fixedExecutionParentType left right)
          left right hparent with ⟨region, hregion, hruntime⟩
      exact hcases region hregion runtimeType hruntime

theorem guardedFieldGroupsIncludeWithFuel_sound_cases
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (checkValues targetValues : VariableValues)
    (leftGroups rightGroups : List GuardedFieldGroup)
    (childIncludes : List Name -> List Selection -> List Selection -> Bool)
    (hcheck
      : guardedFieldGroupsIncludeWithFuel schema responseFuel
          fixedExecutionParentType checkValues leftGroups rightGroups
        = true)
    (hagrees : BooleanAssignmentsAgree checkValues targetValues)
    (hcomplete
      : ∀ right,
          right ∈ rightGroups
          -> boolVarsComplete
              (guardedFieldGroupBooleanVariables
                (guardedFieldGroupFor leftGroups right) right)
              targetValues)
    (hchildSound
      : ∀ childFuel,
          responseFuel = childFuel + 1
          -> ∀ knownValues,
              BooleanAssignmentsAgree knownValues targetValues
              -> ∀ possibleTypes leftSelectionSet rightSelectionSet,
                  guardedFieldChildIncludesBool schema childFuel knownValues
                      possibleTypes leftSelectionSet rightSelectionSet
                    = true
                  -> childIncludes possibleTypes leftSelectionSet rightSelectionSet
                      = true)
    : ∀ right,
        right ∈ rightGroups
        -> ∀ region,
            region
              ∈ guardedFieldGroupTypeRegions
                  (guardedFieldParentRegion schema fixedExecutionParentType
                    (guardedFieldGroupFor leftGroups right) right)
                  (guardedFieldGroupFor leftGroups right) right
            -> ∀ runtimeType,
                runtimeType ∈ region
                -> guardedFieldGroupCaseIncludesBool schema responseFuel
                      fixedExecutionParentType targetValues runtimeType
                      (guardedFieldGroupFor leftGroups right) right childIncludes
                    = true := by
  induction rightGroups with
  | nil => simp
  | cons right rest ih =>
      rw [guardedFieldGroupsIncludeWithFuel.eq_def] at hcheck
      simp only [Bool.and_eq_true] at hcheck
      intro candidate hcandidate
      rcases List.mem_cons.mp hcandidate with heq | hrest
      · subst candidate
        intro region hregion runtimeType hruntime
        simp only [Bool.or_eq_true] at hcheck
        rcases hcheck.1 with hshortcut | hgeneral
        · cases responseFuel with
          | zero =>
              simp [guardedFieldGroupLocallyIncludesBool,
                guardedScalarFieldIncludesBool,
                guardedCompositeFieldIncludesBool] at hshortcut
          | succ childFuel =>
              simp only [guardedFieldGroupLocallyIncludesBool, Bool.or_eq_true]
                at hshortcut
              rcases hshortcut with hscalar | hcomposite
              · simp only [guardedScalarFieldIncludesBool] at hscalar
                have hregionCheck := List.all_eq_true.mp hscalar region hregion
                have hruntimeCheck := List.all_eq_true.mp hregionCheck runtimeType
                  hruntime
                exact guardedScalarFieldIncludesAtRuntimeTypeBool_sound schema
                  childFuel fixedExecutionParentType targetValues runtimeType
                  (guardedFieldGroupFor leftGroups right) right childIncludes
                  hruntimeCheck (hcomplete right (by simp))
              · simp only [guardedCompositeFieldIncludesBool] at hcomposite
                have hregionCheck := List.all_eq_true.mp hcomposite region hregion
                have hruntimeCheck := List.all_eq_true.mp hregionCheck runtimeType
                  hruntime
                apply guardedCompositeFieldIncludesAtRuntimeTypeBool_sound schema
                  childFuel fixedExecutionParentType targetValues runtimeType
                  (guardedFieldGroupFor leftGroups right) right childIncludes
                  hruntimeCheck (hcomplete right (by simp))
                intro possibleTypes leftSelectionSet rightSelectionSet hchildCheck
                exact hchildSound childFuel rfl targetValues
                  (booleanAssignmentsAgree_refl targetValues) possibleTypes
                  leftSelectionSet rightSelectionSet hchildCheck
        · apply guardedFieldGroupIncludesWithFuel_sound schema responseFuel
            fixedExecutionParentType checkValues targetValues
            (guardedFieldGroupBooleanVariables
              (guardedFieldGroupFor leftGroups right) right)
            (guardedFieldParentRegion schema fixedExecutionParentType
              (guardedFieldGroupFor leftGroups right) right)
            (guardedFieldGroupFor leftGroups right) right region runtimeType
            childIncludes
          · unfold guardedFieldGroupFor guardedFieldParentRegion
            exact hgeneral
          · exact hagrees
          · intro variableName hvariable
            exact Or.inl hvariable
          · intro variableName hvariable
            exact hvariable
          · exact hcomplete right (by simp)
          · exact hchildSound
          · exact hregion
          · exact hruntime
      · apply ih hcheck.2
        · intro group hgroup
          exact hcomplete group (by simp [hgroup])
        · exact hrest

set_option maxRecDepth 10000 in
theorem guardedFieldGroupsIncludeWithFuel_complete_cases
    (schema : Schema) (responseFuel : Nat)
    (fixedExecutionParentType : Option Name)
    (baseValues checkValues : VariableValues)
    (leftGroups rightGroups : List GuardedFieldGroup)
    (availableBooleanVariables : List Name)
    (childIncludes
      : VariableValues -> List Name -> List Selection -> List Selection -> Bool)
    (hbaseAgrees : BooleanAssignmentsAgree baseValues checkValues)
    (hknown : KnownBooleanVariablesWithin checkValues availableBooleanVariables)
    (hwithin
      : ∀ right,
          right ∈ rightGroups
          -> ∀ variableName,
              variableName
                ∈ guardedFieldGroupBooleanVariables
                    (guardedFieldGroupFor leftGroups right) right
              -> variableName ∈ availableBooleanVariables)
    (hchildComplete
      : ∀ childFuel,
          responseFuel = childFuel + 1
          -> ∀ knownValues,
              KnownBooleanVariablesWithin knownValues availableBooleanVariables
              -> BooleanAssignmentsAgree baseValues knownValues
              -> ∀ possibleTypes leftSelectionSet rightSelectionSet,
                  childIncludes knownValues possibleTypes leftSelectionSet
                      rightSelectionSet
                    = true
                  -> guardedFieldChildIncludesBool schema childFuel knownValues
                        possibleTypes leftSelectionSet rightSelectionSet
                      = true)
    (hcases
      : ∀ knownValues,
          KnownBooleanVariablesWithin knownValues availableBooleanVariables
          -> BooleanAssignmentsAgree baseValues knownValues
          -> ∀ right,
              right ∈ rightGroups
              -> (∀ variableName,
                    variableName
                      ∈ guardedFieldGroupBooleanVariables
                          (guardedFieldGroupFor leftGroups right) right
                    -> ∃ value,
                        inputValueBoolean? knownValues (.variable variableName)
                        = some value)
              -> ∀ targetValues,
                  boolVarsComplete availableBooleanVariables targetValues
                  -> BooleanAssignmentsAgree knownValues targetValues
                  -> ∀ region,
                      region
                        ∈ guardedFieldGroupTypeRegions
                            (guardedFieldParentRegion schema fixedExecutionParentType
                              (guardedFieldGroupFor leftGroups right) right)
                            (guardedFieldGroupFor leftGroups right) right
                      -> ∀ runtimeType,
                          runtimeType ∈ region
                          -> guardedFieldGroupCaseIncludesBool schema responseFuel
                                fixedExecutionParentType targetValues runtimeType
                                (guardedFieldGroupFor leftGroups right) right
                                (childIncludes knownValues)
                              = true)
    : guardedFieldGroupsIncludeWithFuel schema responseFuel
        fixedExecutionParentType checkValues leftGroups rightGroups
      = true := by
  induction rightGroups with
  | nil => simp [guardedFieldGroupsIncludeWithFuel]
  | cons right rest ih =>
      rw [guardedFieldGroupsIncludeWithFuel.eq_def, Bool.and_eq_true]
      constructor
      · simp only [Bool.or_eq_true]
        apply Or.inr
        apply guardedFieldGroupIncludesWithFuel_complete schema responseFuel
          fixedExecutionParentType baseValues checkValues
          (guardedFieldGroupBooleanVariables
            (guardedFieldGroupFor leftGroups right) right)
          (guardedFieldParentRegion schema fixedExecutionParentType
            (guardedFieldGroupFor leftGroups right) right)
          (guardedFieldGroupFor leftGroups right) right
          availableBooleanVariables childIncludes hbaseAgrees hknown
        · intro variableName hvariable
          exact Or.inl hvariable
        · intro variableName hvariable
          exact hvariable
        · exact hwithin right (by simp)
        · exact hchildComplete
        · intro knownValues hknownValues hagrees hgroupKnown targetValues hcomplete
            htargetAgrees
          exact hcases knownValues hknownValues hagrees right (by simp) hgroupKnown
            targetValues hcomplete htargetAgrees
      · apply ih
        · intro group hgroup
          exact hwithin group (by simp [hgroup])
        · intro knownValues hknownValues hagrees group hgroup hgroupKnown
            targetValues hcomplete htargetAgrees
          exact hcases knownValues hknownValues hagrees group (by simp [hgroup])
            hgroupKnown targetValues hcomplete htargetAgrees

end QueryInclusion
end GraphQL
