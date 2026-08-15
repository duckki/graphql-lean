import Proofs.GraphQL.Theories.QueryInclusion.Execution

/-! Complete Boolean assignments determine the proof-facing reference checker. -/

namespace GraphQL
namespace QueryInclusion

open Execution

private def executableGroupFields (groups : List (Name × List ExecutableField))
    : List ExecutableField :=
  groups.flatMap Prod.snd

private theorem mem_executableGroupFields_addExecutableGroup
    (field : ExecutableField) (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : field ∈ executableGroupFields (addExecutableGroup group groups)
      ↔ field ∈ group.2 ∨ field ∈ executableGroupFields groups := by
  induction groups with
  | nil => simp [executableGroupFields, addExecutableGroup]
  | cons head rest ih =>
      rcases head with ⟨responseName, fields⟩
      simp only [addExecutableGroup]
      split
      · simp [executableGroupFields, or_left_comm]
      · change field ∈
            (fields ++ executableGroupFields (addExecutableGroup group rest))
          ↔ field ∈ group.2 ∨ field ∈
            (fields ++ executableGroupFields rest)
        simp only [List.mem_append]
        rw [ih]
        simp [or_left_comm]

private theorem mem_executableGroupFields_mergeExecutableGroups
    (field : ExecutableField)
    (left right : List (Name × List ExecutableField))
    : field ∈ executableGroupFields (mergeExecutableGroups left right)
      ↔ field ∈ executableGroupFields left ∨ field ∈ executableGroupFields right := by
  unfold mergeExecutableGroups
  induction right generalizing left with
  | nil => simp [executableGroupFields]
  | cons group rest ih =>
      rw [List.foldl_cons, ih]
      rw [mem_executableGroupFields_addExecutableGroup]
      simp only [executableGroupFields, List.flatMap_cons, List.mem_append]
      simp [or_left_comm, or_assoc]

private theorem mem_group_field_executableGroupFields
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    (hgroup : group ∈ groups) {field : ExecutableField}
    (hfield : field ∈ group.2)
    : field ∈ executableGroupFields groups := by
  unfold executableGroupFields
  exact List.mem_flatMap.mpr ⟨group, hgroup, hfield⟩

mutual
  private theorem collectSelection_field_variables_within
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection) (field : ExecutableField)
      (hfield
        : field
          ∈ executableGroupFields
              (collectSelection schema variableValues parentType source selection))
      : ∀ variableName,
          variableName
            ∈ SelectionConditions.selectionSetBooleanVariables field.selectionSet
          -> variableName ∈ SelectionConditions.selectionBooleanVariables selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp only [collectSelection] at hfield
        split at hfield
        · simp only [executableGroupFields, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hfield
          subst field
          intro variableName hvariable
          simp [SelectionConditions.selectionBooleanVariables, hvariable]
        · simp [executableGroupFields] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            simp only [collectSelection] at hfield
            split at hfield
            · intro variableName hvariable
              have hwithin := (collectFields_field_variables_within schema variableValues parentType
                source selectionSet field hfield) variableName hvariable
              change variableName ∈ directives.filterMap
                  SelectionConditions.directiveBooleanVariable?
                ++ SelectionConditions.selectionSetBooleanVariables selectionSet
              exact List.mem_append.mpr (Or.inr hwithin)
            · simp [executableGroupFields] at hfield
        | some typeName =>
            simp only [collectSelection] at hfield
            split at hfield
            · split at hfield
              · intro variableName hvariable
                have hwithin := (collectFields_field_variables_within schema variableValues parentType
                  source selectionSet field hfield) variableName hvariable
                change variableName ∈ directives.filterMap
                    SelectionConditions.directiveBooleanVariable?
                  ++ SelectionConditions.selectionSetBooleanVariables selectionSet
                exact List.mem_append.mpr (Or.inr hwithin)
              · simp [executableGroupFields] at hfield
            · simp [executableGroupFields] at hfield

  private theorem collectFields_field_variables_within
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selectionSet : List Selection) (field : ExecutableField)
      (hfield
        : field
          ∈ executableGroupFields
              (collectFields schema variableValues parentType source selectionSet))
      : ∀ variableName,
          variableName
            ∈ SelectionConditions.selectionSetBooleanVariables field.selectionSet
          -> variableName
              ∈ SelectionConditions.selectionSetBooleanVariables selectionSet := by
    cases selectionSet with
    | nil => simp [collectFields, executableGroupFields] at hfield
    | cons selection rest =>
        simp only [collectFields] at hfield
        rcases (mem_executableGroupFields_mergeExecutableGroups field _ _).mp hfield with
          hhead | htail
        · intro variableName hvariable
          have horigin := collectSelection_field_variables_within schema variableValues
            parentType source selection field hhead variableName hvariable
          simp [SelectionConditions.selectionSetBooleanVariables, horigin]
        · intro variableName hvariable
          have horigin := collectFields_field_variables_within schema variableValues
            parentType source rest field htail variableName hvariable
          simp [SelectionConditions.selectionSetBooleanVariables, horigin]
end

private theorem selectionSetBooleanVariables_append (left right : List Selection)
    : SelectionConditions.selectionSetBooleanVariables (left ++ right)
      = SelectionConditions.selectionSetBooleanVariables left
        ++ SelectionConditions.selectionSetBooleanVariables right := by
  induction left with
  | nil => rfl
  | cons selection rest ih =>
      simp [SelectionConditions.selectionSetBooleanVariables, ih, List.append_assoc]

private theorem mem_selectionSetBooleanVariables_flatMap_selectionSet
    (fields : List ExecutableField) (variableName : Name)
    : variableName
        ∈ SelectionConditions.selectionSetBooleanVariables
            (fields.flatMap ExecutableField.selectionSet)
      ↔ ∃ field,
          field ∈ fields
          ∧ variableName
            ∈ SelectionConditions.selectionSetBooleanVariables field.selectionSet := by
  induction fields with
  | nil => simp [SelectionConditions.selectionSetBooleanVariables]
  | cons field rest ih =>
      rw [List.flatMap_cons, selectionSetBooleanVariables_append]
      simp only [List.mem_append, ih]
      constructor
      · intro h
        rcases h with h | ⟨candidate, hrest, hcandidate⟩
        · exact ⟨field, by simp, h⟩
        · exact ⟨candidate, by simp [hrest], hcandidate⟩
      · rintro ⟨candidate, hcandidate, hvariable⟩
        rcases List.mem_cons.mp hcandidate with rfl | hrest
        · exact Or.inl hvariable
        · exact Or.inr ⟨candidate, hrest, hvariable⟩

theorem mergedSelectionSet_variables_within_of_group_mem
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (selectionSet : List Selection)
    (group : Name × List ExecutableField)
    (hgroup
      : group
        ∈ collectRuntimeFieldGroups schema variableValues parentType runtimeType
            selectionSet)
    : ∀ variableName,
        variableName
          ∈ SelectionConditions.selectionSetBooleanVariables
              (executableFieldsMergedSelectionSet group.2)
        -> variableName
            ∈ SelectionConditions.selectionSetBooleanVariables selectionSet := by
  intro variableName hvariable
  rw [executableFieldsMergedSelectionSet,
    mem_selectionSetBooleanVariables_flatMap_selectionSet] at hvariable
  rcases hvariable with ⟨field, hfield, hvariable⟩
  rw [collectRuntimeFieldGroups_eq_collectFields_object] at hgroup
  exact collectFields_field_variables_within schema variableValues parentType
    (.object runtimeType PUnit.unit) selectionSet field
    (mem_group_field_executableGroupFields hgroup hfield) variableName hvariable

private theorem listAll_congr_of_mem {items : List α} {left right : α -> Bool}
    (heq : ∀ item ∈ items, left item = right item)
    : items.all left = items.all right := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.all_cons]
      rw [heq item (by simp)]
      rw [ih (by
        intro candidate hcandidate
        exact heq candidate (by simp [hcandidate]))]

private theorem listAny_congr_of_mem {items : List α} {left right : α -> Bool}
    (heq : ∀ item ∈ items, left item = right item)
    : items.any left = items.any right := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [List.any_cons]
      rw [heq item (by simp)]
      rw [ih (by
        intro candidate hcandidate
        exact heq candidate (by simp [hcandidate]))]

theorem selectionSetIncludesBoolWithFuel_eq_of_boolean_agreement
    (schema : Schema) (fuel : Nat) (parentType : Name)
    (first second : VariableValues)
    (leftSelectionSet rightSelectionSet : List Selection)
    (hleft
      : ∀ variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables leftSelectionSet
          -> inputValueBoolean? first (.variable variableName)
              = inputValueBoolean? second (.variable variableName))
    (hright
      : ∀ variableName,
          variableName
            ∈ SelectionConditions.selectionSetBooleanVariables rightSelectionSet
          -> inputValueBoolean? first (.variable variableName)
              = inputValueBoolean? second (.variable variableName))
    : selectionSetIncludesBoolWithFuel schema fuel parentType first
        leftSelectionSet rightSelectionSet
      = selectionSetIncludesBoolWithFuel schema fuel parentType second
          leftSelectionSet rightSelectionSet := by
  induction fuel generalizing parentType leftSelectionSet rightSelectionSet with
  | zero =>
      simp only [selectionSetIncludesBoolWithFuel,
        selectionSetIncludesAtRuntimeBoolWithFuel]
      apply listAll_congr_of_mem
      intro runtimeType _hruntime
      have hrightGroups := collectFields_eq_of_boolean_agreement schema first second
        parentType (.object runtimeType PUnit.unit) rightSelectionSet hright
      change collectRuntimeFieldGroups schema first parentType runtimeType
          rightSelectionSet
        = collectRuntimeFieldGroups schema second parentType runtimeType
            rightSelectionSet at hrightGroups
      rw [hrightGroups]
  | succ fuel ih =>
      simp only [selectionSetIncludesBoolWithFuel,
        selectionSetIncludesAtRuntimeBoolWithFuel]
      apply listAll_congr_of_mem
      intro runtimeType _hruntime
      have hleftGroups := collectFields_eq_of_boolean_agreement schema first second
        parentType (ResolverValue.object runtimeType PUnit.unit) leftSelectionSet hleft
      have hrightGroups := collectFields_eq_of_boolean_agreement schema first second
        parentType (ResolverValue.object runtimeType PUnit.unit) rightSelectionSet hright
      change collectRuntimeFieldGroups schema first parentType runtimeType leftSelectionSet
          = collectRuntimeFieldGroups schema second parentType runtimeType leftSelectionSet
        at hleftGroups
      change collectRuntimeFieldGroups schema first parentType runtimeType rightSelectionSet
          = collectRuntimeFieldGroups schema second parentType runtimeType rightSelectionSet
        at hrightGroups
      rw [hleftGroups, hrightGroups]
      apply listAll_congr_of_mem
      intro rightGroup hrightGroup
      apply listAny_congr_of_mem
      intro leftGroup hleftGroup
      rcases leftGroup with ⟨leftName, leftFields⟩
      rcases rightGroup with ⟨rightName, rightFields⟩
      cases leftFields with
      | nil => rfl
      | cons leftField leftRest =>
          cases rightFields with
          | nil => rfl
          | cons rightField rightRest =>
              cases hlookup
                    : schema.lookupField rightField.parentType rightField.fieldName with
              | none => simp [hlookup]
              | some definition =>
                  by_cases hcomposite : definition.outputType.isCompositeBool schema = true
                  · simp only [hlookup, hcomposite, ↓reduceIte]
                    have hnested :
                        (schema.getPossibleTypes definition.outputType.namedType).all
                            (fun childRuntimeType =>
                              selectionSetIncludesBoolWithFuel schema fuel childRuntimeType
                                first
                                (executableFieldsMergedSelectionSet
                                  (leftField :: leftRest))
                                (executableFieldsMergedSelectionSet
                                  (rightField :: rightRest)))
                          = (schema.getPossibleTypes definition.outputType.namedType).all
                            (fun childRuntimeType =>
                              selectionSetIncludesBoolWithFuel schema fuel childRuntimeType
                                second
                                (executableFieldsMergedSelectionSet
                                  (leftField :: leftRest))
                                (executableFieldsMergedSelectionSet
                                  (rightField :: rightRest))) := by
                      apply listAll_congr_of_mem
                      intro childRuntimeType _hchildRuntime
                      apply ih
                      · intro variableName hvariable
                        apply hleft variableName
                        exact mergedSelectionSet_variables_within_of_group_mem schema second
                          parentType runtimeType leftSelectionSet
                          (leftName, leftField :: leftRest) hleftGroup variableName hvariable
                      · intro variableName hvariable
                        apply hright variableName
                        exact mergedSelectionSet_variables_within_of_group_mem schema second
                          parentType runtimeType rightSelectionSet
                          (rightName, rightField :: rightRest) hrightGroup variableName hvariable
                    have hnested' := hnested
                    simp only [selectionSetIncludesBoolWithFuel.eq_def] at hnested'
                    rw [hnested']
                  · simp [hlookup, hcomposite]

theorem includesBoolReference_to_selectionSetChecks
    {schema : Schema} {left right : Operation}
    (hcheck : includesBoolReference schema left right = true)
    : left.rootType schema = right.rootType schema
      ∧ sharedVariableDefinitionsSyntacticallyCompatibleBool
          left.variableDefinitions right.variableDefinitions
        = true
      ∧ ∀ variableValues,
          boolVarsComplete
            (comparisonConditionVariables left.selectionSet right.selectionSet)
            variableValues
          -> selectionSetIncludesBoolWithFuel schema (right.size + 1)
                (right.rootType schema) variableValues
                left.selectionSet right.selectionSet
              = true := by
  unfold includesBoolReference at hcheck
  split at hcheck
  · rename_i hguard
    have hparts :
        (left.rootType schema == right.rootType schema) = true
          ∧ sharedVariableDefinitionsSyntacticallyCompatibleBool
            left.variableDefinitions right.variableDefinitions = true := by
      simpa only [Bool.and_eq_true] using hguard
    rcases hparts with ⟨hroot, hdefinitions⟩
    refine ⟨beq_iff_eq.mp hroot, hdefinitions, ?_⟩
    intro variableValues hcomplete
    let variables := comparisonConditionVariables left.selectionSet right.selectionSet
    let representative := representativeBooleanValues variables variableValues
    have hrepresentative : representative ∈ booleanVariableAssignments variables :=
      representativeBooleanValues_mem variables variableValues
    have hrepresentativeCheck :
        selectionSetIncludesBoolWithFuel schema (right.size + 1)
          (right.rootType schema) representative
          left.selectionSet right.selectionSet = true := by
      exact List.all_eq_true.mp hcheck representative (by
        simpa only [variables] using hrepresentative)
    have hagreement := selectionSetIncludesBoolWithFuel_eq_of_boolean_agreement schema
      (right.size + 1) (right.rootType schema) representative variableValues
      left.selectionSet right.selectionSet
      (by
        intro variableName hvariable
        exact inputValueBoolean?_representativeBooleanValues variables variableValues
          (by
            intro candidate hcandidate
            exact hcomplete candidate (by simpa [variables] using hcandidate))
          variableName (by
            simp [variables, comparisonConditionVariables, hvariable]))
      (by
        intro variableName hvariable
        exact inputValueBoolean?_representativeBooleanValues variables variableValues
          (by
            intro candidate hcandidate
            exact hcomplete candidate (by simpa [variables] using hcandidate))
          variableName (by
            simp [variables, comparisonConditionVariables, hvariable]))
    rw [← hagreement]
    exact hrepresentativeCheck
  · simp at hcheck

end QueryInclusion
end GraphQL
