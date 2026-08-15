import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Theories.QueryInclusion.BooleanAssignments
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant
import Proofs.GraphQL.Execution.FieldGroups
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.RuntimeFragmentSemantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterExecution
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Variables
import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes

/-! Soundness of the executable query-inclusion check for annotated execution. -/

namespace GraphQL
namespace QueryInclusion

open Execution AnnotatedExecution
open Algorithms.ExecutionUngroupedUncached.Eager
open NormalForm.CompleteNormalization

universe u v

mutual
  theorem collectFields_object_ref_irrelevant
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name) (leftRef : α) (rightRef : β)
      (selectionSet : List Selection)
      : collectFields schema variableValues parentType (.object runtimeType leftRef)
          selectionSet
        = collectFields schema variableValues parentType (.object runtimeType rightRef)
            selectionSet := by
    cases selectionSet with
    | nil => rfl
    | cons selection rest =>
        simp only [collectFields]
        rw [collectSelection_object_ref_irrelevant schema variableValues parentType
          runtimeType leftRef rightRef selection]
        rw [collectFields_object_ref_irrelevant schema variableValues parentType
          runtimeType leftRef rightRef rest]

  theorem collectSelection_object_ref_irrelevant
      (schema : Schema) (variableValues : VariableValues)
      (parentType runtimeType : Name) (leftRef : α) (rightRef : β)
      (selection : Selection)
      : collectSelection schema variableValues parentType (.object runtimeType leftRef)
          selection
        = collectSelection schema variableValues parentType (.object runtimeType rightRef)
            selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rfl
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            simp only [collectSelection]
            split
            · exact collectFields_object_ref_irrelevant schema variableValues parentType
                runtimeType leftRef rightRef selectionSet
            · rfl
        | some typeName =>
            simp only [collectSelection, doesFragmentTypeApplyBool, runtimeObjectType?]
            split
            · by_cases happlies :
                  schema.typeIncludesObjectBool typeName runtimeType = true
              · simp only [happlies, ↓reduceIte]
                exact collectFields_object_ref_irrelevant schema variableValues parentType
                  runtimeType leftRef rightRef selectionSet
              · simp [happlies]
            · rfl
end

theorem collectRuntimeFieldGroups_eq_collectFields_object
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (ref : ObjectRef)
    (selectionSet : List Selection)
    : collectRuntimeFieldGroups schema variableValues parentType runtimeType selectionSet
      = collectFields schema variableValues parentType (.object runtimeType ref)
          selectionSet := by
  exact collectFields_object_ref_irrelevant schema variableValues parentType runtimeType
    PUnit.unit ref selectionSet

@[simp]
theorem executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet
    (fields : List ExecutableField)
    : executableFieldsMergedSelectionSet fields = mergedFieldSelectionSet fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      change field.selectionSet ++ executableFieldsMergedSelectionSet rest
        = field.selectionSet ++ mergedFieldSelectionSet rest
      rw [ih]

private theorem isCompositeBool_eq_true_of_typeIncludesObjectBool
    (schema : Schema) (typeName objectName : Name)
    (hincludes : schema.typeIncludesObjectBool typeName objectName = true)
    : (TypeRef.named typeName).isCompositeBool schema = true := by
  unfold Schema.typeIncludesObjectBool Schema.getPossibleTypes at hincludes
  unfold TypeRef.isCompositeBool TypeRef.namedType
  cases hlookup : schema.lookupType typeName with
  | none => simp [hlookup] at hincludes
  | some typeDefinition =>
      cases typeDefinition <;> simp [hlookup] at hincludes ⊢

theorem inputValueBoolean?_eq_of_lookup_equivalent
    {left right : VariableValues} {variableName : Name}
    (hequivalent
      : Option.Rel
          (fun leftValue rightValue =>
            InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
          (lookupVariableValue? left variableName)
          (lookupVariableValue? right variableName))
    : inputValueBoolean? left (.variable variableName)
      = inputValueBoolean? right (.variable variableName) := by
  cases hleft : lookupVariableValue? left variableName <;>
    cases hright : lookupVariableValue? right variableName <;>
    simp [hleft, hright, inputValueBoolean?] at hequivalent ⊢
  rename_i leftValue rightValue
  have hcanonical := Execution.inputValue_canonical_eq_of_equivalent hequivalent
  cases leftValue <;> cases rightValue <;>
    simp [ConstInputValue.toInputValue, InputValue.canonical,
      InputValue.staticBoolean?] at hcanonical ⊢
  exact hcanonical

theorem lookupVariableValue?_append
    : ∀ (initial suffix : VariableValues) name,
        lookupVariableValue? (initial ++ suffix) name
        = match lookupVariableValue? initial name with
          | some value => some value
          | none => lookupVariableValue? suffix name
  | [], _suffix, _name => rfl
  | (candidateName, candidateValue) :: rest, suffix, name => by
      by_cases hname : candidateName = name <;>
        simp [lookupVariableValue?, hname,
          lookupVariableValue?_append rest suffix name]

private theorem lookupVariableValue?_foldlDefaults_of_name_not_mem
    (definitions : List VariableDefinition) (variableValues : VariableValues)
    (name : Name) (hname : name ∉ definitions.map VariableDefinition.name)
    : lookupVariableValue?
        (definitions.foldl
          (fun values definition =>
            match lookupVariableValue? values definition.name with
            | some _value => values
            | none =>
                match definition.defaultValue with
                | some defaultValue => (definition.name, defaultValue) :: values
                | none => values)
          variableValues)
        name
      = lookupVariableValue? variableValues name := by
  induction definitions generalizing variableValues with
  | nil => rfl
  | cons definition rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hname
      simp only [List.foldl_cons]
      apply (ih _ hname.2).trans
      split
      · rfl
      · split
        · simp only [lookupVariableValue?]
          split
          · rename_i heq
            exact (hname.1 heq.symm).elim
          · rfl
        · rfl

theorem lookupVariableValue?_coerceVariableValues_of_name_not_defined
    (operation : Operation) (variableValues : VariableValues) (name : Name)
    (hname : name ∉ operation.variableDefinitions.map VariableDefinition.name)
    : lookupVariableValue? (coerceVariableValues operation variableValues) name
      = lookupVariableValue? variableValues name := by
  exact lookupVariableValue?_foldlDefaults_of_name_not_mem
    operation.variableDefinitions variableValues name hname

private theorem lookupVariableValue?_foldlDefaults_at_definition
    {definitions : List VariableDefinition} {definition : VariableDefinition}
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    (hdefinition : definition ∈ definitions) (variableValues : VariableValues)
    : lookupVariableValue?
        (definitions.foldl
          (fun values candidate =>
            match lookupVariableValue? values candidate.name with
            | some _value => values
            | none =>
                match candidate.defaultValue with
                | some defaultValue => (candidate.name, defaultValue) :: values
                | none => values)
          variableValues)
        definition.name
      = match lookupVariableValue? variableValues definition.name with
        | some value => some value
        | none => definition.defaultValue := by
  induction definitions generalizing variableValues with
  | nil => simp at hdefinition
  | cons candidate rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hdefinition with rfl | hrest
      · simp only [List.foldl_cons]
        cases hlookup : lookupVariableValue? variableValues definition.name with
        | some value =>
            simpa [hlookup] using
              lookupVariableValue?_foldlDefaults_of_name_not_mem rest variableValues
                definition.name hnodup.1
        | none =>
            cases hdefault : definition.defaultValue with
            | none =>
                simpa [hlookup, hdefault] using
                  lookupVariableValue?_foldlDefaults_of_name_not_mem rest variableValues
                    definition.name hnodup.1
            | some defaultValue =>
                have hadded : lookupVariableValue?
                    ((definition.name, defaultValue) :: variableValues)
                    definition.name = some defaultValue := by
                  simp [lookupVariableValue?]
                simpa [hlookup, hdefault] using
                  (lookupVariableValue?_foldlDefaults_of_name_not_mem rest
                    ((definition.name, defaultValue) :: variableValues)
                    definition.name hnodup.1).trans hadded
      · simp only [List.foldl_cons]
        let nextValues :=
          match lookupVariableValue? variableValues candidate.name with
          | some _value => variableValues
          | none =>
              match candidate.defaultValue with
              | some defaultValue => (candidate.name, defaultValue) :: variableValues
              | none => variableValues
        have hne : candidate.name ≠ definition.name := by
          intro heq
          apply hnodup.1
          rw [heq]
          exact List.mem_map.mpr ⟨definition, hrest, rfl⟩
        have hnextLookup : lookupVariableValue? nextValues definition.name
            = lookupVariableValue? variableValues definition.name := by
          simp only [nextValues]
          split
          · rfl
          · split
            · simp [lookupVariableValue?, hne]
            · rfl
        rw [ih hnodup.2 hrest nextValues, hnextLookup]

theorem lookupVariableValue?_coerceVariableValues_at_definition
    {operation : Operation} {definition : VariableDefinition}
    (hnodup : (operation.variableDefinitions.map VariableDefinition.name).Nodup)
    (hdefinition : definition ∈ operation.variableDefinitions)
    (variableValues : VariableValues)
    : lookupVariableValue? (coerceVariableValues operation variableValues) definition.name
      = match lookupVariableValue? variableValues definition.name with
        | some value => some value
        | none => definition.defaultValue := by
  exact lookupVariableValue?_foldlDefaults_at_definition hnodup hdefinition
    variableValues

theorem coerceVariableValues_shared_lookup_equivalent
    {left right : Operation} {leftDefinition rightDefinition : VariableDefinition}
    (hdefinitions
      : sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
          right.variableDefinitions)
    (hleftNodup : (left.variableDefinitions.map VariableDefinition.name).Nodup)
    (hrightNodup : (right.variableDefinitions.map VariableDefinition.name).Nodup)
    (hleftDefinition : leftDefinition ∈ left.variableDefinitions)
    (hrightDefinition : rightDefinition ∈ right.variableDefinitions)
    (hname : leftDefinition.name = rightDefinition.name)
    (variableValues : VariableValues)
    : Option.Rel
        (fun leftValue rightValue =>
          InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
        (lookupVariableValue? (coerceVariableValues left variableValues)
          leftDefinition.name)
        (lookupVariableValue? (coerceVariableValues right variableValues)
          rightDefinition.name) := by
  rw [lookupVariableValue?_coerceVariableValues_at_definition hleftNodup
      hleftDefinition,
    lookupVariableValue?_coerceVariableValues_at_definition hrightNodup
      hrightDefinition]
  rw [← hname]
  cases hlookup : lookupVariableValue? variableValues leftDefinition.name with
  | some value =>
      exact .some (inputValueStructuralEquivalent_refl value.toInputValue.canonical)
  | none =>
      rcases sharedVariableDefinitionsSyntacticallyCompatible_of_mem hdefinitions
          hrightNodup hleftDefinition hrightDefinition hname with
        ⟨_hdefinitionName, _hdefinitionType, hdefaults⟩
      generalize hleftDefault : leftDefinition.defaultValue = leftDefault at hdefaults ⊢
      generalize hrightDefault : rightDefinition.defaultValue = rightDefault at hdefaults ⊢
      cases leftDefault <;> cases rightDefault <;>
        simp at hdefaults ⊢
      change InputValue.equivalent _ _ at hdefaults
      exact hdefaults

private theorem selectionConditionDirectiveVariables_mem_normalForm
    : ∀ directives variableName,
        variableName ∈ directives.filterMap SelectionConditions.directiveBooleanVariable?
        -> variableName ∈ NormalForm.directivesBooleanVariables directives
  | [], _variableName, hmember => by simp at hmember
  | directive :: rest, variableName, hmember => by
      simp only [List.filterMap_cons] at hmember
      rw [NormalForm.directivesBooleanVariables]
      cases hdirective : SelectionConditions.directiveBooleanVariable? directive with
      | none =>
          simp only [hdirective] at hmember
          exact List.mem_append_right _
            (selectionConditionDirectiveVariables_mem_normalForm rest variableName
              hmember)
      | some candidate =>
          simp only [hdirective, List.mem_cons] at hmember
          rcases hmember with rfl | hrest
          · apply List.mem_append_left
            cases directive <;> rename_i value <;> cases value <;>
              simp [SelectionConditions.directiveBooleanVariable?,
                NormalForm.directiveBooleanVariables,
                NormalForm.inputValueBooleanVariables] at hdirective ⊢
            all_goals exact hdirective.symm
          · exact List.mem_append_right _
              (selectionConditionDirectiveVariables_mem_normalForm rest variableName
                hrest)

mutual
  private theorem selectionConditionVariables_mem_normalForm
      : ∀ selection variableName,
          variableName ∈ SelectionConditions.selectionBooleanVariables selection
          -> variableName ∈ NormalForm.selectionBooleanVariables selection
    | .field _responseName _fieldName _arguments directives selectionSet,
        variableName, hmember
    | .inlineFragment _typeCondition directives selectionSet,
        variableName, hmember => by
        simp only [SelectionConditions.selectionBooleanVariables, List.mem_append]
          at hmember
        simp only [NormalForm.selectionBooleanVariables, List.mem_append]
        cases hmember with
        | inl hdirectives =>
            exact Or.inl
              (selectionConditionDirectiveVariables_mem_normalForm directives
                variableName hdirectives)
        | inr hchildren =>
            exact Or.inr
              (selectionSetConditionVariables_mem_normalForm selectionSet variableName
                hchildren)

  private theorem selectionSetConditionVariables_mem_normalForm
      : ∀ selectionSet variableName,
          variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
          -> variableName ∈ NormalForm.selectionSetBooleanVariables selectionSet
    | [], _variableName, hmember => by cases hmember
    | selection :: rest, variableName, hmember => by
        simp only [SelectionConditions.selectionSetBooleanVariables, List.mem_append]
          at hmember
        simp only [NormalForm.selectionSetBooleanVariables, List.mem_append]
        cases hmember with
        | inl hselection =>
            exact Or.inl
              (selectionConditionVariables_mem_normalForm selection variableName
                hselection)
        | inr hrest =>
            exact Or.inr
              (selectionSetConditionVariables_mem_normalForm rest variableName hrest)
end

mutual
  private theorem selectionBooleanVariables_mem_selectionVariables
      : ∀ selection variableName,
          variableName ∈ NormalForm.selectionBooleanVariables selection
          -> variableName ∈ Validation.selectionVariables selection
    | .field _responseName _fieldName _arguments directives selectionSet,
        variableName, hvariable => by
        simp only [NormalForm.selectionBooleanVariables, List.mem_append] at hvariable
        simp only [Validation.selectionVariables, List.mem_append]
        rcases hvariable with hdirectives | hchildren
        · exact Or.inl (Or.inr (by
            rw [
              NormalForm.CompleteNormalization.directivesBooleanVariables_eq_variables]
              at hdirectives
            exact hdirectives))
        · exact Or.inr
            (selectionSetBooleanVariables_mem_selectionSetVariables selectionSet
              variableName hchildren)
    | .inlineFragment _typeCondition directives selectionSet,
        variableName, hvariable => by
        simp only [NormalForm.selectionBooleanVariables, List.mem_append] at hvariable
        simp only [Validation.selectionVariables, List.mem_append]
        rcases hvariable with hdirectives | hchildren
        · exact Or.inl (by
            rw [
              NormalForm.CompleteNormalization.directivesBooleanVariables_eq_variables]
              at hdirectives
            exact hdirectives)
        · exact Or.inr
            (selectionSetBooleanVariables_mem_selectionSetVariables selectionSet
              variableName hchildren)

  private theorem selectionSetBooleanVariables_mem_selectionSetVariables
      : ∀ selectionSet variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables selectionSet
          -> variableName ∈ Validation.selectionSetVariables selectionSet
    | [], _variableName, hvariable => by cases hvariable
    | selection :: rest, variableName, hvariable => by
        simp only [NormalForm.selectionSetBooleanVariables, List.mem_append] at hvariable
        simp only [Validation.selectionSetVariables, List.mem_append]
        rcases hvariable with hselection | hrest
        · exact Or.inl
            (selectionBooleanVariables_mem_selectionVariables selection variableName
              hselection)
        · exact Or.inr
            (selectionSetBooleanVariables_mem_selectionSetVariables rest variableName
              hrest)
end

theorem modeledConditionVariable_mem_selectionVariables
    (selectionSet : List Selection) (variableName : Name)
    (hvariable
      : variableName ∈ SelectionConditions.selectionSetBooleanVariables selectionSet)
    : variableName ∈ Validation.selectionSetVariables selectionSet :=
  selectionSetBooleanVariables_mem_selectionSetVariables selectionSet variableName
    (selectionSetConditionVariables_mem_normalForm selectionSet variableName hvariable)

theorem selectionBooleanVariable_mem_selectionVariables
    (selectionSet : List Selection) (variableName : Name)
    (hvariable : variableName ∈ NormalForm.selectionSetBooleanVariables selectionSet)
    : variableName ∈ Validation.selectionSetVariables selectionSet :=
  selectionSetBooleanVariables_mem_selectionSetVariables selectionSet variableName
    hvariable

mutual
  private theorem collectSelection_executableFieldVariables
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (selection : Selection)
      : ∀ field,
          field
            ∈ collectedExecutableFields
                (collectSelection schema variableValues parentType source selection)
          -> ∀ variableName,
              variableName ∈ Validation.argumentsVariables field.arguments
                ∨ variableName ∈ Validation.selectionSetVariables field.selectionSet
              -> variableName ∈ Validation.selectionVariables selection := by
    intro field hfield variableName hvariable
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        cases hallows : selectionDirectivesAllowBool variableValues directives <;>
          simp [collectSelection, hallows, collectedExecutableFields] at hfield
        subst field
        rcases hvariable with harguments | hchildren
        · change variableName ∈
              (Validation.argumentsVariables arguments
                ++ Validation.directivesVariables directives)
                ++ Validation.selectionSetVariables selectionSet
          exact List.mem_append_left _ (List.mem_append_left _ harguments)
        · change variableName ∈
              (Validation.argumentsVariables arguments
                ++ Validation.directivesVariables directives)
                ++ Validation.selectionSetVariables selectionSet
          exact List.mem_append_right _ hchildren
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            cases hallows : selectionDirectivesAllowBool variableValues directives
            · simp [collectSelection, hallows, collectedExecutableFields] at hfield
            · have hfield' : field ∈ collectedExecutableFields
                  (collectFields schema variableValues parentType source selectionSet) := by
                simpa [collectSelection, hallows] using hfield
              change variableName ∈ Validation.directivesVariables directives
                ++ Validation.selectionSetVariables selectionSet
              exact List.mem_append_right _
                (collectFields_executableFieldVariables schema variableValues
                  parentType source selectionSet field hfield' variableName hvariable)
        | some typeCondition =>
            cases hallows : selectionDirectivesAllowBool variableValues directives
            · simp [collectSelection, hallows, collectedExecutableFields] at hfield
            · cases happlies : doesFragmentTypeApplyBool schema parentType source
                  typeCondition
              · simp [collectSelection, hallows, happlies,
                  collectedExecutableFields] at hfield
              · have hfield' : field ∈ collectedExecutableFields
                    (collectFields schema variableValues parentType source selectionSet) := by
                  simpa [collectSelection, hallows, happlies] using hfield
                change variableName ∈ Validation.directivesVariables directives
                  ++ Validation.selectionSetVariables selectionSet
                exact List.mem_append_right _
                  (collectFields_executableFieldVariables schema variableValues
                    parentType source selectionSet field hfield' variableName hvariable)

  private theorem collectFields_executableFieldVariables
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selectionSet field,
          field
            ∈ collectedExecutableFields
                (collectFields schema variableValues parentType source selectionSet)
          -> ∀ variableName,
              variableName ∈ Validation.argumentsVariables field.arguments
                ∨ variableName ∈ Validation.selectionSetVariables field.selectionSet
              -> variableName ∈ Validation.selectionSetVariables selectionSet
    | [], _field, hfield => by simp [collectFields, collectedExecutableFields] at hfield
    | selection :: rest, field, hfield => by
        simp only [collectFields] at hfield
        rcases (collectedExecutableFields_mem_mergeExecutableGroups _ _ field).mp
            hfield with hselection | hrest
        · intro variableName hvariable
          simp only [Validation.selectionSetVariables, List.mem_append]
          exact Or.inl
            (collectSelection_executableFieldVariables schema variableValues
              parentType source selection field hselection variableName hvariable)
        · intro variableName hvariable
          simp only [Validation.selectionSetVariables, List.mem_append]
          exact Or.inr
            (collectFields_executableFieldVariables schema variableValues parentType
              source rest field hrest variableName hvariable)
end

private theorem validationSelectionSetVariables_append
    : ∀ left right,
        Validation.selectionSetVariables (left ++ right)
        = Validation.selectionSetVariables left ++ Validation.selectionSetVariables right
  | [], _right => rfl
  | selection :: rest, right => by
      simp [Validation.selectionSetVariables,
        validationSelectionSetVariables_append rest right, List.append_assoc]

private theorem executableFieldsMergedSelectionVariables_exists {variableName : Name}
    : ∀ fields,
        variableName
          ∈ Validation.selectionSetVariables (executableFieldsMergedSelectionSet fields)
        -> ∃ field,
            field ∈ fields
            ∧ variableName ∈ Validation.selectionSetVariables field.selectionSet
  | [], hvariable => by cases hvariable
  | field :: rest, hvariable => by
      change variableName ∈ Validation.selectionSetVariables
        (field.selectionSet ++ executableFieldsMergedSelectionSet rest) at hvariable
      rw [validationSelectionSetVariables_append,
        List.mem_append] at hvariable
      rcases hvariable with hfield | hrest
      · exact ⟨field, by simp, hfield⟩
      · rcases executableFieldsMergedSelectionVariables_exists rest hrest with
          ⟨candidate, hcandidate, hcandidateVariable⟩
        exact ⟨candidate, by simp [hcandidate], hcandidateVariable⟩

def executableFieldListsIncludeWithFuel (schema : Schema) (fuel : Nat)
    (conditionValues leftValues rightValues : VariableValues)
    (leftFields rightFields : List ExecutableField)
    : Prop :=
  match leftFields, rightFields with
  | leftField :: _leftRest, rightField :: _rightRest =>
      leftField.parentType = rightField.parentType
      ∧ leftField.fieldName = rightField.fieldName
      ∧ Argument.argumentsEquivalent leftField.arguments rightField.arguments
      ∧ (∃ definition,
          schema.lookupField rightField.parentType rightField.fieldName = some definition
          ∧ ArgumentCoercionResult.equivalent
              (coerceArgumentValues schema leftValues definition.arguments
                leftField.arguments)
              (coerceArgumentValues schema rightValues definition.arguments
                rightField.arguments)
          ∧ if definition.outputType.isCompositeBool schema then
              ∀ childRuntimeType,
                childRuntimeType ∈ schema.getPossibleTypes definition.outputType.namedType
                -> selectionSetIncludesBoolWithFuel schema fuel childRuntimeType
                      conditionValues
                      (executableFieldsMergedSelectionSet leftFields)
                      (executableFieldsMergedSelectionSet rightFields)
                    = true
            else
              True)
      ∧ ExecutableFieldsArgumentsNodup (leftField :: _leftRest)
      ∧ ExecutableFieldsArgumentsNodup (rightField :: _rightRest)
      ∧ (∀ field,
          field ∈ leftField :: _leftRest -> selectionSetArgumentsNodup field.selectionSet)
      ∧ (∀ field,
          field ∈ rightField :: _rightRest
          -> selectionSetArgumentsNodup field.selectionSet)
      ∧ (∀ variableName,
          variableName
            ∈ NormalForm.selectionSetBooleanVariables
                (executableFieldsMergedSelectionSet (leftField :: _leftRest))
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? leftValues (.variable variableName))
      ∧ (∀ variableName,
          variableName
            ∈ NormalForm.selectionSetBooleanVariables
                (executableFieldsMergedSelectionSet (rightField :: _rightRest))
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
      ∧ (∀ variableName,
          variableName
            ∈ Validation.selectionSetVariables
                (executableFieldsMergedSelectionSet (leftField :: _leftRest))
          -> variableName
              ∈ Validation.selectionSetVariables
                  (executableFieldsMergedSelectionSet (rightField :: _rightRest))
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? leftValues variableName)
              (lookupVariableValue? rightValues variableName))
  | _, _ => False

def executableGroupsIncludeWithFuel (schema : Schema) (fuel : Nat)
    (conditionValues leftValues rightValues : VariableValues)
    (leftGroups rightGroups : List (Name × List ExecutableField))
    : Prop :=
  ∀ rightName rightFields,
    (rightName, rightFields) ∈ rightGroups
    -> ∃ leftFields,
        (rightName, leftFields) ∈ leftGroups
        ∧ executableFieldListsIncludeWithFuel schema fuel conditionValues leftValues
            rightValues leftFields rightFields

def completionFieldsIncludeWithFuel (schema : Schema) (fuel : Nat)
    (conditionValues leftValues rightValues : VariableValues) (fieldType : TypeRef)
    (leftFields rightFields : List ExecutableField)
    : Prop :=
  executableFieldListsIncludeWithFuel schema fuel conditionValues leftValues rightValues
    leftFields rightFields
  ∧ (∃ rightField definition rightRest,
      rightFields = rightField :: rightRest
      ∧ schema.lookupField rightField.parentType rightField.fieldName = some definition
      ∧ definition.outputType.namedType = fieldType.namedType)

theorem selectionSetIncludesBoolWithFuel_groups
    (schema : Schema) (fuel : Nat) (parentType : Name)
    (conditionValues leftValues rightValues : VariableValues)
    (leftSelectionSet rightSelectionSet : List Selection)
    (hleftBoolean
      : ∀ variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables leftSelectionSet
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? leftValues (.variable variableName))
    (hrightBoolean
      : ∀ variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables rightSelectionSet
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
    (hcommonLookups
      : ∀ variableName,
          variableName ∈ Validation.selectionSetVariables leftSelectionSet
          -> variableName ∈ Validation.selectionSetVariables rightSelectionSet
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? leftValues variableName)
              (lookupVariableValue? rightValues variableName))
    (hleftNodup : selectionSetArgumentsNodup leftSelectionSet)
    (hrightNodup : selectionSetArgumentsNodup rightSelectionSet)
    (hcheck
      : selectionSetIncludesBoolWithFuel schema (fuel + 1) parentType
          conditionValues leftSelectionSet rightSelectionSet
        = true)
    (runtimeType : Name) (hruntime : runtimeType ∈ schema.getPossibleTypes parentType)
    : executableGroupsIncludeWithFuel schema fuel conditionValues leftValues rightValues
        (collectRuntimeFieldGroups schema leftValues parentType runtimeType
          leftSelectionSet)
        (collectRuntimeFieldGroups schema rightValues parentType runtimeType
          rightSelectionSet) := by
  have hleftArgumentsAndChildrenNodup :=
    collectFields_argumentsAndChildrenNodup schema leftValues parentType
      (.object runtimeType ()) leftSelectionSet hleftNodup
  have hrightArgumentsAndChildrenNodup :=
    collectFields_argumentsAndChildrenNodup schema rightValues parentType
      (.object runtimeType ()) rightSelectionSet hrightNodup
  have hrightGroups := collectRuntimeFieldGroups_eq_of_boolean_agreement schema
    conditionValues rightValues parentType runtimeType rightSelectionSet (by
      intro variableName hvariable
      exact hrightBoolean variableName
        (selectionSetConditionVariables_mem_normalForm rightSelectionSet variableName
          hvariable))
  have hleftGroups := collectRuntimeFieldGroups_eq_of_boolean_agreement schema
    conditionValues leftValues parentType runtimeType leftSelectionSet (by
      intro variableName hvariable
      exact hleftBoolean variableName
        (selectionSetConditionVariables_mem_normalForm leftSelectionSet variableName
          hvariable))
  simp only [selectionSetIncludesBoolWithFuel, selectionSetIncludesAtRuntimeBoolWithFuel,
    executableGroupsIncludeBool, executableGroupIncludedBool, List.all_eq_true] at hcheck
  have hgroups := hcheck runtimeType hruntime
  intro rightName rightFields hright
  have hrightForConditions :
      (rightName, rightFields) ∈
        collectRuntimeFieldGroups schema conditionValues parentType runtimeType
          rightSelectionSet := by
    rw [hrightGroups]
    exact hright
  have hrightMatch := hgroups (rightName, rightFields) hrightForConditions
  rw [List.any_eq_true] at hrightMatch
  rcases hrightMatch with
    ⟨leftGroup, hleft, hmatching⟩
  rcases leftGroup with ⟨leftName, leftFields⟩
  simp only [Bool.and_eq_true] at hmatching
  have hname : leftName = rightName := beq_iff_eq.mp hmatching.1
  have hfieldMatching := hmatching.2
  subst leftName
  have hleftForValues :
      (rightName, leftFields) ∈
        collectRuntimeFieldGroups schema leftValues parentType runtimeType
          leftSelectionSet := by
    rw [← hleftGroups]
    exact hleft
  refine ⟨leftFields, hleftForValues, ?_⟩
  cases leftFields with
  | nil => simp at hfieldMatching
  | cons leftField leftRest =>
      cases rightFields with
      | nil => simp at hfieldMatching
      | cons rightField rightRest =>
          have hrightForValues := hright
          simp only [Bool.and_eq_true] at hfieldMatching
          have hprefix := hfieldMatching.1
          have hdefinition := hfieldMatching.2
          have hparentField := hprefix.1
          have hparent := hparentField.1
          have hfield := hparentField.2
          have harguments := hprefix.2
          have hargumentsEquivalent :=
            (argumentsSyntacticallyEquivalentBool_iff _ _).mp harguments
          refine ⟨beq_iff_eq.mp hparent, beq_iff_eq.mp hfield,
            hargumentsEquivalent, ?_⟩
          generalize hlookup :
              schema.lookupField rightField.parentType rightField.fieldName = lookup
            at hdefinition
          cases lookup with
          | none => simp at hdefinition
          | some definition =>
              have hleftGroup :
                  (rightName, leftField :: leftRest) ∈
                    collectFields schema leftValues parentType (.object runtimeType ())
                      leftSelectionSet := by
                simpa [← collectRuntimeFieldGroups_eq_collectFields_object schema
                  leftValues parentType runtimeType () leftSelectionSet] using
                  hleftForValues
              have hrightGroup :
                  (rightName, rightField :: rightRest) ∈
                    collectFields schema rightValues parentType (.object runtimeType ())
                      rightSelectionSet := by
                simpa [← collectRuntimeFieldGroups_eq_collectFields_object schema
                  rightValues parentType runtimeType () rightSelectionSet] using
                  hrightForValues
              have hleftFieldCollected : leftField ∈ collectedExecutableFields
                    (collectFields schema leftValues parentType
                      (.object runtimeType ()) leftSelectionSet) :=
                collectedExecutableFields_mem_of_group_mem hleftGroup (by simp)
              have hrightFieldCollected : rightField ∈ collectedExecutableFields
                    (collectFields schema rightValues parentType
                      (.object runtimeType ()) rightSelectionSet) :=
                collectedExecutableFields_mem_of_group_mem hrightGroup (by simp)
              have hleftReordered : ArgumentCoercionResult.equivalent
                  (coerceArgumentValues schema leftValues definition.arguments
                    leftField.arguments)
                  (coerceArgumentValues schema leftValues definition.arguments
                    rightField.arguments) :=
                coerceArgumentValues_equivalent_of_equivalent schema leftValues
                  definition.arguments
                  (hleftArgumentsAndChildrenNodup.1 rightName
                    (leftField :: leftRest) hleftGroup leftField (by simp))
                  (hrightArgumentsAndChildrenNodup.1 rightName
                    (rightField :: rightRest) hrightGroup rightField (by simp))
                  hargumentsEquivalent
              have hrightEnvironment : ArgumentCoercionResult.equivalent
                  (coerceArgumentValues schema leftValues definition.arguments
                    rightField.arguments)
                  (coerceArgumentValues schema rightValues definition.arguments
                    rightField.arguments) :=
                coerceArgumentValues_equivalent_of_lookup_agreement schema
                  definition.arguments rightField.arguments (by
                    intro variableName hvariable
                    apply hcommonLookups variableName
                    · apply collectFields_executableFieldVariables schema leftValues
                        parentType (.object runtimeType ()) leftSelectionSet leftField
                        hleftFieldCollected variableName
                      exact Or.inl
                        ((Validation.argumentsVariables_mem_iff_of_equivalent variableName
                          hargumentsEquivalent).2 hvariable)
                    · apply collectFields_executableFieldVariables schema rightValues
                        parentType (.object runtimeType ()) rightSelectionSet rightField
                        hrightFieldCollected variableName
                      exact Or.inl hvariable)
              refine ⟨⟨definition, rfl,
                ArgumentCoercionResult.equivalent_trans hleftReordered
                  hrightEnvironment, ?_⟩,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              cases hcomposite : definition.outputType.isCompositeBool schema with
              | false => trivial
              | true =>
                  simp only [hcomposite, ↓reduceIte, List.all_eq_true] at hdefinition
                  intro childRuntimeType hchild
                  rw [selectionSetIncludesBoolWithFuel.eq_def]
                  exact List.all_eq_true.mpr (hdefinition childRuntimeType hchild)
              · exact hleftArgumentsAndChildrenNodup.1 rightName
                  (leftField :: leftRest) hleftGroup
              · exact hrightArgumentsAndChildrenNodup.1 rightName
                  (rightField :: rightRest) hrightGroup
              · intro field hfield
                exact hleftArgumentsAndChildrenNodup.2 field
                  (collectedExecutableFields_mem_of_group_mem (by
                    exact hleftGroup)
                    hfield)
              · intro field hfield
                exact hrightArgumentsAndChildrenNodup.2 field
                  (collectedExecutableFields_mem_of_group_mem (by
                    exact hrightGroup)
                    hfield)
              · let scopeOperation : Operation := { selectionSet := leftSelectionSet }
                have horigin :=
                  collectFields_executableGroupsSelectionVarsInOperation schema
                    leftValues scopeOperation parentType (.object runtimeType ())
                    leftSelectionSet (by simp [scopeOperation])
                have hgroupOrigin := horigin (rightName, leftField :: leftRest) (by
                  simpa [← collectRuntimeFieldGroups_eq_collectFields_object schema
                    leftValues parentType runtimeType () leftSelectionSet] using
                    hleftForValues)
                intro variableName hvariable
                apply hleftBoolean variableName
                apply executableFieldsSelectionVarsInOperation_merged scopeOperation
                    (leftField :: leftRest) hgroupOrigin variableName
                simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                  using hvariable
              · let scopeOperation : Operation := { selectionSet := rightSelectionSet }
                have horigin :=
                  collectFields_executableGroupsSelectionVarsInOperation schema
                    rightValues scopeOperation parentType (.object runtimeType ())
                    rightSelectionSet (by simp [scopeOperation])
                have hgroupOrigin := horigin (rightName, rightField :: rightRest) (by
                  simpa [← collectRuntimeFieldGroups_eq_collectFields_object schema
                    rightValues parentType runtimeType () rightSelectionSet] using
                    hrightForValues)
                intro variableName hvariable
                apply hrightBoolean variableName
                apply executableFieldsSelectionVarsInOperation_merged scopeOperation
                    (rightField :: rightRest) hgroupOrigin variableName
                simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet]
                  using hvariable
              · intro variableName hleftVariable hrightVariable
                rcases executableFieldsMergedSelectionVariables_exists
                    (leftField :: leftRest) hleftVariable with
                  ⟨leftOrigin, hleftOrigin, hleftOriginVariable⟩
                rcases executableFieldsMergedSelectionVariables_exists
                    (rightField :: rightRest) hrightVariable with
                  ⟨rightOrigin, hrightOrigin, hrightOriginVariable⟩
                apply hcommonLookups variableName
                · apply collectFields_executableFieldVariables schema leftValues
                    parentType (.object runtimeType ()) leftSelectionSet leftOrigin
                  · exact collectedExecutableFields_mem_of_group_mem hleftGroup
                      hleftOrigin
                  · exact Or.inr hleftOriginVariable
                · apply collectFields_executableFieldVariables schema rightValues
                    parentType (.object runtimeType ()) rightSelectionSet rightOrigin
                  · exact collectedExecutableFields_mem_of_group_mem hrightGroup
                      hrightOrigin
                  · exact Or.inr hrightOriginVariable

theorem resultCombine_eq_ok_zero
    {left : Result α} {right : Result β} {combine : α -> β -> γ} {result : γ}
    (hresult : Result.combine combine left right = .ok (result, 0))
    : ∃ leftValue rightValue,
        left = .ok (leftValue, 0)
        ∧ right = .ok (rightValue, 0)
        ∧ combine leftValue rightValue = result := by
  cases left with
  | error leftErrors =>
      cases right <;> simp [Result.combine] at hresult
  | ok leftResult =>
      rcases leftResult with ⟨leftValue, leftErrors⟩
      cases right with
      | error rightErrors => simp [Result.combine] at hresult
      | ok rightResult =>
          rcases rightResult with ⟨rightValue, rightErrors⟩
          simp only [Result.combine, Except.ok.injEq, Prod.mk.injEq] at hresult
          have hleftErrors : leftErrors = 0 := by omega
          have hrightErrors : rightErrors = 0 := by omega
          subst leftErrors
          subst rightErrors
          exact ⟨leftValue, rightValue, rfl, rfl, hresult.1⟩

theorem executeAnnotatedCollectedFields_group_result
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (responseFields : List AnnotatedResponseField)
    (hresult
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          source groups
        = .ok (responseFields, 0))
    {responseName : Name} {fields : List ExecutableField}
    (hgroup : (responseName, fields) ∈ groups)
    : ∃ groupResponseFields,
        executeQueryAnnotatedField schema resolvers variableValues fuel source
            responseName fields
          = .ok (groupResponseFields, 0)
        ∧ ∀ field, field ∈ groupResponseFields -> field ∈ responseFields := by
  induction groups generalizing responseFields with
  | nil => simp at hgroup
  | cons group rest ih =>
      rcases group with ⟨headName, headFields⟩
      simp only [executeQueryAnnotatedCollectedFields] at hresult
      rcases resultCombine_eq_ok_zero hresult with
        ⟨headResponseFields, tailResponseFields, hhead, htail, happend⟩
      rcases List.mem_cons.mp hgroup with hsame | hrest
      · injection hsame with hname hfields
        subst headName
        subst headFields
        refine ⟨headResponseFields, hhead, ?_⟩
        intro field hfield
        rw [← happend]
        exact List.mem_append_left tailResponseFields hfield
      · rcases ih tailResponseFields htail hrest with
          ⟨groupResponseFields, hgroupResult, hmembers⟩
        refine ⟨groupResponseFields, hgroupResult, ?_⟩
        intro field hfield
        rw [← happend]
        exact List.mem_append_right headResponseFields (hmembers field hfield)

theorem executeAnnotatedCollectedFields_field_origin
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (responseFields : List AnnotatedResponseField)
    (hresult
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          source groups
        = .ok (responseFields, 0))
    {responseField : AnnotatedResponseField} (hfield : responseField ∈ responseFields)
    : ∃ responseName fields groupResponseFields,
        (responseName, fields) ∈ groups
        ∧ executeQueryAnnotatedField schema resolvers variableValues fuel source
            responseName fields
          = .ok (groupResponseFields, 0)
        ∧ responseField ∈ groupResponseFields := by
  induction groups generalizing responseFields with
  | nil =>
      simp [executeQueryAnnotatedCollectedFields] at hresult
      subst responseFields
      simp at hfield
  | cons group rest ih =>
      rcases group with ⟨headName, headFields⟩
      simp only [executeQueryAnnotatedCollectedFields] at hresult
      rcases resultCombine_eq_ok_zero hresult with
        ⟨headResponseFields, tailResponseFields, hhead, htail, happend⟩
      rw [← happend] at hfield
      rcases List.mem_append.mp hfield with hheadMember | htailMember
      · exact ⟨headName, headFields, headResponseFields, by simp, hhead, hheadMember⟩
      · rcases ih tailResponseFields htail htailMember with
          ⟨responseName, fields, groupResponseFields, hgroup, hgroupResult,
            hgroupMember⟩
        exact ⟨responseName, fields, groupResponseFields,
          List.mem_cons_of_mem _ hgroup, hgroupResult, hgroupMember⟩

def resultErrorPositive (result : Result α) : Prop :=
  ∀ errors, result = .error errors -> 0 < errors

theorem annotatedExecution_error_positive_all
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ fuel source groups,
        resultErrorPositive
          (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
            source groups))
      ∧ (∀ fuel source responseName fields,
          resultErrorPositive
            (executeQueryAnnotatedField schema resolvers variableValues fuel source
              responseName fields))
      ∧ (∀ fuel fieldType fields value,
          resultErrorPositive
            (completeAnnotatedResponseValue schema resolvers variableValues fuel fieldType
              fields value))
      ∧ (∀ fuel itemType fields values,
          resultErrorPositive
            (completeAnnotatedResponseValueList schema resolvers variableValues fuel
              itemType fields values)) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  all_goals
    simp_all [resultErrorPositive, executeQueryAnnotatedCollectedFields,
      executeQueryAnnotatedField, completeAnnotatedResponseValue,
      completeAnnotatedResponseValueList, completeNonNullAnnotatedResponseValue,
      singleAnnotatedResponseFieldResult, catchAnnotatedResponseBubbleAsNull]
  case case2 =>
    intro fuel source responseName fields rest hhead htail errors herror
    cases hheadResult : executeQueryAnnotatedField schema resolvers variableValues fuel
        source responseName fields <;>
      cases htailResult : executeQueryAnnotatedCollectedFields schema resolvers
        variableValues fuel source rest <;>
      simp_all [Result.combine] <;> omega
  case case6 =>
    intro source responseName field definition hlookup hcoerce errors herror
    generalize htype : definition.outputType = outputType at herror
    cases outputType <;> simp at herror <;> omega
  case case7 =>
    intro source responseName field definition hlookup coercedArguments hcoerce hresolve
      errors herror
    generalize htype : definition.outputType = outputType at herror
    cases outputType <;> simp at herror <;> omega
  case case8 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      resolved hresolve hcomplete errors herror
    cases hcompleted : completeAnnotatedResponseValue schema resolvers variableValues fuel
        definition.outputType (field :: rest) resolved <;>
      simp_all
  case case10 =>
    intro fuel inner fields value hfuel hinner errors herror
    generalize hcompleted :
        completeAnnotatedResponseValue schema resolvers variableValues fuel inner fields
          value = completed at herror
    cases completed with
    | error completedErrors =>
        simp only at herror
        injection herror with herrors
        subst errors
        exact hinner completedErrors hcompleted
    | ok completed =>
        rcases completed with ⟨outcome, completedErrors⟩
        cases outcome with
        | null =>
            cases completedErrors <;>
              simp at herror <;> omega
        | scalar value => simp at herror
        | object runtimeType fields =>
            simp at herror
        | list values => simp at herror
  case case14 =>
    intro fuel parentType fields runtimeType ref hincludes hchild errors herror
    cases hcompleted : executeQueryAnnotatedCollectedFields schema resolvers variableValues
        fuel (.object runtimeType ref)
        (collectSubfields schema variableValues runtimeType (.object runtimeType ref) fields) <;>
      simp_all
  case case16 =>
    intro fuel inner fields values hvalues errors herror
    cases hcompleted : completeAnnotatedResponseValueList schema resolvers variableValues
        fuel inner fields values <;>
      simp_all
  case case20 =>
    intro fuel itemType fields value values hhead htail errors herror
    cases hheadResult : completeAnnotatedResponseValue schema resolvers variableValues fuel
        itemType fields value <;>
      cases htailResult : completeAnnotatedResponseValueList schema resolvers variableValues
        fuel itemType fields values <;>
      simp_all [Result.combine] <;> omega

private theorem executeAnnotatedCollectedFields_error_positive
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : resultErrorPositive
        (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel source
          groups) :=
  (annotatedExecution_error_positive_all schema resolvers variableValues).1 fuel source
    groups

theorem executeQueryAnnotatedCollectedFields_error_positive
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField)) (errors : Nat)
    (hresult
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          source groups
        = .error errors)
    : 0 < errors :=
  executeAnnotatedCollectedFields_error_positive schema resolvers variableValues fuel
    source groups errors hresult

theorem completeNonNull_eq_ok_zero
    {completed : Result AnnotatedResponseValue} {value : AnnotatedResponseValue}
    (hresult : completeNonNullAnnotatedResponseValue completed = .ok (value, 0))
    : completed = .ok (value, 0) ∧ value ≠ .null := by
  cases completed with
  | error errors => simp [completeNonNullAnnotatedResponseValue] at hresult
  | ok result =>
      rcases result with ⟨outcome, errors⟩
      cases outcome with
      | null => simp [completeNonNullAnnotatedResponseValue] at hresult
      | scalar scalarValue =>
          simp only [completeNonNullAnnotatedResponseValue, Except.ok.injEq,
            Prod.mk.injEq] at hresult
          rcases hresult with ⟨rfl, rfl⟩
          exact ⟨rfl, by simp⟩
      | object runtimeType fields =>
          simp only [completeNonNullAnnotatedResponseValue, Except.ok.injEq,
            Prod.mk.injEq] at hresult
          rcases hresult with ⟨rfl, rfl⟩
          exact ⟨rfl, by simp⟩
      | list values =>
          simp only [completeNonNullAnnotatedResponseValue, Except.ok.injEq,
            Prod.mk.injEq] at hresult
          rcases hresult with ⟨rfl, rfl⟩
          exact ⟨rfl, by simp⟩

theorem catchAnnotated_eq_ok_zero_of_error_positive
    {completed : Result α} {wrap : α -> AnnotatedResponseValue}
    {value : AnnotatedResponseValue}
    (hpositive : resultErrorPositive completed)
    (hresult : catchAnnotatedResponseBubbleAsNull wrap completed = .ok (value, 0))
    : ∃ outcome, completed = .ok (outcome, 0) ∧ value = wrap outcome := by
  cases completed with
  | error errors =>
      simp only [catchAnnotatedResponseBubbleAsNull, Except.ok.injEq,
        Prod.mk.injEq] at hresult
      have hzero : errors = 0 := hresult.2
      subst errors
      exact False.elim ((Nat.lt_irrefl 0) (hpositive 0 rfl))
  | ok result =>
      rcases result with ⟨outcome, errors⟩
      simp only [catchAnnotatedResponseBubbleAsNull, Except.ok.injEq,
        Prod.mk.injEq] at hresult
      rcases hresult with ⟨hvalue, herrors⟩
      subst value
      subst errors
      exact ⟨outcome, rfl, rfl⟩

theorem executeAnnotatedField_ok_zero_decompose
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef) (responseName : Name)
    (fields : List ExecutableField) (responseFields : List AnnotatedResponseField)
    (hresult
      : executeQueryAnnotatedField schema resolvers variableValues fuel source
          responseName fields
        = .ok (responseFields, 0))
    : ∃ completionFuel field rest definition resolved responseValue,
        fuel = completionFuel + 1
        ∧ fields = field :: rest
        ∧ schema.lookupField field.parentType field.fieldName = some definition
        ∧ coerceAndResolveFieldValue schema resolvers variableValues definition
            field.parentType field.fieldName field.arguments source
          = some resolved
        ∧ completeAnnotatedResponseValue schema resolvers variableValues
            completionFuel definition.outputType (field :: rest) resolved
          = .ok (responseValue, 0)
        ∧ responseFields
          = [.resolved responseName
              (resolvedFieldProvenance schema variableValues definition field)
              responseValue] := by
  cases fields with
  | nil => simp [executeQueryAnnotatedField] at hresult
  | cons field rest =>
      cases fuel with
      | zero => simp [executeQueryAnnotatedField] at hresult
      | succ completionFuel =>
          cases hlookup : schema.lookupField field.parentType field.fieldName with
          | none => simp [executeQueryAnnotatedField, hlookup] at hresult
          | some definition =>
              cases hcoerce
                    : coerceArgumentValues schema variableValues
                        definition.arguments field.arguments with
              | error =>
                  generalize htype : definition.outputType = outputType at hresult
                  cases outputType <;>
                    simp [executeQueryAnnotatedField, hlookup, hcoerce, htype,
                      singleAnnotatedResponseFieldResult] at hresult
              | success coercedArguments =>
                  cases hresolve
                        : resolveFieldValue resolvers field.parentType
                            field.fieldName coercedArguments source with
                  | none =>
                      generalize htype : definition.outputType = outputType at hresult
                      cases outputType <;>
                        simp [executeQueryAnnotatedField, hlookup, hcoerce, hresolve,
                          htype, singleAnnotatedResponseFieldResult] at hresult
                  | some resolved =>
                      cases hcomplete
                            : completeAnnotatedResponseValue schema resolvers
                                variableValues completionFuel definition.outputType
                                (field :: rest) resolved with
                      | error errors =>
                          simp [executeQueryAnnotatedField, hlookup, hcoerce, hresolve,
                            hcomplete, singleAnnotatedResponseFieldResult] at hresult
                      | ok completed =>
                          rcases completed with ⟨responseValue, errors⟩
                          simp only [executeQueryAnnotatedField, hlookup, hcoerce,
                            hresolve, hcomplete, singleAnnotatedResponseFieldResult,
                            Except.ok.injEq, Prod.mk.injEq] at hresult
                          rcases hresult with ⟨rfl, rfl⟩
                          refine ⟨completionFuel, field, rest, definition, resolved,
                            responseValue, rfl, rfl, hlookup, ?_, hcomplete, rfl⟩
                          simp [coerceAndResolveFieldValue, hcoerce, hresolve]

private def recursiveChildExecutionSound
    (schema : Schema) (resolvers : Resolvers ObjectRef) (inclusionFuel : Nat)
    (conditionValues leftValues rightValues : VariableValues)
    : Prop :=
  ∀ (parentType runtimeType : Name) (ref : ObjectRef)
    (leftSelectionSet rightSelectionSet : List Selection)
    (executionFuel : Nat)
    (leftResponseFields rightResponseFields : List AnnotatedResponseField),
    runtimeType ∈ schema.getPossibleTypes parentType
    -> selectionSetIncludesBoolWithFuel schema inclusionFuel parentType
          conditionValues leftSelectionSet rightSelectionSet
        = true
    -> (∀ variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables leftSelectionSet
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? leftValues (.variable variableName))
    -> (∀ variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables rightSelectionSet
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
    -> (∀ variableName,
          variableName ∈ Validation.selectionSetVariables leftSelectionSet
          -> variableName ∈ Validation.selectionSetVariables rightSelectionSet
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? leftValues variableName)
              (lookupVariableValue? rightValues variableName))
    -> selectionSetArgumentsNodup leftSelectionSet
    -> selectionSetArgumentsNodup rightSelectionSet
    -> executeQueryAnnotatedCollectedFields schema resolvers leftValues
          executionFuel
          (.object runtimeType ref)
          (collectFields schema leftValues parentType (.object runtimeType ref)
            leftSelectionSet)
        = .ok (leftResponseFields, 0)
    -> executeQueryAnnotatedCollectedFields schema resolvers rightValues
          executionFuel
          (.object runtimeType ref)
          (collectFields schema rightValues parentType (.object runtimeType ref)
            rightSelectionSet)
        = .ok (rightResponseFields, 0)
    -> responseValueIncludes (.object runtimeType leftResponseFields)
        (.object runtimeType rightResponseFields)

set_option maxHeartbeats 800000 in
private theorem annotatedExecution_inclusion_all
    (schema : Schema) (resolvers : Resolvers ObjectRef) (inclusionFuel : Nat)
    (conditionValues leftValues : VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (childSound
      : ∀ rightValues,
          recursiveChildExecutionSound schema resolvers inclusionFuel conditionValues
            leftValues rightValues)
    : (∀ (_executionFuel : Nat) (_source : ResolverValue ObjectRef)
          (_groups : List (Name × List ExecutableField)),
        True)
      ∧ (∀ executionFuel source responseName leftFields,
          ∀ rightValues rightFields leftResponseFields rightResponseFields,
            executableFieldListsIncludeWithFuel schema inclusionFuel
              conditionValues leftValues rightValues leftFields rightFields
            -> executeQueryAnnotatedField schema resolvers leftValues executionFuel
                  source responseName leftFields
                = .ok (leftResponseFields, 0)
            -> executeQueryAnnotatedField schema resolvers rightValues executionFuel
                  source responseName rightFields
                = .ok (rightResponseFields, 0)
            -> responseValueIncludes (.object "" leftResponseFields)
                (.object "" rightResponseFields))
      ∧ (∀ executionFuel fieldType leftFields value,
          ∀ rightValues rightFields leftResponseValue rightResponseValue,
            completionFieldsIncludeWithFuel schema inclusionFuel conditionValues
              leftValues rightValues fieldType leftFields rightFields
            -> completeAnnotatedResponseValue schema resolvers leftValues executionFuel
                  fieldType leftFields value
                = .ok (leftResponseValue, 0)
            -> completeAnnotatedResponseValue schema resolvers rightValues executionFuel
                  fieldType rightFields value
                = .ok (rightResponseValue, 0)
            -> responseValueIncludes leftResponseValue rightResponseValue)
      ∧ (∀ executionFuel itemType leftFields values,
          ∀ rightValues rightFields leftResponseValues rightResponseValues,
            completionFieldsIncludeWithFuel schema inclusionFuel conditionValues
              leftValues rightValues itemType leftFields rightFields
            -> completeAnnotatedResponseValueList schema resolvers leftValues
                  executionFuel itemType leftFields values
                = .ok (leftResponseValues, 0)
            -> completeAnnotatedResponseValueList schema resolvers rightValues
                  executionFuel itemType rightFields values
                = .ok (rightResponseValues, 0)
            -> responseValueIncludes (.list leftResponseValues)
                (.list rightResponseValues)) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers leftValues
  all_goals
    simp_all [executableFieldListsIncludeWithFuel, completionFieldsIncludeWithFuel,
      executeQueryAnnotatedField, completeAnnotatedResponseValue,
      completeAnnotatedResponseValueList, responseValueIncludes,
      completeNonNullAnnotatedResponseValue, singleAnnotatedResponseFieldResult,
      catchAnnotatedResponseBubbleAsNull, Result.combine]
  case case6 =>
    intro source responseName field rest errors definition hlookup hresolve rightValues
      rightFields leftResponseFields rightResponseFields hfields hleft hright
    generalize htype : definition.outputType = outputType at hleft
    cases outputType <;> simp at hleft <;> omega
  case case11 =>
    intros
    subst_vars
    exact responseValueIncludes_refl _
  case case13 =>
    intros
    subst_vars
    exact responseValueIncludes_refl _
  case case7 =>
    intro source responseName field rest errors definition hlookup coercedArguments
      hcoerce hresolve rightValues rightFields leftResponseFields rightResponseFields
      hfields hleft hright
    generalize htype : definition.outputType = outputType at hleft
    cases outputType <;> simp at hleft <;> omega
  case case8 =>
    intro source responseName field rest executionFuel definition hlookup coercedArguments
      hcoerce resolved hresolve completeIH rightValues rightFields leftResponseFields
      rightResponseFields hfields hleft hright
    cases rightFields with
    | nil => simp at hfields
    | cons rightField rightRest =>
        simp only at hfields
        rcases hfields with ⟨hparent, hfield, harguments,
          ⟨rightDefinition, hrightLookup, hcoerced, hchildren⟩, hleftArguments,
          hrightArguments, hleftChildren, hrightChildren, hleftBooleanChild,
          hrightBooleanChild, hcommonChild⟩
        have hrightLookup' :
            schema.lookupField rightField.parentType rightField.fieldName
              = some definition := by
          simpa [← hparent, ← hfield] using hlookup
        have hdefinition : rightDefinition = definition := by
          rw [hrightLookup'] at hrightLookup
          exact (Option.some.inj hrightLookup).symm
        subst rightDefinition
        have hleftSuccess :
            (coerceArgumentValues schema leftValues definition.arguments
              field.arguments).isSuccess = true := by
          simp [hcoerce]
        have hrightSuccess :
            (coerceArgumentValues schema rightValues definition.arguments
              rightField.arguments).isSuccess = true := by
          rw [← ArgumentCoercionResult.isSuccess_eq_of_equivalent hcoerced]
          exact hleftSuccess
        rcases ArgumentCoercionResult.exists_success_of_isSuccess hrightSuccess with
          ⟨rightCoercedArguments, hrightCoercion⟩
        have hcoercedArguments :
            CoercedArgument.argumentsEquivalent coercedArguments
              rightCoercedArguments := by
          simpa [ArgumentCoercionResult.equivalent, hcoerce,
            hrightCoercion] using hcoerced
        have hrightResolve :
            coerceAndResolveFieldValue schema resolvers rightValues definition
                rightField.parentType rightField.fieldName rightField.arguments source
              = some resolved := by
          unfold coerceAndResolveFieldValue
          simp only [hrightCoercion]
          unfold resolveFieldValue at hresolve ⊢
          calc
            resolvers.resolve rightField.parentType rightField.fieldName
                rightCoercedArguments source =
                resolvers.resolve field.parentType field.fieldName
                  rightCoercedArguments source := by rw [hparent, hfield]
            _ = resolvers.resolve field.parentType field.fieldName
                coercedArguments source :=
              (resolvers.resolve_argumentsEquivalent field.parentType field.fieldName
                _ _ source hcoercedArguments).symm
            _ = some resolved := hresolve
        have hrightResolved :
            resolveFieldValue resolvers rightField.parentType rightField.fieldName
                rightCoercedArguments source = some resolved := by
          simpa [coerceAndResolveFieldValue, hrightCoercion] using hrightResolve
        generalize hleftCompleted :
            completeAnnotatedResponseValue schema resolvers leftValues executionFuel
              definition.outputType (field :: rest) resolved = leftCompleted at hleft
        cases leftCompleted with
        | error leftErrors => cases hleft
        | ok leftResult =>
            rcases leftResult with ⟨leftValue, leftErrors⟩
            simp only [Except.ok.injEq, Prod.mk.injEq] at hleft
            rcases hleft with ⟨hleftFields, hleftErrors⟩
            subst leftResponseFields
            subst leftErrors
            simp only [executeQueryAnnotatedField, hrightLookup', hrightCoercion,
              hrightResolved] at hright
            generalize hrightCompleted :
                completeAnnotatedResponseValue schema resolvers rightValues executionFuel
                  definition.outputType (rightField :: rightRest) resolved = rightCompleted
              at hright
            cases rightCompleted with
            | error rightErrors => cases hright
            | ok rightResult =>
                rcases rightResult with ⟨rightValue, rightErrors⟩
                rcases hright with ⟨hrightFields, hrightErrors⟩
                have hvalueIncludes := completeIH rightValues
                  (rightField :: rightRest) leftValue rightValue
                  ⟨hparent, hfield, harguments,
                    ⟨definition, hrightLookup', hcoerced, hchildren⟩, hleftArguments,
                    hrightArguments, hleftChildren, hrightChildren,
                    hleftBooleanChild, hrightBooleanChild, hcommonChild⟩
                  rightField rightRest rfl definition hrightLookup' rfl
                  hleftCompleted hrightCompleted
                intro rightName rightCall requestedValue hmember
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
                injection hmember with hname hcall hvalue
                subst rightName
                subst rightCall
                subst requestedValue
                refine ⟨responseName,
                  resolvedFieldProvenance schema leftValues definition field, leftValue,
                  by simp, rfl, ?_, hvalueIncludes⟩
                exact (sameFieldProvenance_iff _ _).mpr
                  ⟨hparent, hfield, harguments⟩
  case case10 =>
    intro executionFuel inner fields value hfuel innerIH rightValues rightFields
      leftResponseValue rightResponseValue hfields rightField rightRest
      hrightFields definition hlookup hnamed hleft hright
    subst rightFields
    have hleftInner := completeNonNull_eq_ok_zero hleft
    have hrightInner := completeNonNull_eq_ok_zero hright
    exact innerIH rightValues (rightField :: rightRest) leftResponseValue
      rightResponseValue hfields rightField rightRest rfl definition hlookup
      (by simpa [TypeRef.namedType] using hnamed) hleftInner.1 hrightInner.1
  case case14 =>
    intro executionFuel parentType fields runtimeType ref hincludes rightValues rightFields
      leftResponseValue rightResponseValue hfields rightField rightRest
      hrightFields definition hlookup hnamed hleft hright
    subst rightFields
    have hruntime : runtimeType ∈ schema.getPossibleTypes parentType :=
      List.contains_iff_mem.mp hincludes
    have hparent : definition.outputType.namedType = parentType := by
      simpa [TypeRef.namedType] using hnamed
    subst parentType
    cases fields with
    | nil => simp at hfields
    | cons leftField leftRest =>
      simp only at hfields
      rcases hfields with ⟨hleftParent, hleftField, harguments,
        ⟨checkerDefinition, hcheckerLookup, hcoerced, hcheck⟩, hleftArguments,
        hrightArguments, hleftChildren, hrightChildren, hleftBooleanChild,
        hrightBooleanChild, hcommonChild⟩
      have hcheckerDefinition : checkerDefinition = definition := by
        rw [hlookup] at hcheckerLookup
        exact (Option.some.inj hcheckerLookup).symm
      subst checkerDefinition
      have hcomposite : definition.outputType.isCompositeBool schema = true := by
        exact isCompositeBool_eq_true_of_typeIncludesObjectBool schema
          definition.outputType.namedType runtimeType hincludes
      have hselection := hcheck hcomposite runtimeType hruntime
      have hleftCompleted := catchAnnotated_eq_ok_zero_of_error_positive
        (executeAnnotatedCollectedFields_error_positive schema resolvers leftValues
          executionFuel (.object runtimeType ref)
          (collectFields schema leftValues runtimeType (.object runtimeType ref)
            (mergedFieldSelectionSet (leftField :: leftRest)))) hleft
      have hrightCompleted := catchAnnotated_eq_ok_zero_of_error_positive
        (executeAnnotatedCollectedFields_error_positive schema resolvers rightValues
          executionFuel (.object runtimeType ref)
          (collectFields schema rightValues runtimeType (.object runtimeType ref)
            (mergedFieldSelectionSet (rightField :: rightRest)))) hright
      rcases hleftCompleted with ⟨leftFields, hleftFields, rfl⟩
      rcases hrightCompleted with ⟨rightFields, hrightFields, rfl⟩
      have hobject := SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
        hschema definition.outputType.namedType runtimeType hruntime
      have hobjectBool :=
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
          schema hobject
      have hself :=
        NormalForm.GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
          schema hobjectBool
      have hruntimeSelf : runtimeType ∈ schema.getPossibleTypes runtimeType :=
        List.contains_iff_mem.mp hself
      have hleftMergedNodup : selectionSetArgumentsNodup
          (mergedFieldSelectionSet (leftField :: leftRest)) :=
        selectionSetArgumentsNodup_mergedFieldSelectionSet _ (by
          intro field hfield
          rcases List.mem_cons.mp hfield with rfl | hfield
          · exact hleftChildren.1
          · exact hleftChildren.2 field hfield)
      have hrightMergedNodup : selectionSetArgumentsNodup
          (mergedFieldSelectionSet (rightField :: rightRest)) :=
        selectionSetArgumentsNodup_mergedFieldSelectionSet _ (by
          intro field hfield
          rcases List.mem_cons.mp hfield with rfl | hfield
          · exact hrightChildren.1
          · exact hrightChildren.2 field hfield)
      apply childSound rightValues runtimeType runtimeType ref
        (mergedFieldSelectionSet (leftField :: leftRest))
        (mergedFieldSelectionSet (rightField :: rightRest)) executionFuel leftFields
        rightFields
      · exact hruntimeSelf
      · simpa using hselection
      · simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet] using
          hleftBooleanChild
      · simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet] using
          hrightBooleanChild
      · simpa [executableFieldsMergedSelectionSet_eq_mergedFieldSelectionSet] using
          hcommonChild
      · exact hleftMergedNodup
      · exact hrightMergedNodup
      · simpa [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
          using hleftFields
      · simpa [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
          using hrightFields
  case case16 =>
    intro executionFuel inner fields values listIH rightValues rightFields
      leftResponseValue rightResponseValue hfields rightField rightRest
      hrightFields definition hlookup hnamed hleft hright
    subst rightFields
    have hleftCompleted := catchAnnotated_eq_ok_zero_of_error_positive
      ((annotatedExecution_error_positive_all schema resolvers leftValues).2.2.2
        executionFuel inner fields values) hleft
    have hrightCompleted := catchAnnotated_eq_ok_zero_of_error_positive
      ((annotatedExecution_error_positive_all schema resolvers rightValues).2.2.2
        executionFuel inner (rightField :: rightRest) values) hright
    rcases hleftCompleted with ⟨leftValuesResult, hleftValues, rfl⟩
    rcases hrightCompleted with ⟨rightValuesResult, hrightValues, rfl⟩
    simpa [responseValueIncludes] using
      listIH rightValues (rightField :: rightRest) leftValuesResult
        rightValuesResult hfields rightField rightRest rfl definition hlookup
        (by simpa [TypeRef.namedType] using hnamed) hleftValues hrightValues
  case case20 =>
    intro executionFuel itemType fields value values headIH tailIH rightValues
      rightFields leftResponseValues rightResponseValues hfields rightField
      rightRest hrightFields definition hlookup hnamed hleft hright
    subst rightFields
    rcases resultCombine_eq_ok_zero hleft with
      ⟨leftHead, leftTail, hleftHead, hleftTail, hleftCons⟩
    rcases resultCombine_eq_ok_zero hright with
      ⟨rightHead, rightTail, hrightHead, hrightTail, hrightCons⟩
    have hheadIncludes := headIH rightValues (rightField :: rightRest) leftHead
      rightHead hfields rightField rightRest rfl definition hlookup hnamed
      hleftHead hrightHead
    have htailIncludes := tailIH rightValues (rightField :: rightRest) leftTail
      rightTail hfields rightField rightRest rfl definition hlookup hnamed
      hleftTail hrightTail
    rw [← hleftCons, ← hrightCons]
    intro index requested hmember
    cases index with
    | zero =>
        simp at hmember
        subst requested
        exact ⟨leftHead, by simp, hheadIncludes⟩
    | succ index =>
        simp at hmember
        rcases htailIncludes index requested hmember with
          ⟨leftValue, hleftMember, hincludes⟩
        exact ⟨leftValue, by simpa using hleftMember, hincludes⟩

private theorem recursiveChildExecutionSound_proved
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ inclusionFuel conditionValues leftValues rightValues,
        recursiveChildExecutionSound schema resolvers inclusionFuel conditionValues
          leftValues rightValues := by
  intro inclusionFuel
  induction inclusionFuel with
  | zero =>
      intro conditionValues leftValues rightValues parentType runtimeType ref leftSelectionSet
        rightSelectionSet executionFuel leftResponseFields rightResponseFields hruntime
        hcheck hleftBoolean hrightBoolean _hcommonLookups hleftNodup hrightNodup hleft
        hright
      simp only [selectionSetIncludesBoolWithFuel, selectionSetIncludesAtRuntimeBoolWithFuel,
        List.all_eq_true] at hcheck
      have hregion := hcheck runtimeType hruntime
      have hrightGroupsLeft : collectRuntimeFieldGroups schema conditionValues parentType
          runtimeType rightSelectionSet = [] := List.isEmpty_iff.mp hregion
      have hrightGroupsEq := collectRuntimeFieldGroups_eq_of_boolean_agreement schema
        conditionValues rightValues parentType runtimeType rightSelectionSet
        (by
          intro variableName hvariable
          exact hrightBoolean variableName
            (selectionSetConditionVariables_mem_normalForm rightSelectionSet
              variableName hvariable))
      have hrightGroups : collectRuntimeFieldGroups schema rightValues parentType
          runtimeType rightSelectionSet = [] := by
        rw [← hrightGroupsEq]
        exact hrightGroupsLeft
      rw [collectRuntimeFieldGroups_eq_collectFields_object schema rightValues
        parentType runtimeType ref rightSelectionSet] at hrightGroups
      rw [hrightGroups] at hright
      simp only [executeQueryAnnotatedCollectedFields, Except.ok.injEq,
        Prod.mk.injEq] at hright
      rcases hright with ⟨rfl, _hzero⟩
      simp only [responseValueIncludes]
      intro rightName rightCall rightValue hmember
      simp at hmember
  | succ inclusionFuel ih =>
      intro conditionValues leftValues rightValues parentType runtimeType ref leftSelectionSet
        rightSelectionSet executionFuel leftResponseFields rightResponseFields hruntime
        hcheck hleftBoolean hrightBoolean hcommonLookups hleftNodup hrightNodup hleft
        hright
      have hgroups : executableGroupsIncludeWithFuel schema inclusionFuel conditionValues
          leftValues rightValues
          (collectFields schema leftValues parentType (.object runtimeType ref)
            leftSelectionSet)
          (collectFields schema rightValues parentType (.object runtimeType ref)
            rightSelectionSet) := by
        have hcanonical := selectionSetIncludesBoolWithFuel_groups schema inclusionFuel
          parentType conditionValues leftValues rightValues leftSelectionSet
          rightSelectionSet hleftBoolean hrightBoolean
          hcommonLookups hleftNodup hrightNodup hcheck runtimeType hruntime
        rw [collectRuntimeFieldGroups_eq_collectFields_object schema leftValues parentType
          runtimeType ref leftSelectionSet,
          collectRuntimeFieldGroups_eq_collectFields_object schema rightValues parentType
            runtimeType ref rightSelectionSet] at hcanonical
        exact hcanonical
      have hfieldSound :=
        (annotatedExecution_inclusion_all schema resolvers inclusionFuel conditionValues
          leftValues
          hschema (by
            intro nestedRightValues
            exact ih conditionValues leftValues nestedRightValues)).2.1
      simp only [responseValueIncludes]
      intro rightName rightCall rightValue hrightMember
      rcases executeAnnotatedCollectedFields_field_origin schema resolvers rightValues
          executionFuel (.object runtimeType ref)
          (collectFields schema rightValues parentType (.object runtimeType ref)
            rightSelectionSet) rightResponseFields hright hrightMember with
        ⟨responseName, rightFields, rightGroupResponseFields, hrightGroup,
          hrightGroupResult, hrightGroupMember⟩
      rcases hgroups responseName rightFields hrightGroup with
        ⟨leftFields, hleftGroup, hfieldIncludes⟩
      rcases executeAnnotatedCollectedFields_group_result schema resolvers leftValues
          executionFuel (.object runtimeType ref)
          (collectFields schema leftValues parentType (.object runtimeType ref)
            leftSelectionSet) leftResponseFields hleft hleftGroup with
        ⟨leftGroupResponseFields, hleftGroupResult, hleftGroupMembers⟩
      have hgroupIncludes := hfieldSound executionFuel (.object runtimeType ref)
        responseName leftFields rightValues rightFields leftGroupResponseFields
        rightGroupResponseFields hfieldIncludes hleftGroupResult
        hrightGroupResult
      unfold responseValueIncludes at hgroupIncludes
      rcases hgroupIncludes rightName rightCall rightValue hrightGroupMember with
        ⟨leftName, leftCall, leftValue, hleftMember, hname, hcall, hvalue⟩
      exact ⟨leftName, leftCall, leftValue, hleftGroupMembers _ hleftMember,
        hname, hcall, hvalue⟩

theorem selectionSetIncludesBoolWithFuel_annotated_execution
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (inclusionFuel : Nat) (conditionValues leftValues rightValues : VariableValues)
    (parentType runtimeType : Name) (ref : ObjectRef)
    (leftSelectionSet rightSelectionSet : List Selection)
    (executionFuel : Nat)
    (leftResponseFields rightResponseFields : List AnnotatedResponseField)
    (hruntime : runtimeType ∈ schema.getPossibleTypes parentType)
    (hcheck
      : selectionSetIncludesBoolWithFuel schema inclusionFuel parentType
          conditionValues leftSelectionSet rightSelectionSet
        = true)
    (hleftBoolean
      : ∀ variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables leftSelectionSet
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? leftValues (.variable variableName))
    (hrightBoolean
      : ∀ variableName,
          variableName ∈ NormalForm.selectionSetBooleanVariables rightSelectionSet
          -> inputValueBoolean? conditionValues (.variable variableName)
              = inputValueBoolean? rightValues (.variable variableName))
    (hcommonLookups
      : ∀ variableName,
          variableName ∈ Validation.selectionSetVariables leftSelectionSet
          -> variableName ∈ Validation.selectionSetVariables rightSelectionSet
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? leftValues variableName)
              (lookupVariableValue? rightValues variableName))
    (hleftNodup : selectionSetArgumentsNodup leftSelectionSet)
    (hrightNodup : selectionSetArgumentsNodup rightSelectionSet)
    (hleft
      : executeQueryAnnotatedCollectedFields schema resolvers leftValues
          executionFuel (.object runtimeType ref)
          (collectFields schema leftValues parentType (.object runtimeType ref)
            leftSelectionSet)
        = .ok (leftResponseFields, 0))
    (hright
      : executeQueryAnnotatedCollectedFields schema resolvers rightValues
          executionFuel (.object runtimeType ref)
          (collectFields schema rightValues parentType (.object runtimeType ref)
            rightSelectionSet)
        = .ok (rightResponseFields, 0))
    : responseValueIncludes (.object runtimeType leftResponseFields)
        (.object runtimeType rightResponseFields) :=
  recursiveChildExecutionSound_proved schema resolvers hschema inclusionFuel
    conditionValues leftValues rightValues parentType runtimeType ref leftSelectionSet
    rightSelectionSet executionFuel leftResponseFields rightResponseFields hruntime hcheck
    hleftBoolean hrightBoolean hcommonLookups hleftNodup hrightNodup hleft hright

private theorem annotatedExecution_success_mono_all
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ fuel source groups value,
        executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel source
            groups
          = .ok (value, 0)
        -> ∀ extra,
            executeQueryAnnotatedCollectedFields schema resolvers variableValues
              (fuel + extra) source groups
            = .ok (value, 0))
      ∧ (∀ fuel source responseName fields value,
          executeQueryAnnotatedField schema resolvers variableValues fuel source
              responseName fields
            = .ok (value, 0)
          -> ∀ extra,
              executeQueryAnnotatedField schema resolvers variableValues (fuel + extra)
                source responseName fields
              = .ok (value, 0))
      ∧ (∀ fuel fieldType fields source value,
          completeAnnotatedResponseValue schema resolvers variableValues fuel fieldType
              fields source
            = .ok (value, 0)
          -> ∀ extra,
              completeAnnotatedResponseValue schema resolvers variableValues
                (fuel + extra) fieldType fields source
              = .ok (value, 0))
      ∧ (∀ fuel itemType fields sources values,
          completeAnnotatedResponseValueList schema resolvers variableValues fuel itemType
              fields sources
            = .ok (values, 0)
          -> ∀ extra,
              completeAnnotatedResponseValueList schema resolvers variableValues
                (fuel + extra) itemType fields sources
              = .ok (values, 0)) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  all_goals
    simp_all [executeQueryAnnotatedCollectedFields, executeQueryAnnotatedField,
      completeAnnotatedResponseValue, completeAnnotatedResponseValueList,
      completeNonNullAnnotatedResponseValue, singleAnnotatedResponseFieldResult,
      catchAnnotatedResponseBubbleAsNull, Result.combine, Nat.add_assoc]
  case case2 =>
    intro fuel source responseName fields rest headIH tailIH value hresult extra
    cases hhead : executeQueryAnnotatedField schema resolvers variableValues fuel source
        responseName fields with
    | error headErrors =>
        cases htail : executeQueryAnnotatedCollectedFields schema resolvers variableValues
          fuel source rest <;> simp_all
    | ok headResult =>
        rcases headResult with ⟨headFields, headErrors⟩
        cases htail : executeQueryAnnotatedCollectedFields schema resolvers variableValues
            fuel source rest with
        | error tailErrors => simp [hhead, htail] at hresult
        | ok tailResult =>
            rcases tailResult with ⟨tailFields, tailErrors⟩
            change Result.combine List.append
              (executeQueryAnnotatedField schema resolvers variableValues fuel source
                responseName fields)
              (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                source rest) = .ok (value, 0) at hresult
            rw [hhead, htail] at hresult
            simp only [Result.combine, Except.ok.injEq, Prod.mk.injEq] at hresult
            have hheadErrors : headErrors = 0 := by omega
            have htailErrors : tailErrors = 0 := by omega
            subst headErrors
            subst tailErrors
            rw [← hresult.1]
            rw [headIH headFields hhead extra, tailIH tailFields htail extra]
            rfl
  case case6 =>
    intro source responseName field rest fuel definition hlookup hcoerce value hresult
      extra
    generalize htype : definition.outputType = outputType at hresult
    cases outputType <;> simp at hresult
    all_goals
      subst_vars
      simp [executeQueryAnnotatedField, hlookup, hcoerce, htype]
  case case7 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      hresolve value hresult extra
    generalize htype : definition.outputType = outputType at hresult
    cases outputType <;> simp at hresult
    all_goals
      subst_vars
      simp [executeQueryAnnotatedField, hlookup, hcoerce, hresolve, htype]
  case case8 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      resolved hresolve completeIH value hresult extra
    generalize hcompleted :
        completeAnnotatedResponseValue schema resolvers variableValues fuel
          definition.outputType (field :: rest) resolved = completed at hresult
    cases completed with
    | error completedErrors => simp at hresult
    | ok completedResult =>
        rcases completedResult with ⟨completedValue, completedErrors⟩
        simp only [Except.ok.injEq, Prod.mk.injEq] at hresult
        rcases hresult with ⟨rfl, hzero⟩
        subst completedErrors
        rw [show fuel + (1 + extra) = (fuel + extra) + 1 by omega]
        simp only [executeQueryAnnotatedField, hlookup, hcoerce, hresolve]
        rw [completeIH completedValue hcompleted extra]
        rfl
  case case10 =>
    intro fuel inner fields value hfuel innerIH result hresult extra
    generalize hcompleted :
        completeAnnotatedResponseValue schema resolvers variableValues fuel inner fields
          value = completed at hresult
    cases completed with
    | error completedErrors => simp at hresult
    | ok completedResult =>
        rcases completedResult with ⟨completedValue, completedErrors⟩
        cases completedValue with
        | null => simp at hresult
        | scalar scalarValue =>
            rcases hresult with ⟨rfl, rfl⟩
            rw [innerIH _ hcompleted extra]
        | object runtimeType fields =>
            rcases hresult with ⟨rfl, rfl⟩
            rw [innerIH _ hcompleted extra]
        | list values =>
            rcases hresult with ⟨rfl, rfl⟩
            rw [innerIH _ hcompleted extra]
  case case14 =>
    intro fuel parentType fields runtimeType ref hincludes childIH value hresult
      extra
    have hcompleted := catchAnnotated_eq_ok_zero_of_error_positive
      (executeAnnotatedCollectedFields_error_positive schema resolvers variableValues fuel
        (.object runtimeType ref)
        (collectFields schema variableValues runtimeType (.object runtimeType ref)
          (mergedFieldSelectionSet fields))) hresult
    rcases hcompleted with ⟨completedFields, hcompleted, rfl⟩
    rw [show fuel + (1 + extra) = (fuel + extra) + 1 by omega]
    simp only [completeAnnotatedResponseValue, hincludes,
      catchAnnotatedResponseBubbleAsNull]
    rw [NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
    rw [childIH completedFields hcompleted extra]
    rfl
  case case16 =>
    intro fuel inner fields values listIH value hresult extra
    have hcompleted := catchAnnotated_eq_ok_zero_of_error_positive
      ((annotatedExecution_error_positive_all schema resolvers variableValues).2.2.2
        fuel inner fields values) hresult
    rcases hcompleted with ⟨completedValues, hcompleted, rfl⟩
    rw [show fuel + (1 + extra) = (fuel + extra) + 1 by omega]
    simp only [completeAnnotatedResponseValue, catchAnnotatedResponseBubbleAsNull]
    rw [listIH completedValues hcompleted extra]
  case case20 =>
    intro fuel itemType fields value values headIH tailIH result hresult extra
    cases hhead : completeAnnotatedResponseValue schema resolvers variableValues fuel
        itemType fields value with
    | error headErrors =>
        cases htail : completeAnnotatedResponseValueList schema resolvers variableValues
          fuel itemType fields values <;> simp_all
    | ok headResult =>
        rcases headResult with ⟨headValue, headErrors⟩
        cases htail : completeAnnotatedResponseValueList schema resolvers variableValues
            fuel itemType fields values with
        | error tailErrors => simp [hhead, htail] at hresult
        | ok tailResult =>
            rcases tailResult with ⟨tailValues, tailErrors⟩
            change Result.combine List.cons
              (completeAnnotatedResponseValue schema resolvers variableValues fuel itemType
                fields value)
              (completeAnnotatedResponseValueList schema resolvers variableValues fuel
                itemType fields values) = .ok (result, 0) at hresult
            rw [hhead, htail] at hresult
            simp only [Result.combine, Except.ok.injEq, Prod.mk.injEq] at hresult
            have hheadErrors : headErrors = 0 := by omega
            have htailErrors : tailErrors = 0 := by omega
            subst headErrors
            subst tailErrors
            rw [← hresult.1]
            rw [headIH headValue hhead extra, tailIH tailValues htail extra]
  case case11 =>
    intro fuel fieldType fields hnotNonNull extra
    rw [show fuel + (1 + extra) = (fuel + extra) + 1 by omega]
    simp [completeAnnotatedResponseValue]
  case case13 =>
    intro fuel typeName fields value hnotComposite extra
    rw [show fuel + (1 + extra) = (fuel + extra) + 1 by omega]
    simp [completeAnnotatedResponseValue, hnotComposite]

theorem executeQueryAnnotatedCollectedFields_success_mono
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (value : List AnnotatedResponseField)
    (hresult
      : executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          source groups
        = .ok (value, 0))
    (extra : Nat)
    : executeQueryAnnotatedCollectedFields schema resolvers variableValues (fuel + extra)
        source groups
      = .ok (value, 0) :=
  (annotatedExecution_success_mono_all schema resolvers variableValues).1 fuel source
    groups value hresult extra

end QueryInclusion
end GraphQL
