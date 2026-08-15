import Proofs.GraphQL.Validation.FieldMerge
import Proofs.GraphQL.Validation.SelectionValidity

/-! Variable-collector facts used by validation-preservation proofs. -/

namespace GraphQL

namespace Validation

theorem inputObjectFieldsVariables_insertObjectFieldSorted_mem_iff
    (variableName : Name) (field : Name × InputValue)
    : ∀ fields,
        variableName
          ∈ inputObjectFieldsVariables (InputValue.insertObjectFieldSorted field fields)
        ↔ variableName ∈ inputValueVariables field.2
          ∨ variableName ∈ inputObjectFieldsVariables fields
  | [] => by
      simp [InputValue.insertObjectFieldSorted, inputObjectFieldsVariables]
  | candidate :: rest => by
    rw [InputValue.insertObjectFieldSorted]
    split
    · simp [inputObjectFieldsVariables]
    · simp only [inputObjectFieldsVariables, List.mem_append]
      rw [inputObjectFieldsVariables_insertObjectFieldSorted_mem_iff]
      constructor
      · rintro (hcandidate | hfield | hrest)
        · exact Or.inr (Or.inl hcandidate)
        · exact Or.inl hfield
        · exact Or.inr (Or.inr hrest)
      · rintro (hfield | hcandidate | hrest)
        · exact Or.inr (Or.inl hfield)
        · exact Or.inl hcandidate
        · exact Or.inr (Or.inr hrest)

theorem inputObjectFieldsVariables_sortObjectFieldsByName_mem_iff (variableName : Name)
    : ∀ fields,
        variableName
          ∈ inputObjectFieldsVariables (InputValue.sortObjectFieldsByName fields)
        ↔ variableName ∈ inputObjectFieldsVariables fields
  | [] => by
      simp [InputValue.sortObjectFieldsByName, inputObjectFieldsVariables]
  | field :: rest => by
    simp only [InputValue.sortObjectFieldsByName]
    rw [inputObjectFieldsVariables_insertObjectFieldSorted_mem_iff,
      inputObjectFieldsVariables_sortObjectFieldsByName_mem_iff]
    simp [inputObjectFieldsVariables]

mutual
  theorem inputValueVariables_canonical_mem_iff (variableName : Name)
      : ∀ value,
          variableName ∈ inputValueVariables value.canonical
          ↔ variableName ∈ inputValueVariables value
    | .null => by simp [InputValue.canonical, inputValueVariables]
    | .int value => by simp [InputValue.canonical, inputValueVariables]
    | .float value => by simp [InputValue.canonical, inputValueVariables]
    | .string value => by simp [InputValue.canonical, inputValueVariables]
    | .boolean value => by simp [InputValue.canonical, inputValueVariables]
    | .enum value => by simp [InputValue.canonical, inputValueVariables]
    | .variable name => by simp [InputValue.canonical, inputValueVariables]
    | .list values => by
        simp only [InputValue.canonical, inputValueVariables]
        exact inputValuesVariables_canonical_mem_iff variableName values
    | .object fields => by
        simp only [InputValue.canonical, inputValueVariables]
        rw [inputObjectFieldsVariables_sortObjectFieldsByName_mem_iff]
        exact inputObjectFieldsVariables_canonical_mem_iff variableName fields

  theorem inputValuesVariables_canonical_mem_iff (variableName : Name)
      : ∀ values,
          variableName ∈ inputValuesVariables (InputValue.canonicalValues values)
          ↔ variableName ∈ inputValuesVariables values
    | [] => by simp [InputValue.canonicalValues, inputValuesVariables]
    | value :: rest => by
        simp only [InputValue.canonicalValues, inputValuesVariables,
          List.mem_append]
        rw [inputValueVariables_canonical_mem_iff,
          inputValuesVariables_canonical_mem_iff]

  theorem inputObjectFieldsVariables_canonical_mem_iff (variableName : Name)
      : ∀ fields,
          variableName
            ∈ inputObjectFieldsVariables (InputValue.canonicalObjectFields fields)
          ↔ variableName ∈ inputObjectFieldsVariables fields
    | [] => by
        simp [InputValue.canonicalObjectFields, inputObjectFieldsVariables]
    | (name, value) :: rest => by
        simp only [InputValue.canonicalObjectFields,
          inputObjectFieldsVariables, List.mem_append]
        rw [inputValueVariables_canonical_mem_iff,
          inputObjectFieldsVariables_canonical_mem_iff]
end

mutual
  theorem inputValueVariables_mem_iff_of_structuralEquivalent (variableName : Name)
      : ∀ left right,
          InputValue.structuralEquivalent left right
          -> (variableName ∈ inputValueVariables left
              ↔ variableName ∈ inputValueVariables right)
    | .null, .null, _ => by simp [inputValueVariables]
    | .int left, .int right, _ => by simp [inputValueVariables]
    | .float left, .float right, _ => by simp [inputValueVariables]
    | .string left, .string right, _ => by simp [inputValueVariables]
    | .boolean left, .boolean right, _ => by simp [inputValueVariables]
    | .enum left, .enum right, _ => by simp [inputValueVariables]
    | .variable left, .variable right, hequivalent => by
        simp [InputValue.structuralEquivalent] at hequivalent
        simp [inputValueVariables, hequivalent]
    | .list left, .list right, hequivalent => by
        simp only [inputValueVariables]
        exact inputValuesVariables_mem_iff_of_structuralEquivalent
          variableName left right hequivalent
    | .object left, .object right, hequivalent => by
        simp only [inputValueVariables]
        exact inputObjectFieldsVariables_mem_iff_of_structuralEquivalent
          variableName left right hequivalent
    | .null, .int _, hequivalent
    | .null, .float _, hequivalent
    | .null, .string _, hequivalent
    | .null, .boolean _, hequivalent
    | .null, .enum _, hequivalent
    | .null, .list _, hequivalent
    | .null, .object _, hequivalent
    | .null, .variable _, hequivalent
    | .int _, .null, hequivalent
    | .int _, .float _, hequivalent
    | .int _, .string _, hequivalent
    | .int _, .boolean _, hequivalent
    | .int _, .enum _, hequivalent
    | .int _, .list _, hequivalent
    | .int _, .object _, hequivalent
    | .int _, .variable _, hequivalent
    | .float _, .null, hequivalent
    | .float _, .int _, hequivalent
    | .float _, .string _, hequivalent
    | .float _, .boolean _, hequivalent
    | .float _, .enum _, hequivalent
    | .float _, .list _, hequivalent
    | .float _, .object _, hequivalent
    | .float _, .variable _, hequivalent
    | .string _, .null, hequivalent
    | .string _, .int _, hequivalent
    | .string _, .float _, hequivalent
    | .string _, .boolean _, hequivalent
    | .string _, .enum _, hequivalent
    | .string _, .list _, hequivalent
    | .string _, .object _, hequivalent
    | .string _, .variable _, hequivalent
    | .boolean _, .null, hequivalent
    | .boolean _, .int _, hequivalent
    | .boolean _, .float _, hequivalent
    | .boolean _, .string _, hequivalent
    | .boolean _, .enum _, hequivalent
    | .boolean _, .list _, hequivalent
    | .boolean _, .object _, hequivalent
    | .boolean _, .variable _, hequivalent
    | .enum _, .null, hequivalent
    | .enum _, .int _, hequivalent
    | .enum _, .float _, hequivalent
    | .enum _, .string _, hequivalent
    | .enum _, .boolean _, hequivalent
    | .enum _, .list _, hequivalent
    | .enum _, .object _, hequivalent
    | .enum _, .variable _, hequivalent
    | .list _, .null, hequivalent
    | .list _, .int _, hequivalent
    | .list _, .float _, hequivalent
    | .list _, .string _, hequivalent
    | .list _, .boolean _, hequivalent
    | .list _, .enum _, hequivalent
    | .list _, .object _, hequivalent
    | .list _, .variable _, hequivalent
    | .object _, .null, hequivalent
    | .object _, .int _, hequivalent
    | .object _, .float _, hequivalent
    | .object _, .string _, hequivalent
    | .object _, .boolean _, hequivalent
    | .object _, .enum _, hequivalent
    | .object _, .list _, hequivalent
    | .object _, .variable _, hequivalent
    | .variable _, .null, hequivalent
    | .variable _, .int _, hequivalent
    | .variable _, .float _, hequivalent
    | .variable _, .string _, hequivalent
    | .variable _, .boolean _, hequivalent
    | .variable _, .enum _, hequivalent
    | .variable _, .list _, hequivalent
    | .variable _, .object _, hequivalent => by
        simp [InputValue.structuralEquivalent] at hequivalent

  theorem inputValuesVariables_mem_iff_of_structuralEquivalent (variableName : Name)
      : ∀ left right,
          InputValue.structuralValuesEquivalent left right
          -> (variableName ∈ inputValuesVariables left
              ↔ variableName ∈ inputValuesVariables right)
    | [], [], _ => by simp [inputValuesVariables]
    | left :: lefts, right :: rights, hequivalent => by
        simp [InputValue.structuralValuesEquivalent] at hequivalent
        simp only [inputValuesVariables, List.mem_append]
        rw [inputValueVariables_mem_iff_of_structuralEquivalent
            variableName left right hequivalent.1,
          inputValuesVariables_mem_iff_of_structuralEquivalent
            variableName lefts rights hequivalent.2]
    | [], _ :: _, hequivalent
    | _ :: _, [], hequivalent => by
        simp [InputValue.structuralValuesEquivalent] at hequivalent

  theorem inputObjectFieldsVariables_mem_iff_of_structuralEquivalent (variableName : Name)
      : ∀ left right,
          InputValue.structuralObjectFieldsEquivalent left right
          -> (variableName ∈ inputObjectFieldsVariables left
              ↔ variableName ∈ inputObjectFieldsVariables right)
    | [], [], _ => by simp [inputObjectFieldsVariables]
    | (leftName, leftValue) :: lefts,
      (rightName, rightValue) :: rights, hequivalent => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hequivalent
        simp only [inputObjectFieldsVariables, List.mem_append]
        rw [inputValueVariables_mem_iff_of_structuralEquivalent
            variableName leftValue rightValue hequivalent.2.1,
          inputObjectFieldsVariables_mem_iff_of_structuralEquivalent
            variableName lefts rights hequivalent.2.2]
    | [], _ :: _, hequivalent
    | _ :: _, [], hequivalent => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hequivalent
end

theorem inputValueVariables_mem_iff_of_equivalent
    {left right : InputValue} (variableName : Name)
    (hequivalent : left.equivalent right)
    : variableName ∈ inputValueVariables left
      ↔ variableName ∈ inputValueVariables right := by
  rw [← inputValueVariables_canonical_mem_iff variableName left,
    ← inputValueVariables_canonical_mem_iff variableName right]
  exact inputValueVariables_mem_iff_of_structuralEquivalent
    variableName left.canonical right.canonical hequivalent

theorem argumentVariables_mem_iff_of_equivalent
    {left right : Argument} (variableName : Name)
    (hequivalent : left.equivalent right)
    : variableName ∈ argumentVariables left ↔ variableName ∈ argumentVariables right := by
  exact inputValueVariables_mem_iff_of_equivalent variableName hequivalent.2

theorem argumentsVariables_mem_iff (variableName : Name)
    : ∀ arguments,
        variableName ∈ argumentsVariables arguments
        ↔ ∃ argument, argument ∈ arguments ∧ variableName ∈ argumentVariables argument
  | [] => by
      simp [argumentsVariables]
  | argument :: rest => by
      simp only [argumentsVariables, List.mem_append,
        argumentsVariables_mem_iff]
      constructor
      · rintro (hargument | ⟨candidate, hcandidate, hvariable⟩)
        · exact ⟨argument, by simp, hargument⟩
        · exact ⟨candidate, by simp [hcandidate], hvariable⟩
      · rintro ⟨candidate, hcandidate, hvariable⟩
        rcases List.mem_cons.mp hcandidate with heq | hrest
        · subst candidate
          exact Or.inl hvariable
        · exact Or.inr ⟨candidate, hrest, hvariable⟩

theorem argumentsVariables_mem_iff_of_equivalent
    {left right : List Argument} (variableName : Name)
    (hequivalent : Argument.argumentsEquivalent left right)
    : variableName ∈ argumentsVariables left
      ↔ variableName ∈ argumentsVariables right := by
  constructor
  · intro hvariable
    rcases (argumentsVariables_mem_iff variableName left).1 hvariable with
      ⟨argument, hargument, hargumentVariable⟩
    rcases hequivalent.1 argument hargument with
      ⟨argument', hargument', hargumentEquivalent⟩
    exact (argumentsVariables_mem_iff variableName right).2
      ⟨argument', hargument',
        (argumentVariables_mem_iff_of_equivalent variableName
          hargumentEquivalent).1 hargumentVariable⟩
  · intro hvariable
    rcases (argumentsVariables_mem_iff variableName right).1 hvariable with
      ⟨argument, hargument, hargumentVariable⟩
    rcases hequivalent.2 argument hargument with
      ⟨argument', hargument', hargumentEquivalent⟩
    exact (argumentsVariables_mem_iff variableName left).2
      ⟨argument', hargument',
        (argumentVariables_mem_iff_of_equivalent variableName
          hargumentEquivalent).2 hargumentVariable⟩

mutual
  private theorem constInputValue_toInputValue_variables_empty
      : ∀ (value : ConstInputValue), inputValueVariables value.toInputValue = []
    | .null
    | .int _
    | .float _
    | .string _
    | .boolean _
    | .enum _ => rfl
    | .list values => by
        simp only [ConstInputValue.toInputValue, inputValueVariables]
        exact constInputValues_toInputValues_variables_empty values
    | .object fields => by
        simp only [ConstInputValue.toInputValue, inputValueVariables]
        exact constInputObjectFields_toInputFields_variables_empty fields

  private theorem constInputValues_toInputValues_variables_empty
      : ∀ (values : List ConstInputValue),
          inputValuesVariables (ConstInputValue.valuesToInputValues values) = []
    | [] => rfl
    | value :: rest => by
        simp [ConstInputValue.valuesToInputValues, inputValuesVariables,
          constInputValue_toInputValue_variables_empty value,
          constInputValues_toInputValues_variables_empty rest]

  private theorem constInputObjectFields_toInputFields_variables_empty
      : ∀ (fields : List (Name × ConstInputValue)),
          inputObjectFieldsVariables (ConstInputValue.objectFieldsToInputFields fields)
          = []
    | [] => rfl
    | (_, value) :: rest => by
        simp [ConstInputValue.objectFieldsToInputFields, inputObjectFieldsVariables,
          constInputValue_toInputValue_variables_empty value,
          constInputObjectFields_toInputFields_variables_empty rest]
end

private theorem inputValuesVariables_exists {variableName : Name}
    : ∀ values,
        variableName ∈ inputValuesVariables values
        -> ∃ value, value ∈ values ∧ variableName ∈ inputValueVariables value
  | [], hvariable => by cases hvariable
  | value :: rest, hvariable => by
      simp only [inputValuesVariables, List.mem_append] at hvariable
      rcases hvariable with hvalue | hrest
      · exact ⟨value, by simp, hvalue⟩
      · rcases inputValuesVariables_exists rest hrest with
          ⟨candidate, hcandidate, hcandidateVariable⟩
        exact ⟨candidate, by simp [hcandidate], hcandidateVariable⟩

private theorem inputObjectFieldsVariables_exists {variableName : Name}
    : ∀ fields,
        variableName ∈ inputObjectFieldsVariables fields
        -> ∃ name value, (name, value) ∈ fields ∧ variableName ∈ inputValueVariables value
  | [], hvariable => by cases hvariable
  | (name, value) :: rest, hvariable => by
      simp only [inputObjectFieldsVariables, List.mem_append] at hvariable
      rcases hvariable with hvalue | hrest
      · exact ⟨name, value, by simp, hvalue⟩
      · rcases inputObjectFieldsVariables_exists rest hrest with
          ⟨candidateName, candidateValue, hcandidate, hcandidateVariable⟩
        exact ⟨candidateName, candidateValue, by simp [hcandidate],
          hcandidateVariable⟩

theorem valueIsCorrectTypeAtLocation_variable_defined
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {value : InputValue} {expectedType : TypeRef}
    {locationDefault : Option ConstInputValue}
    (hvalid
      : ValueIsCorrectTypeAtLocation schema variableDefinitions value expectedType
          locationDefault)
    {variableName : Name}
    (hvariable : variableName ∈ inputValueVariables value)
    : ∃ definition,
        getVariableDefinition? variableDefinitions variableName = some definition := by
  apply (ValueIsCorrectTypeAtLocation.rec
    (motive_1 := fun value _expectedType _locationDefault _hvalid =>
      variableName ∈ inputValueVariables value
      -> ∃ definition,
          getVariableDefinition? variableDefinitions variableName = some definition)
    (motive_2 := fun _definitions fields _hvalid =>
      variableName ∈ inputObjectFieldsVariables fields
      -> ∃ definition,
          getVariableDefinition? variableDefinitions variableName = some definition)
    (motive_3 := fun fields _inner _hvalid =>
      variableName ∈ inputObjectFieldsVariables fields
      -> ∃ definition,
          getVariableDefinition? variableDefinitions variableName = some definition)
    (fun definedName _expectedType _locationDefault definition _hinput hlookup
        _husage hvariable => by
      simp [inputValueVariables] at hvariable
      subst variableName
      exact ⟨definition, hlookup⟩)
    (fun _typeName _locationDefault _hinput hvariable => by
      simp [inputValueVariables] at hvariable)
    (fun _inner _locationDefault _hinput hvariable => by
      simp [inputValueVariables] at hvariable)
    (fun _value _inner _locationDefault _hinput _hnotNull _hnotVariable _hinner ih
        hvariable => ih hvariable)
    (fun values _inner _locationDefault _hinput _hitems ihItems hvariable => by
      rcases inputValuesVariables_exists values hvariable with
        ⟨item, hitem, hitemVariable⟩
      exact ihItems item hitem hitemVariable)
    (fun _fields _typeName _locationDefault _inputObject _hinput _hlookup _hfields
        ihFields hvariable => ihFields hvariable)
    (fun _fields _inner _locationDefault _hinput _hitem ihItem hvariable =>
      ihItem hvariable)
    (fun _value _inner _locationDefault _hinput _hnotList _hnotObject _hnotNull
        _hnotVariable _hitem ih hvariable => ih hvariable)
    (fun _value _typeName _locationDefault _hinput _hnotObject _hnotNull
        _hnotVariable hconst _hlookup hvariable => by
      rcases hconst with ⟨constValue, rfl⟩
      rw [constInputValue_toInputValue_variables_empty] at hvariable
      cases hvariable)
    (fun definitions fields _hnodup hknown _htyped _hrequiredPresent
        _hrequiredNonNull ihTyped hvariable => by
      rcases inputObjectFieldsVariables_exists fields hvariable with
        ⟨fieldName, fieldValue, hfield, hfieldVariable⟩
      have hknownField := hknown fieldName fieldValue hfield
      cases hdefinition : Schema.lookupArgumentDefinition definitions fieldName with
      | none => simp [hdefinition] at hknownField
      | some definition =>
          exact ihTyped fieldName fieldValue definition hfield hdefinition
            hfieldVariable)
    (fun _fields _inner _hvalue ih hvariable => ih hvariable)
    hvalid) hvariable

theorem argumentsValid_variable_defined
    {schema : Schema} {definitions : List InputValueDefinition}
    {variableDefinitions : List VariableDefinition} {arguments : List Argument}
    (hvalid : argumentsValid schema definitions variableDefinitions arguments)
    {variableName : Name}
    (hvariable : variableName ∈ argumentsVariables arguments)
    : ∃ definition,
        getVariableDefinition? variableDefinitions variableName = some definition := by
  rcases (argumentsVariables_mem_iff variableName arguments).1 hvariable with
    ⟨argument, hargument, hargumentVariable⟩
  rcases hvalid.2.1 argument hargument with
    ⟨definition, _hlookup, hvalue⟩
  exact valueIsCorrectTypeAtLocation_variable_defined hvalue hargumentVariable

private theorem directivesVariables_exists {variableName : Name}
    : ∀ directives,
        variableName ∈ directivesVariables directives
        -> ∃ directive,
            directive ∈ directives ∧ variableName ∈ directiveVariables directive
  | [], hvariable => by cases hvariable
  | directive :: rest, hvariable => by
      simp only [directivesVariables, List.mem_append] at hvariable
      rcases hvariable with hdirective | hrest
      · exact ⟨directive, by simp, hdirective⟩
      · rcases directivesVariables_exists rest hrest with
          ⟨candidate, hcandidate, hcandidateVariable⟩
        exact ⟨candidate, by simp [hcandidate], hcandidateVariable⟩

theorem directivesValid_variable_defined
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {directives : List DirectiveApplication}
    (hvalid : directivesValid schema variableDefinitions directives)
    {variableName : Name}
    (hvariable : variableName ∈ directivesVariables directives)
    : ∃ definition,
        getVariableDefinition? variableDefinitions variableName = some definition := by
  rcases directivesVariables_exists directives hvariable with
    ⟨directive, hdirective, hdirectiveVariable⟩
  have hdirectiveValid := hvalid.2 directive hdirective
  cases directive <;> rename_i ifArgument <;> cases ifArgument <;>
    simp [directiveVariables, directiveValid, directiveIfArgumentValid,
      inputValueVariables] at hdirectiveVariable hdirectiveValid
  all_goals
    subst variableName
    rcases hdirectiveValid with ⟨definition, hlookup, _husage⟩
    exact ⟨definition, hlookup⟩

mutual
  theorem selectionValid_variable_defined
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name} {selection : Selection}
      (hvalid : selectionValid schema variableDefinitions parentType selection)
      {variableName : Name}
      (hvariable : variableName ∈ selectionVariables selection)
      : ∃ definition,
          getVariableDefinition? variableDefinitions variableName = some definition := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, _hlookup, harguments, hselectionSet⟩
        simp only [selectionVariables, List.mem_append] at hvariable
        rcases hvariable with hhead | hchildren
        · rcases hhead with hargumentsVariable | hdirectives
          · exact argumentsValid_variable_defined harguments hargumentsVariable
          · exact directivesValid_variable_defined
              (selectionValid_field_directivesValid hvalid) hdirectives
        · simp [fieldSelectionSetValid] at hselectionSet
          rcases hselectionSet.2 with hleaf | hcomposite
          · rw [hleaf.2] at hchildren
            cases hchildren
          · exact selectionSetValid_variable_defined selectionSet
              hcomposite.2.2 hchildren
    | inlineFragment typeCondition directives selectionSet =>
        simp only [selectionVariables, List.mem_append] at hvariable
        cases typeCondition with
        | none =>
            simp only [selectionValid] at hvalid
            rcases hvariable with hdirectives | hchildren
            · exact directivesValid_variable_defined hvalid.1 hdirectives
            · exact selectionSetValid_variable_defined selectionSet hvalid.2.2
                hchildren
        | some typeCondition =>
            simp only [selectionValid] at hvalid
            rcases hvariable with hdirectives | hchildren
            · exact directivesValid_variable_defined hvalid.1 hdirectives
            · exact selectionSetValid_variable_defined selectionSet hvalid.2.2.2.2
                hchildren

  theorem selectionSetValid_variable_defined
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name}
      : ∀ selectionSet,
          selectionSetValid schema variableDefinitions parentType selectionSet
          -> ∀ {variableName},
              variableName ∈ selectionSetVariables selectionSet
              -> ∃ definition,
                  getVariableDefinition? variableDefinitions variableName
                  = some definition
    | [], _hvalid, _variableName, hvariable => by cases hvariable
    | selection :: rest, hvalid, variableName, hvariable => by
        unfold selectionSetValid at hvalid
        simp only [selectionSetVariables, List.mem_append] at hvariable
        rcases hvariable with hselection | hrest
        · exact selectionValid_variable_defined (hvalid selection (by simp))
            hselection
        · exact selectionSetValid_variable_defined rest (by
              unfold selectionSetValid
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate])) hrest
end

end Validation

end GraphQL
