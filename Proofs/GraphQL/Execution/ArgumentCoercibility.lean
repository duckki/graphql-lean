import Proofs.GraphQL.Execution.InputDefaults
import GraphQL.Theories.ExecutionReadiness

namespace GraphQL.Execution

theorem schemaWellFormed_lookupField_wellFormed
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType fieldName : Name} {field : FieldDefinition}
    (hlookup : schema.lookupField parentType fieldName = some field)
    : SchemaWellFormedness.fieldDefinitionWellFormed schema field := by
  cases htype : schema.lookupType parentType with
  | none => simp [Schema.lookupField, htype] at hlookup
  | some type =>
      have hwell :=
        SchemaWellFormedness.schemaWellFormed_lookupType_typeDefinitionWellFormed
          hschema htype
      cases type <;> simp [Schema.lookupField, htype, TypeDefinition.fields?] at hlookup
      case object object =>
        exact hwell.1.2.2 field (List.mem_of_find?_eq_some hlookup)
      case interface interface =>
        exact hwell.1.2.2 field (List.mem_of_find?_eq_some hlookup)

private theorem lookupArgumentValue_mem {arguments : List Argument}
    {name : Name} {value : InputValue}
    (hlookup : Argument.lookupValue? arguments name = some value)
    : ∃ argument,
        argument ∈ arguments ∧ argument.name = name ∧ argument.value = value := by
  induction arguments with
  | nil => simp [Argument.lookupValue?] at hlookup
  | cons head rest ih =>
      simp only [Argument.lookupValue?] at hlookup
      split at hlookup
      next heq => exact ⟨head, by simp, heq, Option.some.inj hlookup⟩
      next =>
        obtain ⟨argument, hmem, hname, hvalue⟩ := ih hlookup
        exact ⟨argument, List.mem_cons_of_mem _ hmem, hname, hvalue⟩

private theorem lookupArgumentValue_none {arguments : List Argument} {name : Name}
    (hlookup : Argument.lookupValue? arguments name = none)
    : ∀ argument, argument ∈ arguments -> argument.name ≠ name := by
  induction arguments with
  | nil => simp
  | cons head rest ih =>
      simp only [Argument.lookupValue?] at hlookup
      split at hlookup
      · cases hlookup
      next hne =>
        intro argument hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hne
        · exact ih hlookup argument hmem

private theorem coerceArgumentValues_success_of_entries
    {schema : Schema} {values : VariableValues} {definitions : List InputValueDefinition}
    {arguments : List Argument}
    (hentries
      : ∀ definition,
          definition ∈ definitions
          -> coerceArgumentValue schema values definition arguments ≠ .error)
    : (coerceArgumentValues schema values definitions arguments).isSuccess = true := by
  induction definitions with
  | nil => rfl
  | cons head rest ih =>
      have hrest :=
        ih (fun definition hmem => hentries definition (List.mem_cons_of_mem _ hmem))
      have hhead := hentries head (by simp)
      cases hrestResult : coerceArgumentValues schema values rest arguments with
      | error => simp [hrestResult] at hrest
      | success coercedRest =>
          cases hheadResult : coerceArgumentValue schema values head arguments <;>
            simp_all [coerceArgumentValues]

theorem omittedNonNullArgumentsHaveDefaults_of_valid
    {schema : Schema} {variables : List VariableDefinition}
    {definitions : List InputValueDefinition} {arguments : List Argument}
    (hvalid : Validation.argumentsValid schema definitions variables arguments)
    : omittedNonNullArgumentsHaveDefaults definitions arguments := by
  intro definition hdefinition hnonNull hlookup
  cases hdefault : definition.defaultValue with
  | some value => rfl
  | none =>
      have hrequired : Validation.isRequiredArgument definition := by
        cases htype : definition.inputType <;>
          simp_all [Validation.isRequiredArgument, Validation.isRequiredInputValueDefinition,
            InputValueDefinition.isRequired, TypeRef.isNonNull]
      obtain ⟨argument, hargument, _⟩ := hvalid.2.2 definition hdefinition hrequired
      have hmem : argument ∈ arguments := List.mem_of_find?_eq_some hargument
      have hname : argument.name = definition.name := by
        simpa using List.find?_some hargument
      exact False.elim (lookupArgumentValue_none hlookup argument hmem hname)

-- Supplied values are validated at the declared location. Implementations preserve
-- argument input types, but need not preserve defaults or variable-usage validity.
theorem coerceArgumentValues_success_of_implementation
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {variables : List VariableDefinition} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema variables values)
    {expected definitions : List InputValueDefinition} {arguments : List Argument}
    (hdefinitions
      : SchemaWellFormedness.inputValueDefinitionsWellFormed schema definitions)
    (himplements : SchemaWellFormedness.argumentDefinitionsImplement definitions expected)
    (harguments : Validation.argumentsValid schema expected variables arguments)
    (hdefaults : omittedNonNullArgumentsHaveDefaults definitions arguments)
    : (coerceArgumentValues schema values definitions arguments).isSuccess = true := by
  apply coerceArgumentValues_success_of_entries
  intro definition hdefinition
  cases hlookup : Argument.lookupValue? arguments definition.name with
  | some value =>
      obtain ⟨argument, hmem, hname, hvalue⟩ := lookupArgumentValue_mem hlookup
      obtain ⟨source, hsource, hvalid⟩ := harguments.2.1 argument hmem
      have hsourceMem : source ∈ expected := List.mem_of_find?_eq_some hsource
      have hsourceName : source.name = argument.name := by
        simpa using List.find?_some hsource
      obtain ⟨target, htarget, htype⟩ := himplements.1 source hsourceMem
      have hlookupDef := SchemaWellFormedness.inputValueDefinitions_lookupArgument_of_mem
        hdefinitions.1 hdefinition
      rw [hsourceName, hname, hlookupDef] at htarget
      cases Option.some.inj htarget
      rw [hvalue, ← htype] at hvalid
      obtain ⟨coerced, hcoerced⟩ := coerceInputValue_success_of_valid hschema hvalues hvalid
      simp [coerceArgumentValue, hlookup, hcoerced]
  | none =>
      cases hdefault : definition.defaultValue with
      | some defaultValue =>
          have hvalid := (hdefinitions.2 definition hdefinition).2
          rw [hdefault] at hvalid
          have hliteral := Validation.constInputValue_valid_toInputValue schema
            variables none hvalid
          obtain ⟨coerced, hcoerced⟩ := coerceInputValue_success_of_valid hschema hvalues hliteral
          simp [coerceArgumentValue, coerceArgumentDefault, hlookup, hdefault, hcoerced]
      | none =>
          have hnullable : definition.inputType.isNonNull = false := by
            cases hnonNull : definition.inputType.isNonNull with
            | false => rfl
            | true =>
                have h := hdefaults definition hdefinition hnonNull hlookup
                simp [hdefault] at h
          simp [coerceArgumentValue, coerceArgumentDefault, hlookup, hdefault, hnullable]

theorem coerceArgumentValues_success_of_valid
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {variableDefinitions : List VariableDefinition} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema variableDefinitions values)
    {definitions : List InputValueDefinition} {arguments : List Argument}
    (hdefinitions
      : SchemaWellFormedness.inputValueDefinitionsWellFormed schema definitions)
    (harguments
      : Validation.argumentsValid schema definitions variableDefinitions arguments)
    : (coerceArgumentValues schema values definitions arguments).isSuccess = true := by
  apply coerceArgumentValues_success_of_implementation hschema hvalues hdefinitions
    (expected := definitions) ?_ harguments
    (omittedNonNullArgumentsHaveDefaults_of_valid harguments)
  constructor
  · intro definition hmem
    exact ⟨definition, SchemaWellFormedness.inputValueDefinitions_lookupArgument_of_mem
      hdefinitions.1 hmem, rfl⟩
  · intro definition hmem hmissing
    rw [SchemaWellFormedness.inputValueDefinitions_lookupArgument_of_mem
      hdefinitions.1 hmem] at hmissing
    cases hmissing

end GraphQL.Execution
