import Proofs.GraphQL.Execution.InputDefaults

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
  apply coerceArgumentValues_success_of_entries
  intro definition hdefinition
  cases hlookup : Argument.lookupValue? arguments definition.name with
  | some value =>
      obtain ⟨argument, hmem, hname, hvalue⟩ := lookupArgumentValue_mem hlookup
      obtain ⟨target, htarget, hvalid⟩ := harguments.2.1 argument hmem
      have hlookupDef := SchemaWellFormedness.inputValueDefinitions_lookupArgument_of_mem
        hdefinitions.1 hdefinition
      rw [hname, hlookupDef] at htarget
      have heq : target = definition := Option.some.inj htarget.symm
      subst target
      rw [hvalue] at hvalid
      obtain ⟨coerced, hcoerced⟩ := coerceInputValue_success_of_valid
        hschema hvalues hvalid
      simp [coerceArgumentValue, hlookup, hcoerced]
  | none =>
      cases hdefault : definition.defaultValue with
      | some defaultValue =>
          have hvalid := (hdefinitions.2 definition hdefinition).2
          rw [hdefault] at hvalid
          have hliteral := Validation.constInputValue_valid_toInputValue schema
            variableDefinitions none hvalid
          obtain ⟨coerced, hcoerced⟩ := coerceInputValue_success_of_valid
            hschema hvalues hliteral
          simp [coerceArgumentValue, coerceArgumentDefault, hlookup, hdefault, hcoerced]
      | none =>
          have hnullable : definition.inputType.isNonNull = false := by
            cases htype : definition.inputType with
            | named _ => rfl
            | list _ => rfl
            | nonNull inner =>
                have hrequired : Validation.isRequiredArgument definition := by
                  simp [Validation.isRequiredArgument, Validation.isRequiredInputValueDefinition,
                    InputValueDefinition.isRequired, htype, hdefault]
                obtain ⟨argument, hargument, _⟩ :=
                  harguments.2.2 definition hdefinition hrequired
                have hmem : argument ∈ arguments := List.mem_of_find?_eq_some hargument
                have hname : argument.name = definition.name := by
                  simpa using List.find?_some hargument
                exact False.elim (lookupArgumentValue_none hlookup argument hmem hname)
          simp [coerceArgumentValue, coerceArgumentDefault, hlookup, hdefault, hnullable]

end GraphQL.Execution
