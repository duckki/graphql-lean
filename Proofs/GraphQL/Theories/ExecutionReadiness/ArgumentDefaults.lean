import Proofs.GraphQL.Execution.ArgumentCoercibility
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-! Missing concrete argument defaults are the additional obstruction to constructing
coercible variable environments for an already validated operation. -/

namespace GraphQL.ExecutionReadiness

open Execution NormalForm

theorem omittedNonNullArgumentsHaveDefaultsBool_iff
    (definitions : List InputValueDefinition) (arguments : List Argument)
    : omittedNonNullArgumentsHaveDefaultsBool definitions arguments = true
      ↔ omittedNonNullArgumentsHaveDefaults definitions arguments := by
  simp only [omittedNonNullArgumentsHaveDefaultsBool, List.all_eq_true]
  constructor
  · intro h definition hmem hnonNull hmissing
    simpa [hnonNull, hmissing] using h definition hmem
  · intro h definition hmem
    cases hnonNull : definition.inputType.isNonNull with
    | false => simp
    | true =>
        cases hlookup : Argument.lookupValue? arguments definition.name with
        | none => simp [h definition hmem hnonNull hlookup]
        | some value => simp

mutual
  theorem selectionArgumentsCoercible_of_defaults
      {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
      {variables : List VariableDefinition} {values : VariableValues}
      (hvalues : variablesHaveNonNullValues schema variables values)
      {sourceType runtimeType : Name}
      (hpossible : runtimeType ∈ schema.getPossibleTypes sourceType)
      (hobject : schema.objectType runtimeType) (selection : Selection)
      (hvalid : Validation.selectionValid schema variables sourceType selection)
      (hdefaults : selectionCoercibleInPossibleTypes schema values runtimeType selection)
      : selectionArgumentsCoercible schema values runtimeType selection := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        intro hdirectives field hlookup
        have hdefaults := hdefaults hdirectives
        obtain ⟨source, hsource, harguments, hchildren⟩ :=
          Validation.selectionValid_field_lookup hvalid
        have himplements :=
          SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_argumentsImplement
            hschema hpossible hsource hlookup
        simp only [hlookup] at hdefaults
        constructor
        · exact coerceArgumentValues_success_of_implementation hschema hvalues
            (schemaWellFormed_lookupField_wellFormed hschema hlookup).2
            himplements harguments hdefaults.1
        · intro childType hchildPossible
          have hmember : childType ∈ schema.getPossibleTypes field.outputType.namedType := by
            simpa [Schema.typeIncludesObjectBool] using hchildPossible
          have hsourcePossible := typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
            (SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
              hschema hpossible hsource hlookup) hchildPossible
          have hsourceMember : childType ∈ schema.getPossibleTypes source.outputType.namedType := by
            simpa [Schema.typeIncludesObjectBool] using hsourcePossible
          exact selectionSetArgumentsCoercible_of_defaults hschema hvalues hsourceMember
            (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema _ _
              hmember)
            children
            (fieldSelectionSetValid_child_of_possibleType hchildren hsourceMember)
            (hdefaults.2 childType hmember)
    | inlineFragment condition directives children =>
        intro hdirectives hcondition
        cases condition with
        | none =>
            have hdefaults := hdefaults hdirectives
            exact selectionSetArgumentsCoercible_of_defaults hschema hvalues hpossible hobject
              children (Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid)
              hdefaults
        | some condition =>
            have hdefaults := hdefaults hdirectives
            have hmember : runtimeType ∈ schema.getPossibleTypes condition := by
              simpa [Schema.typeIncludesObjectBool] using hcondition
            exact selectionSetArgumentsCoercible_of_defaults hschema hvalues hmember
              hobject children
              (Validation.selectionValid_inlineFragment_some_selectionSetValid hvalid)
              (hdefaults hcondition)

  theorem selectionSetArgumentsCoercible_of_defaults
      {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
      {variables : List VariableDefinition} {values : VariableValues}
      (hvalues : variablesHaveNonNullValues schema variables values)
      {sourceType runtimeType : Name}
      (hpossible : runtimeType ∈ schema.getPossibleTypes sourceType)
      (hobject : schema.objectType runtimeType) (selections : List Selection)
      (hvalid : Validation.selectionSetValid schema variables sourceType selections)
      (hdefaults
        : selectionSetCoercibleInPossibleTypes schema values runtimeType selections)
      : selectionSetArgumentsCoercible schema values runtimeType selections := by
    cases selections with
    | nil => trivial
    | cons head rest =>
        unfold Validation.selectionSetValid at hvalid
        exact ⟨
          selectionArgumentsCoercible_of_defaults hschema hvalues hpossible hobject head
            (hvalid head (by simp)) hdefaults.1,
          selectionSetArgumentsCoercible_of_defaults hschema hvalues hpossible hobject
            rest
            (by
              unfold Validation.selectionSetValid
              exact fun selection hmem => hvalid selection (List.mem_cons_of_mem _ hmem))
            hdefaults.2
        ⟩
end

theorem operationArgumentsCoercible_of_defaults
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {operation : Operation} {values : VariableValues}
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hvalues : variablesHaveNonNullValues schema operation.variableDefinitions values)
    (hdefaults : operationCoercibleInPossibleTypes schema operation)
    : operationArgumentsCoercible schema values operation := by
  unfold operationArgumentsCoercible
  rw [coerceVariableValues_eq_of_variablesHaveNonNullValues hvalues]
  have hroot : schema.objectType (operation.rootType schema) := by
    cases operation.operationType
    exact hschema.2.1
  apply selectionSetArgumentsCoercible_of_defaults hschema hvalues
    (sourceType := operation.rootType schema) ?_ hroot operation.selectionSet
    (Validation.operationDefinitionValid_selectionSetValid hvalid) (hdefaults values)
  simpa [Schema.typeIncludesObjectBool]
    using object_typeIncludesObjectBool_self schema hroot

mutual
  theorem selectionCoercibleInPossibleTypes_of_validInPossibleTypes
      {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
      {variables : List VariableDefinition} (values : VariableValues) {parentType : Name}
      (hobject : schema.objectType parentType) (selection : Selection)
      (hvalid : selectionValidInPossibleTypes schema variables parentType selection)
      : selectionCoercibleInPossibleTypes schema values parentType selection := by
    have hself : parentType ∈ schema.getPossibleTypes parentType := by
      simpa [Schema.typeIncludesObjectBool]
        using object_typeIncludesObjectBool_self schema hobject
    cases selection with
    | field responseName fieldName arguments directives children =>
        intro _
        obtain ⟨definition, hlookup, harguments, _⟩ :=
          Validation.selectionValid_field_lookup hvalid.1
        have hchildren := hvalid.2
        rw [hlookup] at hchildren ⊢
        exact ⟨omittedNonNullArgumentsHaveDefaults_of_valid harguments,
          fun objectType hpossible =>
            selectionSetCoercibleInPossibleTypes_of_validInPossibleTypes hschema values
              (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema _ _ hpossible)
              children (hchildren objectType hpossible)⟩
    | inlineFragment condition directives children =>
        cases condition with
        | none =>
            intro _
            exact selectionSetCoercibleInPossibleTypes_of_validInPossibleTypes hschema values
              hobject children (hvalid parentType hself)
        | some condition =>
            intro _ hcondition
            have hoverlap : schema.typesOverlapBool parentType condition = true :=
              List.any_eq_true.mpr ⟨parentType, hself, hcondition⟩
            have hmember : parentType ∈ schema.getPossibleTypes condition := by
              simpa [Schema.typeIncludesObjectBool] using hcondition
            exact selectionSetCoercibleInPossibleTypes_of_validInPossibleTypes hschema
              values hobject children (hvalid hoverlap parentType hmember)

  theorem selectionSetCoercibleInPossibleTypes_of_validInPossibleTypes
      {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
      {variables : List VariableDefinition} (values : VariableValues) {parentType : Name}
      (hobject : schema.objectType parentType) (selections : List Selection)
      (hvalid : selectionSetValidInPossibleTypes schema variables parentType selections)
      : selectionSetCoercibleInPossibleTypes schema values parentType selections := by
    cases selections with
    | nil => trivial
    | cons head rest =>
        exact ⟨selectionCoercibleInPossibleTypes_of_validInPossibleTypes hschema values
            hobject head hvalid.1,
          selectionSetCoercibleInPossibleTypes_of_validInPossibleTypes hschema values
            hobject rest hvalid.2⟩
end

theorem operationCoercibleInPossibleTypes_of_fieldsValidInPossibleTypes {schema : Schema}
    (hschema : SchemaWellFormedness.schemaWellFormed schema) {operation : Operation}
    (hvalid : operationFieldsValidInPossibleTypes schema operation)
    : operationCoercibleInPossibleTypes schema operation := by
  intro values
  have hroot : schema.objectType (operation.rootType schema) := by
    cases operation.operationType
    exact hschema.2.1
  exact selectionSetCoercibleInPossibleTypes_of_validInPossibleTypes hschema values hroot
    operation.selectionSet hvalid

end GraphQL.ExecutionReadiness
