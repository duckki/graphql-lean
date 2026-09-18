import Proofs.GraphQL.Execution.ArgumentCoercibility
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ArgumentValues
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.PossibleTypeValidity
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-! Static possible-type validity supplies argument-coercion witnesses for all Boolean cases. -/

namespace GraphQL.NormalForm

/--
Proof-facing witness: every complete Boolean case has a shared supplied-variable
environment making both operations' field arguments coercible. Equivalent Boolean
support lets the left operation's cases cover both sides; base values supply any
non-Boolean variables needed by field arguments.
-/
def completeBoolCasesJointlyCoercible (schema : Schema) (left right : Operation) : Prop :=
  ∀ boolCase,
    completeNormalBoolCase (operationBoolVars left) boolCase
    -> ∃ baseValues,
        operationArgumentsCoercible schema
          (boolCaseVariableValues boolCase baseValues) left
        ∧ operationArgumentsCoercible schema
            (boolCaseVariableValues boolCase baseValues) right

namespace CompleteNormalization

mutual
  theorem selectionArgumentsCoercible_of_possibleTypes
      (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (definitions : List VariableDefinition) (values : Execution.VariableValues)
      (hvalues : Execution.variablesHaveNonNullValues schema definitions values)
      (parentType : Name) (hparent : schema.objectType parentType)
      (selection : Selection)
      (hvalid : selectionValidInPossibleTypes schema definitions parentType selection)
      : selectionArgumentsCoercible schema values parentType selection := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        intro _ field hlookup
        obtain ⟨source, hsource, harguments, _⟩ :=
          Validation.selectionValid_field_lookup hvalid.1
        rw [hlookup] at hsource
        have heq : source = field := Option.some.inj hsource.symm
        subst source
        constructor
        · exact Execution.coerceArgumentValues_success_of_valid hschema
            hvalues (Execution.schemaWellFormed_lookupField_wellFormed hschema hlookup).2 harguments
        · intro runtimeType hpossible
          have hmember
              : runtimeType ∈ schema.getPossibleTypes field.outputType.namedType := by
            simpa [Schema.typeIncludesObjectBool] using hpossible
          have hchildren := hvalid.2
          rw [hlookup] at hchildren
          exact selectionSetArgumentsCoercible_of_possibleTypes schema hschema
            definitions values hvalues runtimeType
            (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema _ _
              hmember)
            children (hchildren runtimeType hmember)
    | inlineFragment condition directives children =>
        intro _ hcondition
        have hself : parentType ∈ schema.getPossibleTypes parentType := by
          simpa [Schema.typeIncludesObjectBool]
            using object_typeIncludesObjectBool_self schema hparent
        cases condition with
        | none =>
            exact selectionSetArgumentsCoercible_of_possibleTypes schema hschema
              definitions values hvalues parentType hparent children
              (hvalid parentType hself)
        | some condition =>
            have hoverlap : schema.typesOverlapBool parentType condition = true := by
              exact List.any_eq_true.mpr ⟨parentType, hself, hcondition⟩
            have hmember : parentType ∈ schema.getPossibleTypes condition := by
              simpa [Schema.typeIncludesObjectBool] using hcondition
            exact selectionSetArgumentsCoercible_of_possibleTypes schema hschema
              definitions values hvalues parentType hparent children
              (hvalid hoverlap parentType hmember)

  theorem selectionSetArgumentsCoercible_of_possibleTypes
      (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (definitions : List VariableDefinition) (values : Execution.VariableValues)
      (hvalues : Execution.variablesHaveNonNullValues schema definitions values)
      (parentType : Name) (hparent : schema.objectType parentType)
      (selections : List Selection)
      (hvalid : selectionSetValidInPossibleTypes schema definitions parentType selections)
      : selectionSetArgumentsCoercible schema values parentType selections := by
    cases selections with
    | nil => trivial
    | cons head rest =>
        exact ⟨selectionArgumentsCoercible_of_possibleTypes schema hschema
          definitions values hvalues parentType hparent head hvalid.1,
          selectionSetArgumentsCoercible_of_possibleTypes schema hschema
            definitions values hvalues parentType hparent rest hvalid.2⟩
end

theorem operationArgumentsCoercible_of_possibleTypes
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {operation : Operation} {values : Execution.VariableValues}
    (hvalues
      : Execution.variablesHaveNonNullValues schema operation.variableDefinitions values)
    (hfields : operationFieldsValidInPossibleTypes schema operation)
    : operationArgumentsCoercible schema values operation := by
  unfold operationArgumentsCoercible
  rw [Execution.coerceVariableValues_eq_of_variablesHaveNonNullValues hvalues]
  have hroot : schema.objectType (operation.rootType schema) := by
    cases operation.operationType
    exact hschema.2.1
  exact selectionSetArgumentsCoercible_of_possibleTypes schema hschema
    operation.variableDefinitions values hvalues (operation.rootType schema) hroot
    operation.selectionSet hfields

theorem completeBoolCasesJointlyCoercible_of_possibleTypes
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleft : Validation.operationDefinitionValid schema left)
    (hleftFields : operationFieldsValidInPossibleTypes schema left)
    (hrightFields : operationFieldsValidInPossibleTypes schema right)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent
          left.variableDefinitions right.variableDefinitions)
    : completeBoolCasesJointlyCoercible schema left right := by
  obtain ⟨baseValues, hvalues⟩ := exists_jointlyTypedBoolCaseValues hschema hleft hdefinitions
  intro boolCase hcomplete
  obtain ⟨hleftValues, hrightValues⟩ := hvalues boolCase hcomplete
  exact ⟨baseValues,
    operationArgumentsCoercible_of_possibleTypes hschema hleftValues hleftFields,
    operationArgumentsCoercible_of_possibleTypes hschema hrightValues
      hrightFields⟩

theorem completeBoolCasesJointlyCoercible_of_completeNormal
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent
          left.variableDefinitions right.variableDefinitions)
    : completeBoolCasesJointlyCoercible schema left right :=
  completeBoolCasesJointlyCoercible_of_possibleTypes hschema hleftValid
    (operationFieldsValidInPossibleTypes_of_completeNormal hschema hleftValid hleftNormal)
    (operationFieldsValidInPossibleTypes_of_completeNormal hschema hrightValid
      hrightNormal)
    hdefinitions

end CompleteNormalization

end GraphQL.NormalForm
