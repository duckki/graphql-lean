import Proofs.GraphQL.Theories.ExecutionReadiness.ArgumentDefaults
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ArgumentValues
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.PossibleTypeValidity
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeTypes

/-! Concrete argument defaults supply argument-coercion witnesses for all Boolean cases. -/

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

theorem completeBoolCasesJointlyCoercible_of_possibleTypes
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleft : Validation.operationDefinitionValid schema left)
    (hright : Validation.operationDefinitionValid schema right)
    (hleftFields : operationCoercibleInPossibleTypes schema left)
    (hrightFields : operationCoercibleInPossibleTypes schema right)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent
          left.variableDefinitions right.variableDefinitions)
    : completeBoolCasesJointlyCoercible schema left right := by
  obtain ⟨baseValues, hvalues⟩ := exists_jointlyTypedBoolCaseValues hschema hleft hdefinitions
  intro boolCase hcomplete
  obtain ⟨hleftValues, hrightValues⟩ := hvalues boolCase hcomplete
  exact ⟨baseValues,
    ExecutionReadiness.operationArgumentsCoercible_of_defaults hschema hleft
      hleftValues hleftFields,
    ExecutionReadiness.operationArgumentsCoercible_of_defaults hschema hright hrightValues
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
  completeBoolCasesJointlyCoercible_of_possibleTypes hschema hleftValid hrightValid
    (ExecutionReadiness.operationCoercibleInPossibleTypes_of_fieldsValidInPossibleTypes
      hschema
      (operationFieldsValidInPossibleTypes_of_completeNormal hschema hleftValid
        hleftNormal))
    (ExecutionReadiness.operationCoercibleInPossibleTypes_of_fieldsValidInPossibleTypes
      hschema
      (operationFieldsValidInPossibleTypes_of_completeNormal hschema hrightValid
        hrightNormal))
    hdefinitions

end CompleteNormalization

end GraphQL.NormalForm
