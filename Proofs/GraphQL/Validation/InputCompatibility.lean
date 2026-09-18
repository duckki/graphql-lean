import GraphQL.Validation

/-! Constant input values remain valid at compatible variable-use locations. -/

namespace GraphQL.Validation

private theorem inputType_of_nonNull {schema : Schema} {inner : TypeRef}
    (h : (TypeRef.nonNull inner).isInputType schema)
    : inner.isInputType schema := by
  cases inner with
  | named _ => exact h
  | list _ => exact h
  | nonNull _ => exact False.elim h

theorem constInputValue_correctType_of_compatible
    {schema : Schema} {value : ConstInputValue} {variableType locationType : TypeRef}
    (hcorrect : Schema.ConstInputValueIsCorrectType schema value variableType)
    (hinput : locationType.isInputType schema)
    (hcompatible : areInputTypesCompatible variableType locationType)
    : Schema.ConstInputValueIsCorrectType schema value locationType := by
  induction variableType generalizing locationType value with
  | named name =>
      cases locationType with
      | named name' =>
          have heq : name = name' := hcompatible
          subst name'
          exact hcorrect
      | list _ => exact False.elim hcompatible
      | nonNull _ => exact False.elim hcompatible
  | list inner ih =>
      cases locationType with
      | named _ => exact False.elim hcompatible
      | nonNull _ => exact False.elim hcompatible
      | list target =>
          cases hcorrect with
          | nullList _ _ => exact .nullList _ hinput
          | list items _ _ hitems =>
              exact .list _ _ hinput
                (fun item hmem => ih (hitems item hmem) hinput hcompatible)
          | objectAsListItem fields _ _ hitem =>
              cases hitem with
              | intro _ _ hvalue =>
                  exact .objectAsListItem _ _ hinput
                    (.intro _ _ (ih hvalue hinput hcompatible))
          | singletonListItem value _ _ hnotList hnotObject hnotNull hitem =>
              exact .singletonListItem _ _ hinput hnotList hnotObject hnotNull
                (ih hitem hinput hcompatible)
  | nonNull inner ih =>
      cases hcorrect with
      | nonNull value _ _ hnotNull hinner =>
          cases locationType with
          | named _ => exact ih hinner hinput hcompatible
          | list _ => exact ih hinner hinput hcompatible
          | nonNull target =>
              exact .nonNull _ _ hinput hnotNull
                (ih hinner (inputType_of_nonNull hinput) hcompatible)

theorem constInputValue_correctType_of_variableUsageAllowed
    {schema : Schema} {value : ConstInputValue} {definition : VariableDefinition}
    {locationType : TypeRef} {locationDefault : Option ConstInputValue}
    (hcorrect : Schema.ConstInputValueIsCorrectType schema value definition.typeRef)
    (hnonnull : value ≠ .null)
    (husage : variableUsageAllowed schema definition locationType locationDefault)
    : Schema.ConstInputValueIsCorrectType schema value locationType := by
  rcases husage with ⟨hvariable, hlocation, husage⟩
  cases locationType with
  | named _ => exact constInputValue_correctType_of_compatible hcorrect hlocation husage
  | list _ => exact constInputValue_correctType_of_compatible hcorrect hlocation husage
  | nonNull inner =>
      cases htype : definition.typeRef with
      | nonNull variableInner =>
          rw [htype] at hcorrect husage
          exact constInputValue_correctType_of_compatible hcorrect hlocation husage
      | named name =>
          rw [htype] at hcorrect husage
          exact .nonNull _ _ hlocation hnonnull
            (constInputValue_correctType_of_compatible hcorrect
              (inputType_of_nonNull hlocation) husage.2)
      | list variableInner =>
          rw [htype] at hcorrect husage
          exact .nonNull _ _ hlocation hnonnull
            (constInputValue_correctType_of_compatible hcorrect
              (inputType_of_nonNull hlocation) husage.2)

end GraphQL.Validation
