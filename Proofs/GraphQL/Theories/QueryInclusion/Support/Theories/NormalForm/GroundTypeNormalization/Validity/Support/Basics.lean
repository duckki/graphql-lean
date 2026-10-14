import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.NormalForm.GroundTypeNormalization

mutual
  theorem inputValue_structuralEquivalent_refl
      : ∀ value, InputValue.structuralEquivalent value value
    | .null => by simp [InputValue.structuralEquivalent]
    | .int _ => by simp [InputValue.structuralEquivalent]
    | .float _ => by simp [InputValue.structuralEquivalent]
    | .string _ => by simp [InputValue.structuralEquivalent]
    | .boolean _ => by simp [InputValue.structuralEquivalent]
    | .enum _ => by simp [InputValue.structuralEquivalent]
    | .variable _ => by simp [InputValue.structuralEquivalent]
    | .list values => by
        simp [InputValue.structuralEquivalent,
          inputValues_structuralEquivalent_refl values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputObjectFields_structuralEquivalent_refl fields]

  theorem inputValues_structuralEquivalent_refl
      : ∀ values, InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValues_structuralEquivalent_refl rest]

  theorem inputObjectFields_structuralEquivalent_refl
      : ∀ fields, InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputObjectFields_structuralEquivalent_refl rest]
end

theorem inputValue_equivalent_refl (value : InputValue) : value.equivalent value := by
  exact inputValue_structuralEquivalent_refl value.canonical

theorem argument_equivalent_refl (argument : Argument)
    : argument.equivalent argument := by
  exact ⟨rfl, inputValue_equivalent_refl argument.value⟩

theorem argumentsEquivalent_refl (arguments : List Argument)
    : Argument.argumentsEquivalent arguments arguments := by
  constructor
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl argument⟩
  · intro argument hargument
    exact ⟨argument, hargument, argument_equivalent_refl argument⟩

end GraphQL.NormalForm.GroundTypeNormalization
