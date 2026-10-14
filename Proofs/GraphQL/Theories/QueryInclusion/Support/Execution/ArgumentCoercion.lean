import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Execution

mutual
  theorem inputValue_structuralEquivalent_eq
      : ∀ {left right : InputValue},
          InputValue.structuralEquivalent left right -> left = right := by
    intro left right h
    cases left <;> cases right <;>
      simp [InputValue.structuralEquivalent] at h ⊢
    all_goals
      first
      | exact inputValues_structuralEquivalent_eq h
      | exact inputObjectFields_structuralEquivalent_eq h
      | exact h

  theorem inputValues_structuralEquivalent_eq
      : ∀ {left right : List InputValue},
          InputValue.structuralValuesEquivalent left right -> left = right
    | [], [], _h => rfl
    | left :: lefts, right :: rights, h => by
        simp [InputValue.structuralValuesEquivalent] at h
        rw [inputValue_structuralEquivalent_eq h.1,
          inputValues_structuralEquivalent_eq h.2]

  theorem inputObjectFields_structuralEquivalent_eq
      : ∀ {left right : List (Name × InputValue)},
          InputValue.structuralObjectFieldsEquivalent left right -> left = right
    | [], [], _h => rfl
    | (leftName, leftValue) :: lefts,
        (rightName, rightValue) :: rights, h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
        rw [h.1, inputValue_structuralEquivalent_eq h.2.1,
          inputObjectFields_structuralEquivalent_eq h.2.2]
end

theorem inputValue_canonical_eq_of_equivalent {left right : InputValue}
    (h : left.equivalent right)
    : left.canonical = right.canonical :=
  inputValue_structuralEquivalent_eq h

mutual
  private theorem inputValue_structuralEquivalent_refl_forCoercion
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
          inputValues_structuralEquivalent_refl_forCoercion values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputObjectFields_structuralEquivalent_refl_forCoercion fields]

  private theorem inputValues_structuralEquivalent_refl_forCoercion
      : ∀ values, InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl_forCoercion value,
          inputValues_structuralEquivalent_refl_forCoercion rest]

  private theorem inputObjectFields_structuralEquivalent_refl_forCoercion
      : ∀ fields, InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl_forCoercion value,
          inputObjectFields_structuralEquivalent_refl_forCoercion rest]
end

private theorem inputValue_equivalent_trans_forCoercion
    {left middle right : InputValue}
    (hleft : left.equivalent middle) (hright : middle.equivalent right)
    : left.equivalent right := by
  have hleftCanonical := inputValue_canonical_eq_of_equivalent hleft
  have hrightCanonical := inputValue_canonical_eq_of_equivalent hright
  unfold InputValue.equivalent
  rw [hleftCanonical, hrightCanonical]
  exact inputValue_structuralEquivalent_refl_forCoercion right.canonical

theorem CoercedArgument.argumentsEquivalent_trans
    {left middle right : CoercedArguments}
    (hleft : CoercedArgument.argumentsEquivalent left middle)
    (hright : CoercedArgument.argumentsEquivalent middle right)
    : CoercedArgument.argumentsEquivalent left right := by
  constructor
  · intro argument hargument
    rcases hleft.1 argument hargument with
      ⟨middleArgument, hmiddle, hleftEquivalent⟩
    rcases hright.1 middleArgument hmiddle with
      ⟨rightArgument, hrightArgument, hrightEquivalent⟩
    exact ⟨rightArgument, hrightArgument,
      ⟨hleftEquivalent.1.trans hrightEquivalent.1,
        inputValue_equivalent_trans_forCoercion hleftEquivalent.2
          hrightEquivalent.2⟩⟩
  · intro argument hargument
    rcases hright.2 argument hargument with
      ⟨middleArgument, hmiddle, hrightEquivalent⟩
    rcases hleft.2 middleArgument hmiddle with
      ⟨leftArgument, hleftArgument, hleftEquivalent⟩
    exact ⟨leftArgument, hleftArgument,
      ⟨hleftEquivalent.1.trans hrightEquivalent.1,
        inputValue_equivalent_trans_forCoercion hleftEquivalent.2
          hrightEquivalent.2⟩⟩

def coerceAndResolveFieldValue (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fieldDefinition : FieldDefinition)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : ResolverValue ObjectRef)
    : Option (ResolverValue ObjectRef) :=
  match coerceArgumentValues schema variableValues fieldDefinition.arguments
          arguments with
  | .error => none
  | .success coercedArguments =>
      resolveFieldValue resolvers parentType fieldName coercedArguments source

def resolveFieldValueByName (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (parentType fieldName : Name)
    (arguments : List Argument) (source : ResolverValue ObjectRef)
    : Option (ResolverValue ObjectRef) :=
  match schema.lookupField parentType fieldName with
  | none => none
  | some fieldDefinition =>
      coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
        parentType fieldName arguments source

end GraphQL.Execution
