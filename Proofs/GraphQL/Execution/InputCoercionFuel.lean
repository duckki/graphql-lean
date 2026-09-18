import GraphQL.Execution

/-! Type-wrapper bounds for input coercion. -/

namespace GraphQL.Execution

def wrapSingletonInput (inputType : TypeRef) (value : CoercedInputValue)
    : CoercedInputValue :=
  match inputType with
  | .named _ => value
  | .nonNull inner => wrapSingletonInput inner value
  | .list inner => .list [wrapSingletonInput inner value]

theorem inputTypeCoercionDepth_pos (inputType : TypeRef)
    : 0 < inputTypeCoercionDepth inputType := by
  cases inputType <;> simp [inputTypeCoercionDepth]

theorem coerceInputValueBounded_int (schema : Schema) (values : VariableValues)
    (inputType : TypeRef) (value : Int) (fuel : Nat)
    (hlookup : schema.lookupInputObject inputType.namedType = none)
    (hfuel : inputTypeCoercionDepth inputType ≤ fuel)
    : coerceInputValueBounded schema values fuel inputType (.int value)
      = .success (wrapSingletonInput inputType (.int value)) := by
  induction inputType generalizing fuel with
  | named name =>
      cases fuel with
      | zero => simp [inputTypeCoercionDepth] at hfuel
      | succ fuel =>
          simp [coerceInputValueBounded, TypeRef.namedType] at hlookup ⊢
          simp [hlookup, ConstInputValue.ofInputValue?, wrapSingletonInput]
  | list inner ih =>
      cases fuel with
      | zero => simp [inputTypeCoercionDepth] at hfuel
      | succ fuel =>
          have hinner : inputTypeCoercionDepth inner ≤ fuel := by
            simpa [inputTypeCoercionDepth] using hfuel
          simp [coerceInputValueBounded, ih fuel hlookup hinner, wrapSingletonInput]
  | nonNull inner ih =>
      cases fuel with
      | zero => simp [inputTypeCoercionDepth] at hfuel
      | succ fuel =>
          have hinner : inputTypeCoercionDepth inner ≤ fuel := by
            simpa [inputTypeCoercionDepth] using hfuel
          simp [coerceInputValueBounded, ih fuel hlookup hinner, wrapSingletonInput]

theorem inputTypeCoercionDepth_le_fuel (schema : Schema) (values : VariableValues)
    (inputType : TypeRef) (value : InputValue)
    : inputTypeCoercionDepth inputType
      ≤ coerceInputValueFuel schema values inputType value := by
  unfold coerceInputValueFuel
  have hpositive : 0 < schemaInputCoercionFuel schema
      + referencedVariableValuesCoercionFuel values value + inputValueCoercionFuel value := by
    unfold schemaInputCoercionFuel
    omega
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_mul_of_pos_left _ hpositive)

theorem coerceInputValue_int (schema : Schema) (values : VariableValues)
    (inputType : TypeRef) (value : Int)
    (hlookup : schema.lookupInputObject inputType.namedType = none)
    : coerceInputValue schema values inputType (.int value)
      = .success (wrapSingletonInput inputType (.int value)) := by
  exact coerceInputValueBounded_int schema values inputType value _ hlookup
    (inputTypeCoercionDepth_le_fuel schema values inputType _)

end GraphQL.Execution
