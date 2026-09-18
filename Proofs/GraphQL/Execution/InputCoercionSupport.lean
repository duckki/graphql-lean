import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Execution.InputCoercionFuel
import Proofs.GraphQL.SchemaWellFormedness.InputInhabited

namespace GraphQL.Execution

def inputCoercionSyntaxSize (values : VariableValues) (value : InputValue) : Nat :=
  referencedVariableValuesCoercionFuel values value + inputValueCoercionFuel value

theorem inputCoercionSyntaxSize_pos (values : VariableValues) (value : InputValue)
    : 0 < inputCoercionSyntaxSize values value := by
  cases value <;> simp [inputCoercionSyntaxSize, inputValueCoercionFuel] <;> omega

mutual
  theorem referencedVariableValuesCoercionFuel_const (values : VariableValues)
      (value : ConstInputValue)
      : referencedVariableValuesCoercionFuel values value.toInputValue = 0 := by
    cases value <;> simp [ConstInputValue.toInputValue, referencedVariableValuesCoercionFuel]
    · exact referencedVariableValuesCoercionFuel_constList values _
    · exact referencedVariableValuesCoercionFuel_constFields values _

  theorem referencedVariableValuesCoercionFuel_constList (values : VariableValues)
      (items : List ConstInputValue)
      : referencedVariableValueListCoercionFuel values
          (ConstInputValue.valuesToInputValues items)
        = 0 := by
    cases items with
    | nil => rfl
    | cons head rest =>
        simp [ConstInputValue.valuesToInputValues,
          referencedVariableValueListCoercionFuel,
          referencedVariableValuesCoercionFuel_const values head,
          referencedVariableValuesCoercionFuel_constList values rest]

  theorem referencedVariableValuesCoercionFuel_constFields (values : VariableValues)
      (fields : List (Name × ConstInputValue))
      : referencedVariableObjectFieldsCoercionFuel values
          (ConstInputValue.objectFieldsToInputFields fields)
        = 0 := by
    cases fields with
    | nil => rfl
    | cons head rest =>
        rcases head with ⟨name, value⟩
        simp [ConstInputValue.objectFieldsToInputFields, referencedVariableObjectFieldsCoercionFuel,
          referencedVariableValuesCoercionFuel_const values value,
          referencedVariableValuesCoercionFuel_constFields values rest]
end

theorem inputCoercionSyntaxSize_mem_list (values : VariableValues)
    {items : List InputValue} {item : InputValue} (hmem : item ∈ items)
    : inputCoercionSyntaxSize values item + 1
      ≤ inputCoercionSyntaxSize values (.list items) := by
  induction items with
  | nil => cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [inputCoercionSyntaxSize, referencedVariableValuesCoercionFuel,
          referencedVariableValueListCoercionFuel, inputValueCoercionFuel, inputValuesCoercionFuel]
        omega
      · have hrest := ih hmem
        simp only [inputCoercionSyntaxSize, referencedVariableValuesCoercionFuel,
          referencedVariableValueListCoercionFuel, inputValueCoercionFuel,
          inputValuesCoercionFuel] at hrest ⊢
        omega

theorem inputCoercionSyntaxSize_mem_object (values : VariableValues)
    {fields : List (Name × InputValue)} {name : Name} {value : InputValue}
    (hmem : (name, value) ∈ fields)
    : inputCoercionSyntaxSize values value + 1
      ≤ inputCoercionSyntaxSize values (.object fields) := by
  induction fields with
  | nil => cases hmem
  | cons head rest ih =>
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst head
        simp [inputCoercionSyntaxSize, referencedVariableValuesCoercionFuel,
          referencedVariableObjectFieldsCoercionFuel, inputValueCoercionFuel,
          inputObjectFieldsCoercionFuel]
        omega
      · have hrest := ih hmem
        cases head
        simp only [inputCoercionSyntaxSize, referencedVariableValuesCoercionFuel,
          referencedVariableObjectFieldsCoercionFuel, inputValueCoercionFuel,
          inputObjectFieldsCoercionFuel] at hrest ⊢
        omega

theorem lookupInputObjectFieldValue_mem {fields : List (Name × InputValue)}
    {name : Name} {value : InputValue}
    (hlookup : lookupInputObjectFieldValue? fields name = some value)
    : (name, value) ∈ fields := by
  induction fields with
  | nil => simp [lookupInputObjectFieldValue?] at hlookup
  | cons head rest ih =>
      rcases head with ⟨fieldName, fieldValue⟩
      simp only [lookupInputObjectFieldValue?] at hlookup
      split at hlookup
      · subst fieldName
        have heq : fieldValue = value := Option.some.inj hlookup
        subst fieldValue
        simp
      · exact List.mem_cons_of_mem _ (ih hlookup)

theorem coerceInputValueListBounded_success_of_items
    {schema : Schema} {values : VariableValues} {fuel : Nat} {inputType : TypeRef}
    {items : List InputValue}
    (hitems
      : ∀ item,
          item ∈ items
          -> ∃ coerced,
              coerceInputValueBounded schema values fuel inputType item
              = .success coerced)
    : ∃ coerced,
        coerceInputValueListBounded schema values fuel inputType items = .ok coerced := by
  induction items with
  | nil => exact ⟨[], by simp [coerceInputValueListBounded]⟩
  | cons head rest ih =>
      obtain ⟨coercedHead, hhead⟩ := hitems head (by simp)
      obtain ⟨coercedRest, hrest⟩ :=
        ih (fun item hmem => hitems item (List.mem_cons_of_mem _ hmem))
      exact ⟨
        coercedHead :: coercedRest,
        by simp [coerceInputValueListBounded, hhead, hrest]
      ⟩

theorem coerceInputObjectFieldsBounded_success_of_fields
    {schema : Schema} {values : VariableValues} {fuel : Nat}
    {definitions : List InputValueDefinition} {fields : List (Name × InputValue)}
    (hfields
      : ∀ definition,
          definition ∈ definitions
          -> coerceInputObjectFieldValueBounded schema values fuel definition fields
              ≠ .error)
    : ∃ coerced,
        coerceInputObjectFieldsBounded schema values fuel definitions fields
        = .ok coerced := by
  induction definitions with
  | nil => exact ⟨[], by simp [coerceInputObjectFieldsBounded]⟩
  | cons head rest ih =>
      obtain ⟨coercedRest, hrest⟩ := ih (fun definition hmem =>
        hfields definition (List.mem_cons_of_mem _ hmem))
      have hhead := hfields head (by simp)
      cases hresult
            : coerceInputObjectFieldValueBounded schema values fuel head fields with
      | error => exact False.elim (hhead hresult)
      | undefined =>
          exact ⟨coercedRest, by rw [coerceInputObjectFieldsBounded_cons, hresult, hrest]⟩
      | success value =>
          exact ⟨
            (head.name, value) :: coercedRest,
            by rw [coerceInputObjectFieldsBounded_cons, hresult, hrest]
          ⟩

theorem coerceInputValueBounded_nonNull
    (schema : Schema) (values : VariableValues) (fuel : Nat) (inner : TypeRef)
    (value : InputValue) (hnotNull : value ≠ .null)
    (hnotVariable : ∀ name, value ≠ .variable name)
    : coerceInputValueBounded schema values (fuel + 1) (.nonNull inner) value
      = coerceInputValueBounded schema values fuel inner value := by
  cases value <;> simp_all [coerceInputValueBounded]

theorem coerceInputValueBounded_singleton
    (schema : Schema) (values : VariableValues) (fuel : Nat) (inner : TypeRef)
    (value : InputValue) (hnotNull : value ≠ .null)
    (hnotVariable : ∀ name, value ≠ .variable name)
    (hnotList : ∀ items, value ≠ .list items)
    : coerceInputValueBounded schema values (fuel + 1) (.list inner) value
      = match coerceInputValueBounded schema values fuel inner value with
        | .undefined => .undefined
        | .success coerced => .success (.list [coerced])
        | .error => .error := by
  cases value <;> simp_all [coerceInputValueBounded]
  all_goals split <;> simp_all

mutual
  theorem ofInputValue_toInputValue (value : ConstInputValue)
      : ConstInputValue.ofInputValue? value.toInputValue = some value := by
    cases value <;> simp [ConstInputValue.toInputValue, ConstInputValue.ofInputValue?]
    · rw [ofInputValues_toInputValues]; rfl
    · rw [ofInputFields_toInputFields]; rfl

  theorem ofInputValues_toInputValues (values : List ConstInputValue)
      : ConstInputValue.inputValuesToConstInputValues?
          (ConstInputValue.valuesToInputValues values)
        = some values := by
    cases values with
    | nil => rfl
    | cons head rest =>
        simp [ConstInputValue.valuesToInputValues, ConstInputValue.inputValuesToConstInputValues?,
          ofInputValue_toInputValue head, ofInputValues_toInputValues rest]

  theorem ofInputFields_toInputFields (fields : List (Name × ConstInputValue))
      : ConstInputValue.inputFieldsToConstInputFields?
          (ConstInputValue.objectFieldsToInputFields fields)
        = some fields := by
    cases fields with
    | nil => rfl
    | cons head rest =>
        rcases head with ⟨name, value⟩
        simp [ConstInputValue.objectFieldsToInputFields, ConstInputValue.inputFieldsToConstInputFields?,
          ofInputValue_toInputValue value, ofInputFields_toInputFields rest]
end

theorem inputObjectFieldsKnownBool_of_known
    {definitions : List InputValueDefinition} {fields : List (Name × InputValue)}
    (hknown
      : ∀ name value,
          (name, value) ∈ fields
          -> (Schema.lookupArgumentDefinition definitions name).isSome = true)
    : inputObjectFieldsKnownBool definitions fields = true := by
  induction fields with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨name, value⟩
      simp only [inputObjectFieldsKnownBool, Bool.and_eq_true]
      exact ⟨
        hknown name value (by simp),
        ih (fun name value hmem => hknown name value (List.mem_cons_of_mem _ hmem))
      ⟩

theorem lookupInputObjectFieldValue_eq_validation (fields : List (Name × InputValue))
    (name : Name)
    : lookupInputObjectFieldValue? fields name
      = Validation.getInputObjectField? fields name := by
  induction fields with
  | nil => rfl
  | cons head rest ih =>
      cases head
      simp [lookupInputObjectFieldValue?, Validation.getInputObjectField?, ih]

-- The reserve covers schema defaults. Remaining syntax pays for a full type-depth
-- traversal at each node; the current node needs only its own type depth.
def inputCoercionBudget (reserve width : Nat) (values : VariableValues)
    (inputType : TypeRef) (value : InputValue)
    : Nat :=
  reserve
  + (inputCoercionSyntaxSize values value - 1) * width
  + inputTypeCoercionDepth inputType

theorem inputCoercionBudget_child (reserve width : Nat) (values : VariableValues)
    {parentType childType : TypeRef} {parent child : InputValue}
    (hsize
      : inputCoercionSyntaxSize values child + 1 ≤ inputCoercionSyntaxSize values parent)
    (hwidth : inputTypeCoercionDepth childType ≤ width)
    : inputCoercionBudget reserve width values childType child + 1
      ≤ inputCoercionBudget reserve width values parentType parent := by
  have hpositive := inputCoercionSyntaxSize_pos values child
  have hdepth := inputTypeCoercionDepth_pos parentType
  have hmul := Nat.mul_le_mul_right width (show inputCoercionSyntaxSize values child ≤
    inputCoercionSyntaxSize values parent - 1 by omega)
  have hsplit : inputCoercionSyntaxSize values child =
      (inputCoercionSyntaxSize values child - 1) + 1 := by omega
  have hsum := congrArg (fun n => n * width) hsplit
  simp only [Nat.add_mul, Nat.one_mul] at hsum
  unfold inputCoercionBudget
  omega

end GraphQL.Execution
