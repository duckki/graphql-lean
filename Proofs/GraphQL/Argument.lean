import GraphQL.Operation

/-! Equivalence-relation algebra for GraphQL field arguments. -/

namespace GraphQL

mutual
  private theorem inputValue_eq_of_structuralEquivalent
      : ∀ {left right : InputValue},
          InputValue.structuralEquivalent left right -> left = right
    | .null, .null, _h => rfl
    | .int left, .int right, h =>
        congrArg InputValue.int h
    | .float left, .float right, h =>
        congrArg InputValue.float h
    | .string left, .string right, h =>
        congrArg InputValue.string h
    | .boolean left, .boolean right, h =>
        congrArg InputValue.boolean h
    | .enum left, .enum right, h =>
        congrArg InputValue.enum h
    | .variable left, .variable right, h =>
        congrArg InputValue.variable h
    | .list left, .list right, h =>
        congrArg InputValue.list (inputValues_eq_of_structuralEquivalent h)
    | .object left, .object right, h =>
        congrArg InputValue.object
          (inputObjectFields_eq_of_structuralEquivalent h)
    | left, right, h => by
        cases left <;> cases right <;>
          simp [InputValue.structuralEquivalent] at h
        all_goals
          first
          | rfl
          | (cases inputValues_eq_of_structuralEquivalent h; rfl)
          | (cases inputObjectFields_eq_of_structuralEquivalent h; rfl)
          | (cases h; rfl)

  private theorem inputValues_eq_of_structuralEquivalent
      : ∀ {left right : List InputValue},
          InputValue.structuralValuesEquivalent left right -> left = right
    | [], [], _h => rfl
    | left :: lefts, right :: rights, h => by
        rcases h with ⟨hleft, hrest⟩
        cases inputValue_eq_of_structuralEquivalent hleft
        cases inputValues_eq_of_structuralEquivalent hrest
        rfl
    | [], _right :: _rights, h => by
        simp [InputValue.structuralValuesEquivalent] at h
    | _left :: _lefts, [], h => by
        simp [InputValue.structuralValuesEquivalent] at h

  private theorem inputObjectFields_eq_of_structuralEquivalent
      : ∀ {left right : List (Name × InputValue)},
          InputValue.structuralObjectFieldsEquivalent left right -> left = right
    | [], [], _h => rfl
    | (leftName, leftValue) :: lefts,
      (rightName, rightValue) :: rights,
      h => by
        rcases h with ⟨hname, hvalue, hrest⟩
        cases hname
        cases inputValue_eq_of_structuralEquivalent hvalue
        cases inputObjectFields_eq_of_structuralEquivalent hrest
        rfl
    | [], _right :: _rights, h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
    | _left :: _lefts, [], h => by
        simp [InputValue.structuralObjectFieldsEquivalent] at h
end

/-- Structural input-value equivalence determines syntax equality. -/
theorem InputValue.eq_of_structuralEquivalent
    {left right : InputValue} (h : left.structuralEquivalent right) : left = right :=
  inputValue_eq_of_structuralEquivalent h

mutual
  private theorem inputValue_structuralEquivalent_refl
      : ∀ value : InputValue, InputValue.structuralEquivalent value value
    | .null => trivial
    | .int _value => rfl
    | .float _value => rfl
    | .string _value => rfl
    | .boolean _value => rfl
    | .enum _value => rfl
    | .variable _name => rfl
    | .list values =>
        inputValues_structuralEquivalent_refl values
    | .object fields =>
        inputObjectFields_structuralEquivalent_refl fields

  private theorem inputValues_structuralEquivalent_refl
      : ∀ values : List InputValue, InputValue.structuralValuesEquivalent values values
    | [] => trivial
    | value :: rest =>
        ⟨
          inputValue_structuralEquivalent_refl value,
          inputValues_structuralEquivalent_refl rest
        ⟩

  private theorem inputObjectFields_structuralEquivalent_refl
      : ∀ fields : List (Name × InputValue),
          InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => trivial
    | (_name, value) :: rest =>
        ⟨
          rfl,
          inputValue_structuralEquivalent_refl value,
          inputObjectFields_structuralEquivalent_refl rest
        ⟩
end

/-- Structural input-value equivalence is reflexive. -/
theorem InputValue.structuralEquivalent_refl (value : InputValue)
    : value.structuralEquivalent value :=
  inputValue_structuralEquivalent_refl value

/-- Structural input-value-list equivalence is reflexive. -/
theorem InputValue.structuralValuesEquivalent_refl (values : List InputValue)
    : structuralValuesEquivalent values values :=
  inputValues_structuralEquivalent_refl values

/-- Structural input-object-field equivalence is reflexive. -/
theorem InputValue.structuralObjectFieldsEquivalent_refl
    (fields : List (Name × InputValue))
    : structuralObjectFieldsEquivalent fields fields :=
  inputObjectFields_structuralEquivalent_refl fields

/-- Structural input-value equivalence is symmetric. -/
theorem InputValue.structuralEquivalent_symm
    {left right : InputValue} (h : left.structuralEquivalent right)
    : right.structuralEquivalent left := by
  cases inputValue_eq_of_structuralEquivalent h
  exact inputValue_structuralEquivalent_refl left

/-- Structural input-value-list equivalence is symmetric. -/
theorem InputValue.structuralValuesEquivalent_symm
    {left right : List InputValue} (h : structuralValuesEquivalent left right)
    : structuralValuesEquivalent right left := by
  cases inputValues_eq_of_structuralEquivalent h
  exact inputValues_structuralEquivalent_refl left

/-- Structural input-object-field equivalence is symmetric. -/
theorem InputValue.structuralObjectFieldsEquivalent_symm
    {left right : List (Name × InputValue)}
    (h : structuralObjectFieldsEquivalent left right)
    : structuralObjectFieldsEquivalent right left := by
  cases inputObjectFields_eq_of_structuralEquivalent h
  exact inputObjectFields_structuralEquivalent_refl left

/-- Structural input-value equivalence is transitive. -/
theorem InputValue.structuralEquivalent_trans
    {left middle right : InputValue}
    (hleft : left.structuralEquivalent middle)
    (hright : middle.structuralEquivalent right)
    : left.structuralEquivalent right := by
  cases inputValue_eq_of_structuralEquivalent hleft
  exact hright

/-- Structural input-value-list equivalence is transitive. -/
theorem InputValue.structuralValuesEquivalent_trans
    {left middle right : List InputValue}
    (hleft : structuralValuesEquivalent left middle)
    (hright : structuralValuesEquivalent middle right)
    : structuralValuesEquivalent left right := by
  cases inputValues_eq_of_structuralEquivalent hleft
  exact hright

/-- Structural input-object-field equivalence is transitive. -/
theorem InputValue.structuralObjectFieldsEquivalent_trans
    {left middle right : List (Name × InputValue)}
    (hleft : structuralObjectFieldsEquivalent left middle)
    (hright : structuralObjectFieldsEquivalent middle right)
    : structuralObjectFieldsEquivalent left right := by
  cases inputObjectFields_eq_of_structuralEquivalent hleft
  exact hright

/-- Canonical input-value equivalence is reflexive. -/
theorem InputValue.equivalent_refl (value : InputValue)
    : value.equivalent value := by
  exact inputValue_structuralEquivalent_refl value.canonical

/-- Canonical input-value equivalence is symmetric. -/
theorem InputValue.equivalent_symm
    {left right : InputValue} (h : left.equivalent right)
    : right.equivalent left := by
  have hequal : left.canonical = right.canonical :=
    inputValue_eq_of_structuralEquivalent h
  rw [InputValue.equivalent, hequal]
  exact inputValue_structuralEquivalent_refl right.canonical

/-- Canonical input-value equivalence is transitive. -/
theorem InputValue.equivalent_trans
    {left middle right : InputValue}
    (hleft : left.equivalent middle)
    (hright : middle.equivalent right)
    : left.equivalent right := by
  have hleftEqual : left.canonical = middle.canonical :=
    inputValue_eq_of_structuralEquivalent hleft
  have hrightEqual : middle.canonical = right.canonical :=
    inputValue_eq_of_structuralEquivalent hright
  rw [InputValue.equivalent, hleftEqual, hrightEqual]
  exact inputValue_structuralEquivalent_refl right.canonical

namespace Argument

/-- Semantic equivalence of one argument is reflexive. -/
theorem equivalent_refl (argument : Argument) : argument.equivalent argument := by
  exact ⟨rfl, InputValue.equivalent_refl argument.value⟩

/-- Semantic equivalence of one argument is symmetric. -/
theorem equivalent_symm {left right : Argument} (h : left.equivalent right)
    : right.equivalent left := by
  exact ⟨h.1.symm, InputValue.equivalent_symm h.2⟩

/-- Semantic equivalence of one argument is transitive. -/
theorem equivalent_trans {left middle right : Argument}
    (hleft : left.equivalent middle)
    (hright : middle.equivalent right)
    : left.equivalent right := by
  exact ⟨hleft.1.trans hright.1,
    InputValue.equivalent_trans hleft.2 hright.2⟩

/-- Bilateral set-containment equivalence of argument lists is reflexive. -/
theorem argumentsEquivalent_refl (arguments : List Argument)
    : argumentsEquivalent arguments arguments := by
  constructor
  · intro argument hargument
    exact ⟨argument, hargument, equivalent_refl argument⟩
  · intro argument hargument
    exact ⟨argument, hargument, equivalent_refl argument⟩

/-- Bilateral set-containment equivalence of argument lists is symmetric. -/
theorem argumentsEquivalent_symm {left right : List Argument}
    (h : argumentsEquivalent left right)
    : argumentsEquivalent right left := by
  constructor
  · intro argument hargument
    rcases h.2 argument hargument with
      ⟨argument', hargument', hequivalent⟩
    exact ⟨argument', hargument', equivalent_symm hequivalent⟩
  · intro argument hargument
    rcases h.1 argument hargument with
      ⟨argument', hargument', hequivalent⟩
    exact ⟨argument', hargument', equivalent_symm hequivalent⟩

/-- Bilateral set-containment equivalence of argument lists is transitive. -/
theorem argumentsEquivalent_trans {left middle right : List Argument}
    (hleft : argumentsEquivalent left middle)
    (hright : argumentsEquivalent middle right)
    : argumentsEquivalent left right := by
  constructor
  · intro argument hargument
    rcases hleft.1 argument hargument with
      ⟨middleArgument, hmiddleArgument, hequivalentLeft⟩
    rcases hright.1 middleArgument hmiddleArgument with
      ⟨rightArgument, hrightArgument, hequivalentRight⟩
    exact ⟨rightArgument, hrightArgument,
      equivalent_trans hequivalentLeft hequivalentRight⟩
  · intro argument hargument
    rcases hright.2 argument hargument with
      ⟨middleArgument, hmiddleArgument, hequivalentRight⟩
    rcases hleft.2 middleArgument hmiddleArgument with
      ⟨leftArgument, hleftArgument, hequivalentLeft⟩
    exact ⟨leftArgument, hleftArgument,
      equivalent_trans hequivalentLeft hequivalentRight⟩

end Argument

end GraphQL
