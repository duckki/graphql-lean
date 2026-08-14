import GraphQL.Execution
import Proofs.GraphQL.Validation.SelectionValidity

/-!
Proof-facing relations and scope predicates for coerced resolver arguments.

`InputValue.canonical` is used here only to reason about the semantic relation
`InputValue.equivalent`. The spec-facing coercer in `GraphQL.Execution` operates on
the supplied values directly and never canonicalizes them.
-/

namespace GraphQL

namespace Execution

mutual
  def selectionArgumentsNodup : Selection -> Prop
    | .field _responseName _fieldName arguments _directives selectionSet =>
        (arguments.map Argument.name).Nodup ∧ selectionSetArgumentsNodup selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetArgumentsNodup selectionSet

  def selectionSetArgumentsNodup : List Selection -> Prop
    | [] => True
    | selection :: rest =>
        selectionArgumentsNodup selection ∧ selectionSetArgumentsNodup rest
end

theorem selectionArgumentsNodup_of_mem
    {selection : Selection} {selectionSet : List Selection}
    : selectionSetArgumentsNodup selectionSet
      -> selection ∈ selectionSet
      -> selectionArgumentsNodup selection := by
  intro hnodup hmem
  induction selectionSet with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases hnodup with ⟨hhead, hrest⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hhead
      · exact ih hrest hmem

theorem argumentsValid_argumentsNodup
    {schema : Schema} {definitions : List InputValueDefinition}
    {variableDefinitions : List VariableDefinition} {arguments : List Argument}
    : Validation.argumentsValid schema definitions variableDefinitions arguments
      -> (arguments.map Argument.name).Nodup := by
  intro hvalid
  exact hvalid.1

mutual
  theorem selectionArgumentsNodup_of_selectionValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name} {selection : Selection}
      : Validation.selectionValid schema variableDefinitions parentType selection
        -> selectionArgumentsNodup selection := by
    intro hvalid
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, _hlookup, harguments, hselectionSet⟩
        constructor
        · exact argumentsValid_argumentsNodup harguments
        · simp [Validation.fieldSelectionSetValid] at hselectionSet
          rcases hselectionSet.2 with hleaf | hcomposite
          · rw [hleaf.2]
            simp [selectionSetArgumentsNodup]
          · exact selectionSetArgumentsNodup_of_selectionSetValid hcomposite.2.2
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            exact selectionSetArgumentsNodup_of_selectionSetValid
              (Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid)
        | some typeCondition =>
            exact selectionSetArgumentsNodup_of_selectionSetValid
              (Validation.selectionValid_inlineFragment_some_selectionSetValid hvalid)

  theorem selectionSetArgumentsNodup_of_selectionSetValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name} {selectionSet : List Selection}
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
        -> selectionSetArgumentsNodup selectionSet := by
    intro hvalid
    cases selectionSet with
    | nil => simp [selectionSetArgumentsNodup]
    | cons selection rest =>
        simp [Validation.selectionSetValid] at hvalid
        constructor
        · exact selectionArgumentsNodup_of_selectionValid hvalid.1
        · apply selectionSetArgumentsNodup_of_selectionSetValid
          simp [Validation.selectionSetValid]
          exact hvalid.2
end

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

private theorem inputValue_equivalent_refl_forCoercion (value : InputValue)
    : value.equivalent value := by
  exact inputValue_structuralEquivalent_refl_forCoercion value.canonical

private theorem inputValue_equivalent_symm_forCoercion
    {left right : InputValue} (hequivalent : left.equivalent right)
    : right.equivalent left := by
  have hcanonical := inputValue_canonical_eq_of_equivalent hequivalent
  unfold InputValue.equivalent
  rw [hcanonical]
  exact inputValue_structuralEquivalent_refl_forCoercion right.canonical

private theorem inputValue_equivalent_trans_forCoercion
    {left middle right : InputValue}
    (hleft : left.equivalent middle) (hright : middle.equivalent right)
    : left.equivalent right := by
  have hleftCanonical := inputValue_canonical_eq_of_equivalent hleft
  have hrightCanonical := inputValue_canonical_eq_of_equivalent hright
  unfold InputValue.equivalent
  rw [hleftCanonical, hrightCanonical]
  exact inputValue_structuralEquivalent_refl_forCoercion right.canonical

private theorem inputValue_equivalent_of_canonical_eq_forCoercion
    {left right : InputValue} (hcanonical : left.canonical = right.canonical)
    : left.equivalent right := by
  unfold InputValue.equivalent
  rw [hcanonical]
  exact inputValue_structuralEquivalent_refl_forCoercion right.canonical

private theorem optionRel_inputValueEquivalent_iff_canonical_map_eq
    {left right : Option InputValue}
    : Option.Rel InputValue.equivalent left right
      ↔ left.map InputValue.canonical = right.map InputValue.canonical := by
  cases left with
  | none =>
      cases right with
      | none => exact ⟨fun _ => rfl, fun _ => .none⟩
      | some right =>
          constructor <;> intro h <;> cases h
  | some left =>
      cases right with
      | none =>
          constructor <;> intro h <;> cases h
      | some right =>
          constructor
          · intro h
            cases h with
            | some hequivalent =>
                exact congrArg some
                  (inputValue_canonical_eq_of_equivalent hequivalent)
          · intro h
            exact .some (inputValue_equivalent_of_canonical_eq_forCoercion
              (Option.some.inj h))

private theorem lookupInputObjectFieldValue?_insertObjectFieldSorted
    (field : Name × InputValue)
    : ∀ fields name,
        lookupInputObjectFieldValue?
          (InputValue.insertObjectFieldSorted field fields) name
        = if field.1 = name then
            some field.2
          else
            lookupInputObjectFieldValue? fields name
  | [], name => by
      simp [InputValue.insertObjectFieldSorted, lookupInputObjectFieldValue?]
  | candidate :: rest, name => by
      by_cases hle : field.1 <= candidate.1
      · rw [InputValue.insertObjectFieldSorted, if_pos hle]
        by_cases hfield : field.1 = name <;>
          simp [lookupInputObjectFieldValue?, hfield]
      · rw [InputValue.insertObjectFieldSorted, if_neg hle]
        by_cases hcandidate : candidate.1 = name
        · by_cases hfield : field.1 = name
          · exact False.elim (hle (by
              rw [hfield, hcandidate]
              exact String.le_refl name))
          · simp [lookupInputObjectFieldValue?, hcandidate, hfield]
        · simp [lookupInputObjectFieldValue?, hcandidate,
            lookupInputObjectFieldValue?_insertObjectFieldSorted field rest]

private theorem lookupInputObjectFieldValue?_sortObjectFieldsByName
    : ∀ fields name,
        lookupInputObjectFieldValue? (InputValue.sortObjectFieldsByName fields) name
        = lookupInputObjectFieldValue? fields name
  | [], name => by
      simp [InputValue.sortObjectFieldsByName, lookupInputObjectFieldValue?]
  | field :: rest, name => by
      simp [InputValue.sortObjectFieldsByName,
        lookupInputObjectFieldValue?_insertObjectFieldSorted,
        lookupInputObjectFieldValue?_sortObjectFieldsByName,
        lookupInputObjectFieldValue?]

private theorem lookupInputObjectFieldValue?_canonicalObjectFields
    : ∀ fields name,
        lookupInputObjectFieldValue? (InputValue.canonicalObjectFields fields) name
        = (lookupInputObjectFieldValue? fields name).map InputValue.canonical
  | [], name => by
      simp [InputValue.canonicalObjectFields, lookupInputObjectFieldValue?]
  | (fieldName, value) :: rest, name => by
      by_cases hname : fieldName = name
      · simp [InputValue.canonicalObjectFields, lookupInputObjectFieldValue?, hname]
      · simp [InputValue.canonicalObjectFields, lookupInputObjectFieldValue?, hname,
          lookupInputObjectFieldValue?_canonicalObjectFields]

private theorem lookupInputObjectFieldValue?_canonical_map_eq
    {left right : List (Name × InputValue)}
    (hcanonical
      : InputValue.sortObjectFieldsByName (InputValue.canonicalObjectFields left)
        = InputValue.sortObjectFieldsByName (InputValue.canonicalObjectFields right))
    (name : Name)
    : (lookupInputObjectFieldValue? left name).map InputValue.canonical
      = (lookupInputObjectFieldValue? right name).map InputValue.canonical := by
  calc
    (lookupInputObjectFieldValue? left name).map InputValue.canonical
        = lookupInputObjectFieldValue? (InputValue.canonicalObjectFields left) name :=
      (lookupInputObjectFieldValue?_canonicalObjectFields left name).symm
    _ = lookupInputObjectFieldValue?
          (InputValue.sortObjectFieldsByName (InputValue.canonicalObjectFields left))
          name :=
      (lookupInputObjectFieldValue?_sortObjectFieldsByName
        (InputValue.canonicalObjectFields left) name).symm
    _ = lookupInputObjectFieldValue?
          (InputValue.sortObjectFieldsByName (InputValue.canonicalObjectFields right))
          name := by
      rw [hcanonical]
    _ = lookupInputObjectFieldValue? (InputValue.canonicalObjectFields right) name :=
      lookupInputObjectFieldValue?_sortObjectFieldsByName
        (InputValue.canonicalObjectFields right) name
    _ = (lookupInputObjectFieldValue? right name).map InputValue.canonical :=
      lookupInputObjectFieldValue?_canonicalObjectFields right name

private theorem optionGetD_canonical_eq
    {left right : Option InputValue}
    (hcanonical : left.map InputValue.canonical = right.map InputValue.canonical)
    : (left.getD .null).canonical = (right.getD .null).canonical := by
  cases left <;> cases right <;> simp at hcanonical ⊢
  exact hcanonical

private def coercedInputObjectFieldValue? (schema : Schema)
    (variableValues : VariableValues) (fuel : Nat)
    (definition : InputValueDefinition) (fields : List (Name × InputValue))
    : Option InputValue :=
  match match lookupInputObjectFieldValue? fields definition.name with
        | some value =>
            coerceInputValueBounded schema variableValues fuel definition.inputType value
        | none => none with
  | some value => some value
  | none =>
      definition.defaultValue.map
        (fun value =>
          (coerceInputValueBounded schema variableValues fuel definition.inputType
            value.toInputValue).getD
            .null)

private theorem coercedInputObjectFieldValue?_canonical_map_eq
    (schema : Schema) {left right : VariableValues} (fuel : Nat)
    (hcoerce
      : ∀ inputType leftValue rightValue,
          leftValue.canonical = rightValue.canonical
          -> (coerceInputValueBounded schema left fuel inputType leftValue).map
                InputValue.canonical
              = (coerceInputValueBounded schema right fuel inputType rightValue).map
                  InputValue.canonical)
    (definition : InputValueDefinition)
    {leftFields rightFields : List (Name × InputValue)}
    (hfields
      : (lookupInputObjectFieldValue? leftFields definition.name).map InputValue.canonical
        = (lookupInputObjectFieldValue? rightFields definition.name).map
            InputValue.canonical)
    : (coercedInputObjectFieldValue? schema left fuel definition leftFields).map
        InputValue.canonical
      = (coercedInputObjectFieldValue? schema right fuel definition rightFields).map
          InputValue.canonical := by
  cases hleftLookup : lookupInputObjectFieldValue? leftFields definition.name with
  | none =>
      cases hrightLookup : lookupInputObjectFieldValue? rightFields definition.name with
      | some rightValue => simp [hleftLookup, hrightLookup] at hfields
      | none =>
          cases hdefault : definition.defaultValue with
          | none =>
              simp [coercedInputObjectFieldValue?, hleftLookup, hrightLookup,
                hdefault]
          | some defaultValue =>
              have hdefaultCoerced := hcoerce definition.inputType
                defaultValue.toInputValue defaultValue.toInputValue rfl
              have hdefaultValue := optionGetD_canonical_eq hdefaultCoerced
              simp [coercedInputObjectFieldValue?, hleftLookup, hrightLookup,
                hdefault, hdefaultValue]
  | some leftValue =>
      cases hrightLookup : lookupInputObjectFieldValue? rightFields definition.name with
      | none => simp [hleftLookup, hrightLookup] at hfields
      | some rightValue =>
          have hvalue : leftValue.canonical = rightValue.canonical := by
            simpa [hleftLookup, hrightLookup] using hfields
          have hcoerced := hcoerce definition.inputType leftValue rightValue hvalue
          cases hleftCoerced
                : coerceInputValueBounded schema left fuel definition.inputType
                    leftValue with
          | none =>
              cases hrightCoerced
                    : coerceInputValueBounded schema right fuel definition.inputType
                        rightValue with
              | some rightCoerced =>
                  simp [hleftCoerced, hrightCoerced] at hcoerced
              | none =>
                  cases hdefault : definition.defaultValue with
                  | none =>
                      simp [coercedInputObjectFieldValue?, hleftLookup, hrightLookup,
                        hleftCoerced, hrightCoerced, hdefault]
                  | some defaultValue =>
                      have hdefaultCoerced := hcoerce definition.inputType
                        defaultValue.toInputValue defaultValue.toInputValue rfl
                      have hdefaultValue := optionGetD_canonical_eq hdefaultCoerced
                      simp [coercedInputObjectFieldValue?, hleftLookup, hrightLookup,
                        hleftCoerced, hrightCoerced, hdefault, hdefaultValue]
          | some leftCoerced =>
              cases hrightCoerced
                    : coerceInputValueBounded schema right fuel definition.inputType
                        rightValue with
              | none => simp [hleftCoerced, hrightCoerced] at hcoerced
              | some rightCoerced =>
                  simpa [coercedInputObjectFieldValue?, hleftLookup, hrightLookup,
                    hleftCoerced, hrightCoerced] using hcoerced

private theorem inputObjectFieldsCoercionFuel_insertObjectFieldSorted
    (field : Name × InputValue)
    : ∀ fields,
        inputObjectFieldsCoercionFuel (InputValue.insertObjectFieldSorted field fields)
        = inputValueCoercionFuel field.2 + inputObjectFieldsCoercionFuel fields
  | [] => by simp [InputValue.insertObjectFieldSorted,
      inputObjectFieldsCoercionFuel]
  | candidate :: rest => by
      by_cases hname : field.1 <= candidate.1
      · simp [InputValue.insertObjectFieldSorted, hname,
          inputObjectFieldsCoercionFuel]
      · simp [InputValue.insertObjectFieldSorted, hname,
          inputObjectFieldsCoercionFuel,
          inputObjectFieldsCoercionFuel_insertObjectFieldSorted field rest,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem inputObjectFieldsCoercionFuel_sortObjectFieldsByName
    : ∀ fields,
        inputObjectFieldsCoercionFuel (InputValue.sortObjectFieldsByName fields)
        = inputObjectFieldsCoercionFuel fields
  | [] => by simp [InputValue.sortObjectFieldsByName,
      inputObjectFieldsCoercionFuel]
  | field :: rest => by
      simp [InputValue.sortObjectFieldsByName,
        inputObjectFieldsCoercionFuel,
        inputObjectFieldsCoercionFuel_insertObjectFieldSorted,
        inputObjectFieldsCoercionFuel_sortObjectFieldsByName rest]

mutual
  private theorem inputValueCoercionFuel_canonical
      : ∀ value, inputValueCoercionFuel value.canonical = inputValueCoercionFuel value
    | .null => rfl
    | .int _ => rfl
    | .float _ => rfl
    | .string _ => rfl
    | .boolean _ => rfl
    | .enum _ => rfl
    | .variable _ => rfl
    | .list values => by
        simp [InputValue.canonical, inputValueCoercionFuel,
          inputValuesCoercionFuel_canonical values]
    | .object fields => by
        simp [InputValue.canonical, inputValueCoercionFuel,
          inputObjectFieldsCoercionFuel_sortObjectFieldsByName,
          inputObjectFieldsCoercionFuel_canonical fields]

  private theorem inputValuesCoercionFuel_canonical
      : ∀ values,
          inputValuesCoercionFuel (InputValue.canonicalValues values)
          = inputValuesCoercionFuel values
    | [] => rfl
    | value :: rest => by
        simp [InputValue.canonicalValues, inputValuesCoercionFuel,
          inputValueCoercionFuel_canonical value,
          inputValuesCoercionFuel_canonical rest]

  private theorem inputObjectFieldsCoercionFuel_canonical
      : ∀ fields,
          inputObjectFieldsCoercionFuel (InputValue.canonicalObjectFields fields)
          = inputObjectFieldsCoercionFuel fields
    | [] => rfl
    | (name, value) :: rest => by
        simp [InputValue.canonicalObjectFields, inputObjectFieldsCoercionFuel,
          inputValueCoercionFuel_canonical value,
          inputObjectFieldsCoercionFuel_canonical rest]
end

private theorem inputValueCoercionFuel_eq_of_equivalent
    {left right : InputValue} (hequivalent : left.equivalent right)
    : inputValueCoercionFuel left = inputValueCoercionFuel right := by
  calc
    inputValueCoercionFuel left = inputValueCoercionFuel left.canonical :=
      (inputValueCoercionFuel_canonical left).symm
    _ = inputValueCoercionFuel right.canonical := by
      rw [inputValue_canonical_eq_of_equivalent hequivalent]
    _ = inputValueCoercionFuel right :=
      inputValueCoercionFuel_canonical right

-- Variable environments are equivalent for input coercion when lookup is
-- extensionally equivalent and the bounded coercer receives the same fuel.
def variableValuesCoercionEquivalent (left right : VariableValues) : Prop :=
  (∀ name,
    Option.Rel InputValue.equivalent
      (lookupVariableValue? left name) (lookupVariableValue? right name))
  ∧ variableValuesCoercionFuel left = variableValuesCoercionFuel right

theorem variableValuesCoercionEquivalent_refl (values : VariableValues)
    : variableValuesCoercionEquivalent values values := by
  constructor
  · intro name
    cases lookupVariableValue? values name <;>
      simp [inputValue_equivalent_refl_forCoercion]
  · rfl

theorem variableValuesCoercionEquivalent_symm
    {left right : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent left right)
    : variableValuesCoercionEquivalent right left := by
  constructor
  · intro name
    have hlookup := hequivalent.1 name
    cases hleft : lookupVariableValue? left name <;>
      cases hright : lookupVariableValue? right name <;>
      simp [hleft, hright] at hlookup ⊢
    exact inputValue_equivalent_symm_forCoercion hlookup
  · exact hequivalent.2.symm

theorem variableValuesCoercionEquivalent_trans
    {left middle right : VariableValues}
    (hleft : variableValuesCoercionEquivalent left middle)
    (hright : variableValuesCoercionEquivalent middle right)
    : variableValuesCoercionEquivalent left right := by
  constructor
  · intro name
    have hleftLookup := hleft.1 name
    have hrightLookup := hright.1 name
    cases leftLookup : lookupVariableValue? left name <;>
      cases middleLookup : lookupVariableValue? middle name <;>
      cases rightLookup : lookupVariableValue? right name <;>
      simp [leftLookup, middleLookup, rightLookup] at hleftLookup hrightLookup ⊢
    exact inputValue_equivalent_trans_forCoercion hleftLookup hrightLookup
  · exact hleft.2.trans hright.2

private theorem coerceInputValueBounded_canonical_map_eq_of_lookup
    (schema : Schema) {left right : VariableValues}
    (hlookup
      : ∀ name,
          (lookupVariableValue? left name).map InputValue.canonical
          = (lookupVariableValue? right name).map InputValue.canonical)
    : ∀ fuel inputType leftValue rightValue,
        leftValue.canonical = rightValue.canonical
        -> (coerceInputValueBounded schema left fuel inputType leftValue).map
              InputValue.canonical
            = (coerceInputValueBounded schema right fuel inputType rightValue).map
                InputValue.canonical := by
  intro fuel
  induction fuel with
  | zero =>
      intro inputType leftValue rightValue hcanonical
      simp [coerceInputValueBounded]
  | succ fuel ih =>
      have hlist : ∀ inputType leftValues rightValues,
          InputValue.canonicalValues leftValues =
              InputValue.canonicalValues rightValues ->
          InputValue.canonicalValues
              (coerceInputValueList schema left fuel inputType leftValues) =
            InputValue.canonicalValues
              (coerceInputValueList schema right fuel inputType rightValues) := by
        intro inputType leftValues
        induction leftValues with
        | nil =>
            intro rightValues hcanonical
            cases rightValues with
            | nil => simp [coerceInputValueList, InputValue.canonicalValues]
            | cons rightValue rightRest =>
                simp [InputValue.canonicalValues] at hcanonical
        | cons leftValue leftRest ihValues =>
            intro rightValues hcanonical
            cases rightValues with
            | nil => simp [InputValue.canonicalValues] at hcanonical
            | cons rightValue rightRest =>
                simp only [InputValue.canonicalValues] at hcanonical
                have hhead : leftValue.canonical = rightValue.canonical := by
                  exact List.cons.inj hcanonical |>.1
                have hrest : InputValue.canonicalValues leftRest =
                    InputValue.canonicalValues rightRest := by
                  exact List.cons.inj hcanonical |>.2
                simp only [coerceInputValueList, InputValue.canonicalValues]
                congr 1
                · exact optionGetD_canonical_eq
                    (ih inputType leftValue rightValue hhead)
                · exact ihValues rightRest hrest
      have hobject : ∀ definitions leftFields rightFields,
          (∀ name,
            (lookupInputObjectFieldValue? leftFields name).map
                InputValue.canonical =
              (lookupInputObjectFieldValue? rightFields name).map
                InputValue.canonical) ->
          InputValue.canonicalObjectFields
              (coerceInputObjectFields schema left fuel definitions leftFields) =
            InputValue.canonicalObjectFields
              (coerceInputObjectFields schema right fuel definitions rightFields) := by
        intro definitions
        induction definitions with
        | nil =>
            intro leftFields rightFields hfields
            simp [coerceInputObjectFields, InputValue.canonicalObjectFields]
        | cons definition rest ihDefinitions =>
            intro leftFields rightFields hfields
            have heffective := coercedInputObjectFieldValue?_canonical_map_eq
              schema fuel ih definition (hfields definition.name)
            rw [coerceInputObjectFields, coerceInputObjectFields]
            split
            case h_1 hleftEffective =>
              split
              case h_1 hrightEffective =>
                exact ihDefinitions leftFields rightFields hfields
              case h_2 rightValue hrightEffective =>
                have hmapped :=
                  (congrArg (Option.map InputValue.canonical) hleftEffective).symm.trans
                    (heffective.trans
                      (congrArg (Option.map InputValue.canonical) hrightEffective))
                simp at hmapped
            case h_2 leftValue hleftEffective =>
              split
              case h_1 hrightEffective =>
                have hmapped :=
                  (congrArg (Option.map InputValue.canonical) hleftEffective).symm.trans
                    (heffective.trans
                      (congrArg (Option.map InputValue.canonical) hrightEffective))
                simp at hmapped
              case h_2 rightValue hrightEffective =>
                have hmapped :=
                  (congrArg (Option.map InputValue.canonical) hleftEffective).symm.trans
                    (heffective.trans
                      (congrArg (Option.map InputValue.canonical) hrightEffective))
                have hvalue : leftValue.canonical = rightValue.canonical :=
                  Option.some.inj hmapped
                simp [InputValue.canonicalObjectFields, hvalue,
                  ihDefinitions leftFields rightFields hfields]
      intro inputType leftValue rightValue hcanonical
      cases leftValue <;> cases rightValue <;>
        simp [InputValue.canonical] at hcanonical
      case null.null =>
        cases inputType <;> simp [coerceInputValueBounded]
      case int.int leftInt rightInt =>
        subst rightInt
        cases inputType with
        | named typeName => simp [coerceInputValueBounded]
        | list inner => simp [coerceInputValueBounded]
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.int leftInt) (.int leftInt) rfl
      case float.float leftFloat rightFloat =>
        subst rightFloat
        cases inputType with
        | named typeName => simp [coerceInputValueBounded]
        | list inner => simp [coerceInputValueBounded]
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.float leftFloat) (.float leftFloat) rfl
      case string.string leftString rightString =>
        subst rightString
        cases inputType with
        | named typeName => simp [coerceInputValueBounded]
        | list inner => simp [coerceInputValueBounded]
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.string leftString) (.string leftString) rfl
      case boolean.boolean leftBool rightBool =>
        subst rightBool
        cases inputType with
        | named typeName => simp [coerceInputValueBounded]
        | list inner => simp [coerceInputValueBounded]
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.boolean leftBool) (.boolean leftBool) rfl
      case enum.enum leftEnum rightEnum =>
        subst rightEnum
        cases inputType with
        | named typeName => simp [coerceInputValueBounded]
        | list inner => simp [coerceInputValueBounded]
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.enum leftEnum) (.enum leftEnum) rfl
      case list.list leftValues rightValues =>
        cases inputType with
        | named typeName =>
            simpa [coerceInputValueBounded, InputValue.canonical] using hcanonical
        | list inner =>
            simp [coerceInputValueBounded, InputValue.canonical,
              hlist inner leftValues rightValues hcanonical]
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.list leftValues) (.list rightValues) (by
                simpa [InputValue.canonical] using hcanonical)
      case object.object leftFields rightFields =>
        cases inputType with
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName with
            | none => simp [coerceInputValueBounded, hinputObject,
                coerceInputObjectFields, InputValue.canonical]
            | some inputObject =>
                have hfields : ∀ name,
                    (lookupInputObjectFieldValue? leftFields name).map
                        InputValue.canonical =
                      (lookupInputObjectFieldValue? rightFields name).map
                        InputValue.canonical :=
                  lookupInputObjectFieldValue?_canonical_map_eq hcanonical
                have hcoercedFields := hobject inputObject.inputFields leftFields
                  rightFields hfields
                simp [coerceInputValueBounded, hinputObject, InputValue.canonical,
                  hcoercedFields]
        | list inner =>
            simpa [coerceInputValueBounded, InputValue.canonical] using hcanonical
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.object leftFields) (.object rightFields) (by
                simpa [InputValue.canonical] using hcanonical)
      case variable.variable leftName rightName =>
        subst rightName
        have hrelated := hlookup leftName
        cases hleft : lookupVariableValue? left leftName with
        | none =>
            cases hright : lookupVariableValue? right leftName with
            | none => simp [coerceInputValueBounded, hleft, hright]
            | some rightValue => simp [hleft, hright] at hrelated
        | some leftValue =>
            cases hright : lookupVariableValue? right leftName with
            | none => simp [hleft, hright] at hrelated
            | some rightValue =>
                have hvalue : leftValue.canonical = rightValue.canonical := by
                  simpa [hleft, hright] using hrelated
                simpa [coerceInputValueBounded, hleft, hright] using
                  ih inputType leftValue rightValue hvalue

theorem coerceInputValue_rel_of_equivalent
    (schema : Schema) {left right : VariableValues}
    (hvalues : variableValuesCoercionEquivalent left right)
    (inputType : TypeRef) {leftValue rightValue : InputValue}
    (hvalue : leftValue.equivalent rightValue)
    : Option.Rel InputValue.equivalent
        (coerceInputValue schema left inputType leftValue)
        (coerceInputValue schema right inputType rightValue) := by
  unfold coerceInputValue
  rw [hvalues.2, inputValueCoercionFuel_eq_of_equivalent hvalue]
  rw [optionRel_inputValueEquivalent_iff_canonical_map_eq]
  apply coerceInputValueBounded_canonical_map_eq_of_lookup schema
  · intro name
    rw [← optionRel_inputValueEquivalent_iff_canonical_map_eq]
    exact hvalues.1 name
  · exact inputValue_canonical_eq_of_equivalent hvalue

theorem coerceInputValue_rel_of_variableValuesCoercionEquivalent
    (schema : Schema) {left right : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent left right)
    (inputType : TypeRef) (value : InputValue)
    : Option.Rel InputValue.equivalent
        (coerceInputValue schema left inputType value)
        (coerceInputValue schema right inputType value) :=
  coerceInputValue_rel_of_equivalent schema hequivalent inputType
    (inputValue_equivalent_refl_forCoercion value)

private theorem lookupValue_eq_some_of_mem
    {arguments : List Argument} {argument : Argument} {name : Name}
    (hnodup : (arguments.map Argument.name).Nodup)
    (hmem : argument ∈ arguments) (hname : argument.name = name)
    : Argument.lookupValue? arguments name = some argument.value := by
  induction arguments with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hhead, hrest⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [Argument.lookupValue?, hname]
      · have hne : head.name ≠ name := by
          intro heq
          apply hhead
          rw [heq, ← hname]
          exact List.mem_map.mpr ⟨argument, hmem, rfl⟩
        simp [Argument.lookupValue?, hne, ih hrest hmem]

private theorem lookupValue_none_iff {arguments : List Argument} {name : Name}
    : Argument.lookupValue? arguments name = none
      ↔ ∀ argument, argument ∈ arguments -> argument.name ≠ name := by
  induction arguments with
  | nil => simp [Argument.lookupValue?]
  | cons head rest ih =>
      by_cases hname : head.name = name
      · simp [Argument.lookupValue?, hname]
      · simp only [Argument.lookupValue?, hname, if_false, ih]
        constructor
        · intro hnone argument hmem
          rcases List.mem_cons.mp hmem with rfl | hrest
          · exact hname
          · exact hnone argument hrest
        · intro hall argument hmem
          exact hall argument (List.mem_cons_of_mem head hmem)

private theorem lookupValue_eq_some_mem
    {arguments : List Argument} {name : Name} {value : InputValue}
    : Argument.lookupValue? arguments name = some value
      -> ∃ argument,
          argument ∈ arguments ∧ argument.name = name ∧ argument.value = value := by
  induction arguments with
  | nil => simp [Argument.lookupValue?]
  | cons head rest ih =>
      by_cases hname : head.name = name
      · intro hlookup
        simp [Argument.lookupValue?, hname] at hlookup
        exact ⟨head, by simp, hname, hlookup⟩
      · intro hlookup
        simp only [Argument.lookupValue?, hname, if_false] at hlookup
        rcases ih hlookup with ⟨argument, hmem, hargumentName, hvalue⟩
        exact ⟨argument, by simp [hmem], hargumentName, hvalue⟩

private theorem lookupValue_equivalent
    {left right : List Argument}
    (_hleft : (left.map Argument.name).Nodup)
    (hright : (right.map Argument.name).Nodup)
    (hequivalent : Argument.argumentsEquivalent left right)
    (name : Name)
    : Option.Rel InputValue.equivalent
        (Argument.lookupValue? left name) (Argument.lookupValue? right name) := by
  cases hleftLookup : Argument.lookupValue? left name with
  | none =>
      have hrightLookup : Argument.lookupValue? right name = none := by
        apply lookupValue_none_iff.mpr
        intro argument hargument hname
        rcases hequivalent.2 argument hargument with
          ⟨leftArgument, hleftArgument, hequivalentArgument⟩
        have hleftName :=
          (lookupValue_none_iff.mp hleftLookup) leftArgument hleftArgument
        exact hleftName (hequivalentArgument.1.trans hname)
      simp [hrightLookup]
  | some leftValue =>
      rcases lookupValue_eq_some_mem hleftLookup with
        ⟨leftArgument, hleftMem, hleftName, rfl⟩
      rcases hequivalent.1 leftArgument hleftMem with
        ⟨rightArgument, hrightMem, hargumentEquivalent⟩
      have hrightName : rightArgument.name = name :=
        hargumentEquivalent.1.symm.trans hleftName
      have hrightLookup :=
        lookupValue_eq_some_of_mem hright hrightMem hrightName
      simp [hrightLookup, hargumentEquivalent.2]

private theorem argumentsEquivalent_nil_forCoercion
    : Argument.argumentsEquivalent [] [] := by
  simp [Argument.argumentsEquivalent]

private theorem argumentsEquivalent_cons_forCoercion
    {leftArgument rightArgument : Argument} {leftRest rightRest : List Argument}
    (hargument : leftArgument.equivalent rightArgument)
    (hrest : Argument.argumentsEquivalent leftRest rightRest)
    : Argument.argumentsEquivalent (leftArgument :: leftRest)
        (rightArgument :: rightRest) := by
  constructor
  · intro argument hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨rightArgument, by simp, hargument⟩
    · rcases hrest.1 argument hmem with ⟨other, hother, hequivalent⟩
      exact ⟨other, by simp [hother], hequivalent⟩
  · intro argument hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨leftArgument, by simp, hargument⟩
    · rcases hrest.2 argument hmem with ⟨other, hother, hequivalent⟩
      exact ⟨other, by simp [hother], hequivalent⟩

theorem argumentsEquivalent_trans_forCoercion
    {left middle right : List Argument}
    (hleft : Argument.argumentsEquivalent left middle)
    (hright : Argument.argumentsEquivalent middle right)
    : Argument.argumentsEquivalent left right := by
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

private def coercedArgumentValue? (schema : Schema)
    (variableValues : VariableValues) (definition : InputValueDefinition)
    (arguments : List Argument)
    : Option InputValue :=
  match (Argument.lookupValue? arguments definition.name).bind
          (coerceInputValue schema variableValues definition.inputType) with
  | some value => some value
  | none =>
      definition.defaultValue.bind
        (fun value =>
          coerceInputValue schema variableValues definition.inputType value.toInputValue)

private theorem coercedArgumentValue?_rel_of_lookup
    (schema : Schema) {leftValues rightValues : VariableValues}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (definition : InputValueDefinition) {leftArguments rightArguments : List Argument}
    (hlookup
      : Option.Rel InputValue.equivalent
          (Argument.lookupValue? leftArguments definition.name)
          (Argument.lookupValue? rightArguments definition.name))
    : Option.Rel InputValue.equivalent
        (coercedArgumentValue? schema leftValues definition leftArguments)
        (coercedArgumentValue? schema rightValues definition rightArguments) := by
  have hdefault : Option.Rel InputValue.equivalent
      (definition.defaultValue.bind (fun value =>
        coerceInputValue schema leftValues definition.inputType value.toInputValue))
      (definition.defaultValue.bind (fun value =>
        coerceInputValue schema rightValues definition.inputType value.toInputValue)) := by
    cases definition.defaultValue with
    | none => exact .none
    | some defaultValue =>
        exact coerceInputValue_rel_of_equivalent schema hvalues definition.inputType
          (inputValue_equivalent_refl_forCoercion defaultValue.toInputValue)
  cases hleftLookup : Argument.lookupValue? leftArguments definition.name with
  | none =>
      cases hrightLookup : Argument.lookupValue? rightArguments definition.name with
      | none =>
          simpa [coercedArgumentValue?, hleftLookup, hrightLookup] using hdefault
      | some rightValue => simp [hleftLookup, hrightLookup] at hlookup
  | some leftValue =>
      cases hrightLookup : Argument.lookupValue? rightArguments definition.name with
      | none => simp [hleftLookup, hrightLookup] at hlookup
      | some rightValue =>
          have hvalue : leftValue.equivalent rightValue := by
            simpa [hleftLookup, hrightLookup] using hlookup
          have hcoerced := coerceInputValue_rel_of_equivalent schema hvalues
            definition.inputType hvalue
          cases hleftCoerced
                : coerceInputValue schema leftValues definition.inputType leftValue with
          | none =>
              cases hrightCoerced
                    : coerceInputValue schema rightValues definition.inputType
                        rightValue with
              | none =>
                  simpa [coercedArgumentValue?, hleftLookup, hrightLookup,
                    hleftCoerced, hrightCoerced] using hdefault
              | some rightCoerced =>
                  simp [hleftCoerced, hrightCoerced] at hcoerced
          | some leftCoerced =>
              cases hrightCoerced
                    : coerceInputValue schema rightValues definition.inputType
                        rightValue with
              | none => simp [hleftCoerced, hrightCoerced] at hcoerced
              | some rightCoerced =>
                  simpa [coercedArgumentValue?, hleftLookup, hrightLookup,
                    hleftCoerced, hrightCoerced] using hcoerced

private theorem coerceArgumentValues_equivalent_of_lookups (schema : Schema)
    {leftValues rightValues : VariableValues}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (definitions : List InputValueDefinition)
    (leftArguments rightArguments : List Argument)
    (hlookup
      : ∀ name,
          Option.Rel InputValue.equivalent
            (Argument.lookupValue? leftArguments name)
            (Argument.lookupValue? rightArguments name))
    : Argument.argumentsEquivalent
        (coerceArgumentValues schema leftValues definitions leftArguments)
        (coerceArgumentValues schema rightValues definitions rightArguments) := by
  induction definitions with
  | nil => exact argumentsEquivalent_nil_forCoercion
  | cons definition rest ih =>
      change Argument.argumentsEquivalent
        (match coercedArgumentValue? schema leftValues definition leftArguments with
        | none => coerceArgumentValues schema leftValues rest leftArguments
        | some value => { name := definition.name, value := value } ::
            coerceArgumentValues schema leftValues rest leftArguments)
        (match coercedArgumentValue? schema rightValues definition rightArguments with
        | none => coerceArgumentValues schema rightValues rest rightArguments
        | some value => { name := definition.name, value := value } ::
            coerceArgumentValues schema rightValues rest rightArguments)
      have heffective := coercedArgumentValue?_rel_of_lookup schema hvalues definition
        (hlookup definition.name)
      cases hleftEffective
            : coercedArgumentValue? schema leftValues definition leftArguments with
      | none =>
          cases hrightEffective
                : coercedArgumentValue? schema rightValues definition rightArguments with
          | none => simpa [hleftEffective, hrightEffective] using ih
          | some rightValue => simp [hleftEffective, hrightEffective] at heffective
      | some leftValue =>
          cases hrightEffective
                : coercedArgumentValue? schema rightValues definition rightArguments with
          | none => simp [hleftEffective, hrightEffective] at heffective
          | some rightValue =>
              have hvalue : leftValue.equivalent rightValue := by
                simpa [hleftEffective, hrightEffective] using heffective
              simpa [hleftEffective, hrightEffective] using
                argumentsEquivalent_cons_forCoercion
                  (leftArgument := { name := definition.name, value := leftValue })
                  (rightArgument := { name := definition.name, value := rightValue })
                  ⟨rfl, hvalue⟩ ih

theorem coerceArgumentValues_equivalent_of_equivalent
    (schema : Schema) (variableValues : VariableValues)
    (definitions : List InputValueDefinition) {left right : List Argument}
    (hleft : (left.map Argument.name).Nodup)
    (hright : (right.map Argument.name).Nodup)
    (hequivalent : Argument.argumentsEquivalent left right)
    : Argument.argumentsEquivalent
        (coerceArgumentValues schema variableValues definitions left)
        (coerceArgumentValues schema variableValues definitions right) := by
  apply coerceArgumentValues_equivalent_of_lookups schema
    (variableValuesCoercionEquivalent_refl variableValues)
  exact lookupValue_equivalent hleft hright hequivalent

theorem coerceArgumentValues_equivalent_of_variableValuesCoercionEquivalent
    (schema : Schema) {left right : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent left right)
    (definitions : List InputValueDefinition) (arguments : List Argument)
    : Argument.argumentsEquivalent
        (coerceArgumentValues schema left definitions arguments)
        (coerceArgumentValues schema right definitions arguments) := by
  apply coerceArgumentValues_equivalent_of_lookups schema hequivalent
  intro name
  cases Argument.lookupValue? arguments name with
  | none => exact .none
  | some value => exact .some (inputValue_equivalent_refl_forCoercion value)

private theorem variableValuesCoercionEquivalent_cons
    {left right : VariableValues} {leftValue rightValue : InputValue}
    (hequivalent : variableValuesCoercionEquivalent left right)
    (name : Name) (hvalue : leftValue.equivalent rightValue)
    : variableValuesCoercionEquivalent ((name, leftValue) :: left)
        ((name, rightValue) :: right) := by
  constructor
  · intro candidate
    by_cases hname : name = candidate
    · simpa [lookupVariableValue?, hname] using hvalue
    · simpa [lookupVariableValue?, hname] using hequivalent.1 candidate
  · simp [variableValuesCoercionFuel, hequivalent.2,
      inputValueCoercionFuel_eq_of_equivalent hvalue]

private theorem variableDefinitionsEquivalent_foldl_defaults_coercionEquivalent
    : ∀ {left right : List VariableDefinition} {leftValues rightValues : VariableValues},
        variableValuesCoercionEquivalent leftValues rightValues
        -> variableDefinitionsEquivalent left right
        -> variableValuesCoercionEquivalent
            (left.foldl
              (fun coercedValues variableDefinition =>
                match lookupVariableValue? coercedValues variableDefinition.name with
                | some _value => coercedValues
                | none =>
                    match variableDefinition.defaultValue with
                    | some defaultValue =>
                        (variableDefinition.name, defaultValue.toInputValue)
                        :: coercedValues
                    | none => coercedValues)
              leftValues)
            (right.foldl
              (fun coercedValues variableDefinition =>
                match lookupVariableValue? coercedValues variableDefinition.name with
                | some _value => coercedValues
                | none =>
                    match variableDefinition.defaultValue with
                    | some defaultValue =>
                        (variableDefinition.name, defaultValue.toInputValue)
                        :: coercedValues
                    | none => coercedValues)
              rightValues)
  | [], [], _leftValues, _rightValues, hvalues, _hdefinitions => hvalues
  | left :: leftRest, right :: rightRest, leftValues, rightValues,
      hvalues, hdefinitions => by
      rcases left with ⟨leftName, leftType, leftDefault⟩
      rcases right with ⟨rightName, rightType, rightDefault⟩
      simp only [variableDefinitionsEquivalent] at hdefinitions
      rcases hdefinitions with ⟨hname, hdefaults⟩
      subst rightName
      have hlookup := hvalues.1 leftName
      cases hleftLookup : lookupVariableValue? leftValues leftName with
      | none =>
          cases hrightLookup : lookupVariableValue? rightValues leftName with
          | none =>
              cases leftDefault with
              | none =>
                  cases rightDefault with
                  | none =>
                      simpa [hleftLookup, hrightLookup] using
                        variableDefinitionsEquivalent_foldl_defaults_coercionEquivalent
                          hvalues hdefaults
                  | some rightDefault => simp at hdefaults
              | some leftDefault =>
                  cases rightDefault with
                  | none => simp at hdefaults
                  | some rightDefault =>
                      simp only at hdefaults
                      simpa [hleftLookup, hrightLookup] using
                        variableDefinitionsEquivalent_foldl_defaults_coercionEquivalent
                          (variableValuesCoercionEquivalent_cons hvalues leftName
                            hdefaults.1)
                          hdefaults.2
          | some rightValue => simp [hleftLookup, hrightLookup] at hlookup
      | some leftValue =>
          cases hrightLookup : lookupVariableValue? rightValues leftName with
          | none => simp [hleftLookup, hrightLookup] at hlookup
          | some rightValue =>
              cases leftDefault <;> cases rightDefault <;>
                simp only at hdefaults
              all_goals
                simpa [hleftLookup, hrightLookup] using
                  variableDefinitionsEquivalent_foldl_defaults_coercionEquivalent
                    hvalues (by first | exact hdefaults | exact hdefaults.2)

theorem coerceVariableValues_coercionEquivalent_of_variableDefinitionsEquivalent
    {left right : Operation} {leftValues rightValues : VariableValues}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (hdefinitions
      : variableDefinitionsEquivalent left.variableDefinitions right.variableDefinitions)
    : variableValuesCoercionEquivalent
        (coerceVariableValues left leftValues)
        (coerceVariableValues right rightValues) := by
  exact variableDefinitionsEquivalent_foldl_defaults_coercionEquivalent
    hvalues hdefinitions

-- Proof-facing name-based resolution for statements that intentionally quantify over
-- arbitrary field names without carrying a successful schema lookup witness. Runtime
-- executors pass their already-looked-up field definition to `resolveFieldValue`.
def resolveFieldValueByName (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (parentType fieldName : Name)
    (arguments : List Argument) (source : ResolverValue ObjectRef)
    : Option (ResolverValue ObjectRef) :=
  match schema.lookupField parentType fieldName with
  | none => none
  | some fieldDefinition =>
      resolveFieldValue schema resolvers variableValues fieldDefinition parentType
        fieldName arguments source

-- Proof-facing field lookup wrapper used by resolver probes. Runtime execution calls
-- `coerceArgumentValues` directly after the same lookup.
def coercedArgumentsForField (schema : Schema) (variableValues : VariableValues)
    (parentType fieldName : Name) (arguments : List Argument)
    : CoercedArguments :=
  match schema.lookupField parentType fieldName with
  | none => []
  | some fieldDefinition =>
      coerceArgumentValues schema variableValues fieldDefinition.arguments arguments

-- Two variable environments are indistinguishable at the resolver boundary when
-- every field-argument definition and syntax pair produces equivalent semantic maps.
def argumentCoercionEquivalent (schema : Schema) (leftValues rightValues : VariableValues)
    : Prop :=
  ∀ definitions arguments,
    Argument.argumentsEquivalent
      (coerceArgumentValues schema leftValues definitions arguments)
      (coerceArgumentValues schema rightValues definitions arguments)

theorem argumentCoercionEquivalent_of_variableValuesCoercionEquivalent
    (schema : Schema) {leftValues rightValues : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent leftValues rightValues)
    : argumentCoercionEquivalent schema leftValues rightValues := by
  intro definitions arguments
  exact coerceArgumentValues_equivalent_of_variableValuesCoercionEquivalent
    schema hequivalent definitions arguments

-- Operation-variable default materialization is observationally inert for resolver
-- arguments under this proof-side scope condition.
def operationArgumentCoercionInvariant (schema : Schema) (operation : Operation) : Prop :=
  ∀ variableValues,
    argumentCoercionEquivalent schema variableValues
      (coerceVariableValues operation variableValues)

-- Ground normal-form uniqueness can recover raw argument syntax only when the
-- resolver boundary does not identify distinct argument lists at the empty variable
-- environment used by the separating probes.
def argumentCoercionReflectsSyntaxAtEmpty (schema : Schema) : Prop :=
  ∀ definitions leftArguments rightArguments,
    Argument.argumentsEquivalent
      (coerceArgumentValues schema [] definitions leftArguments)
      (coerceArgumentValues schema [] definitions rightArguments)
    -> Argument.argumentsEquivalent leftArguments rightArguments

end Execution

end GraphQL
