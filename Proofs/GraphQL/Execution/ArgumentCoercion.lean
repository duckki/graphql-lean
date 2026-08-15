import GraphQL.Execution
import Proofs.GraphQL.Validation.SelectionValidity
import Proofs.GraphQL.Validation.Variables

/-!
Proof-facing relations and scope predicates for coerced resolver arguments.

`InputValue.canonical` is used here only to reason about the semantic relation
`InputValue.equivalent`. The spec-facing coercer in `GraphQL.Execution` operates on
the supplied values directly and never canonicalizes them.
-/

namespace GraphQL

namespace Execution

theorem ArgumentCoercionResult.exists_success_of_isSuccess
    {result : ArgumentCoercionResult} (hresult : result.isSuccess = true)
    : ∃ arguments, result = .success arguments := by
  cases result with
  | success arguments => exact ⟨arguments, rfl⟩
  | error => simp at hresult

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

private theorem inputObjectFieldsKnownBool_insertObjectFieldSorted
    (definitions : List InputValueDefinition) (field : Name × InputValue)
    : ∀ fields,
        inputObjectFieldsKnownBool definitions
          (InputValue.insertObjectFieldSorted field fields)
        = ((Schema.lookupArgumentDefinition definitions field.1).isSome
            && inputObjectFieldsKnownBool definitions fields)
  | [] => by
      simp [InputValue.insertObjectFieldSorted, inputObjectFieldsKnownBool]
  | candidate :: rest => by
      by_cases hle : field.1 <= candidate.1
      · simp [InputValue.insertObjectFieldSorted, hle, inputObjectFieldsKnownBool]
      · simp [InputValue.insertObjectFieldSorted, hle, inputObjectFieldsKnownBool,
          inputObjectFieldsKnownBool_insertObjectFieldSorted definitions field rest,
          Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

private theorem inputObjectFieldsKnownBool_sortObjectFieldsByName
    (definitions : List InputValueDefinition)
    : ∀ fields,
        inputObjectFieldsKnownBool definitions (InputValue.sortObjectFieldsByName fields)
        = inputObjectFieldsKnownBool definitions fields
  | [] => rfl
  | field :: rest => by
      simp [InputValue.sortObjectFieldsByName, inputObjectFieldsKnownBool,
        inputObjectFieldsKnownBool_insertObjectFieldSorted,
        inputObjectFieldsKnownBool_sortObjectFieldsByName definitions rest]

private theorem inputObjectFieldsKnownBool_canonicalObjectFields
    (definitions : List InputValueDefinition)
    : ∀ fields,
        inputObjectFieldsKnownBool definitions (InputValue.canonicalObjectFields fields)
        = inputObjectFieldsKnownBool definitions fields
  | [] => rfl
  | (_name, _value) :: rest => by
      simp [InputValue.canonicalObjectFields, inputObjectFieldsKnownBool,
        inputObjectFieldsKnownBool_canonicalObjectFields definitions rest]

private theorem inputObjectFieldsKnownBool_canonical
    (definitions : List InputValueDefinition) (fields : List (Name × InputValue))
    : inputObjectFieldsKnownBool definitions
        (InputValue.sortObjectFieldsByName (InputValue.canonicalObjectFields fields))
      = inputObjectFieldsKnownBool definitions fields := by
  rw [inputObjectFieldsKnownBool_sortObjectFieldsByName,
    inputObjectFieldsKnownBool_canonicalObjectFields]

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
-- extensionally equivalent and the legacy whole-environment fuel measure agrees.
-- Local input coercion uses only the first component; the stronger relation remains
-- useful to existing whole-execution equivalence theorems.
def variableValueLookupsEquivalent (left right : VariableValues) : Prop :=
  ∀ name,
    Option.Rel
      (fun leftValue rightValue =>
        InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
      (lookupVariableValue? left name) (lookupVariableValue? right name)

def variableValuesCoercionEquivalent (left right : VariableValues) : Prop :=
  variableValueLookupsEquivalent left right
  ∧ variableValuesCoercionFuel left = variableValuesCoercionFuel right

private theorem referencedVariableObjectFieldsCoercionFuel_insertObjectFieldSorted
    (variableValues : VariableValues) (field : Name × InputValue)
    : ∀ fields,
        referencedVariableObjectFieldsCoercionFuel variableValues
          (InputValue.insertObjectFieldSorted field fields)
        = referencedVariableValuesCoercionFuel variableValues field.2
          + referencedVariableObjectFieldsCoercionFuel variableValues fields
  | [] => by
      simp [InputValue.insertObjectFieldSorted,
        referencedVariableObjectFieldsCoercionFuel]
  | candidate :: rest => by
      by_cases hname : field.1 <= candidate.1
      · simp [InputValue.insertObjectFieldSorted, hname,
          referencedVariableObjectFieldsCoercionFuel]
      · simp [InputValue.insertObjectFieldSorted, hname,
          referencedVariableObjectFieldsCoercionFuel,
          referencedVariableObjectFieldsCoercionFuel_insertObjectFieldSorted
            variableValues field rest,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem referencedVariableObjectFieldsCoercionFuel_sortObjectFieldsByName
    (variableValues : VariableValues)
    : ∀ fields,
        referencedVariableObjectFieldsCoercionFuel variableValues
          (InputValue.sortObjectFieldsByName fields)
        = referencedVariableObjectFieldsCoercionFuel variableValues fields
  | [] => by
      simp [InputValue.sortObjectFieldsByName,
        referencedVariableObjectFieldsCoercionFuel]
  | field :: rest => by
      simp [InputValue.sortObjectFieldsByName,
        referencedVariableObjectFieldsCoercionFuel,
        referencedVariableObjectFieldsCoercionFuel_insertObjectFieldSorted,
        referencedVariableObjectFieldsCoercionFuel_sortObjectFieldsByName
          variableValues rest]

mutual
  private theorem referencedVariableValuesCoercionFuel_canonical
      (variableValues : VariableValues)
      : ∀ value,
          referencedVariableValuesCoercionFuel variableValues value.canonical
          = referencedVariableValuesCoercionFuel variableValues value
    | .null | .int _ | .float _ | .string _ | .boolean _ | .enum _ | .variable _ => rfl
    | .list values => by
        simp [InputValue.canonical, referencedVariableValuesCoercionFuel,
          referencedVariableValueListCoercionFuel_canonical variableValues values]
    | .object fields => by
        simp [InputValue.canonical, referencedVariableValuesCoercionFuel,
          referencedVariableObjectFieldsCoercionFuel_sortObjectFieldsByName,
          referencedVariableObjectFieldsCoercionFuel_canonical variableValues fields]

  private theorem referencedVariableValueListCoercionFuel_canonical
      (variableValues : VariableValues)
      : ∀ values,
          referencedVariableValueListCoercionFuel variableValues
            (InputValue.canonicalValues values)
          = referencedVariableValueListCoercionFuel variableValues values
    | [] => rfl
    | value :: rest => by
        simp [InputValue.canonicalValues, referencedVariableValueListCoercionFuel,
          referencedVariableValuesCoercionFuel_canonical variableValues value,
          referencedVariableValueListCoercionFuel_canonical variableValues rest]

  private theorem referencedVariableObjectFieldsCoercionFuel_canonical
      (variableValues : VariableValues)
      : ∀ fields,
          referencedVariableObjectFieldsCoercionFuel variableValues
            (InputValue.canonicalObjectFields fields)
          = referencedVariableObjectFieldsCoercionFuel variableValues fields
    | [] => rfl
    | (_, value) :: rest => by
        simp [InputValue.canonicalObjectFields,
          referencedVariableObjectFieldsCoercionFuel,
          referencedVariableValuesCoercionFuel_canonical variableValues value,
          referencedVariableObjectFieldsCoercionFuel_canonical variableValues rest]
end

mutual
  private theorem referencedVariableValuesCoercionFuel_eq_of_lookupsEquivalent
      {left right : VariableValues}
      (hequivalent : variableValueLookupsEquivalent left right)
      : ∀ value,
          referencedVariableValuesCoercionFuel left value
          = referencedVariableValuesCoercionFuel right value
    | .null | .int _ | .float _ | .string _ | .boolean _ | .enum _ => rfl
    | .variable name => by
        have hlookup := hequivalent name
        cases hleft : lookupVariableValue? left name with
        | none =>
            cases hright : lookupVariableValue? right name with
            | none => simp [referencedVariableValuesCoercionFuel, hleft, hright]
            | some rightValue => simp [hleft, hright] at hlookup
        | some leftValue =>
            cases hright : lookupVariableValue? right name with
            | none => simp [hleft, hright] at hlookup
            | some rightValue =>
                have hvalue : leftValue.toInputValue.equivalent rightValue.toInputValue := by
                  simpa [hleft, hright] using hlookup
                simpa [referencedVariableValuesCoercionFuel, hleft, hright]
                  using inputValueCoercionFuel_eq_of_equivalent hvalue
    | .list values =>
        referencedVariableValueListCoercionFuel_eq_of_lookupsEquivalent hequivalent values
    | .object fields =>
        referencedVariableObjectFieldsCoercionFuel_eq_of_lookupsEquivalent
          hequivalent fields

  private theorem referencedVariableValueListCoercionFuel_eq_of_lookupsEquivalent
      {left right : VariableValues}
      (hequivalent : variableValueLookupsEquivalent left right)
      : ∀ values,
          referencedVariableValueListCoercionFuel left values
          = referencedVariableValueListCoercionFuel right values
    | [] => rfl
    | value :: rest => by
        simp only [referencedVariableValueListCoercionFuel]
        rw [referencedVariableValuesCoercionFuel_eq_of_lookupsEquivalent
            hequivalent value,
          referencedVariableValueListCoercionFuel_eq_of_lookupsEquivalent
            hequivalent rest]

  private theorem referencedVariableObjectFieldsCoercionFuel_eq_of_lookupsEquivalent
      {left right : VariableValues}
      (hequivalent : variableValueLookupsEquivalent left right)
      : ∀ fields,
          referencedVariableObjectFieldsCoercionFuel left fields
          = referencedVariableObjectFieldsCoercionFuel right fields
    | [] => rfl
    | (_, value) :: rest => by
        simp only [referencedVariableObjectFieldsCoercionFuel]
        rw [referencedVariableValuesCoercionFuel_eq_of_lookupsEquivalent
            hequivalent value,
          referencedVariableObjectFieldsCoercionFuel_eq_of_lookupsEquivalent
            hequivalent rest]
end

private theorem referencedVariableValuesCoercionFuel_eq_of_equivalent
    {left right : VariableValues} {leftValue rightValue : InputValue}
    (hvalues : variableValueLookupsEquivalent left right)
    (hvalue : leftValue.equivalent rightValue)
    : referencedVariableValuesCoercionFuel left leftValue
      = referencedVariableValuesCoercionFuel right rightValue := by
  calc
    referencedVariableValuesCoercionFuel left leftValue
        = referencedVariableValuesCoercionFuel left leftValue.canonical :=
      (referencedVariableValuesCoercionFuel_canonical left leftValue).symm
    _ = referencedVariableValuesCoercionFuel right leftValue.canonical :=
      referencedVariableValuesCoercionFuel_eq_of_lookupsEquivalent hvalues _
    _ = referencedVariableValuesCoercionFuel right rightValue.canonical := by
      rw [inputValue_canonical_eq_of_equivalent hvalue]
    _ = referencedVariableValuesCoercionFuel right rightValue :=
      referencedVariableValuesCoercionFuel_canonical right rightValue

mutual
  private theorem referencedVariableValuesCoercionFuel_eq_of_lookup_agreement
      {left right : VariableValues}
      : ∀ value,
          (∀ name,
            name ∈ Validation.inputValueVariables value
            -> Option.Rel
                (fun leftValue rightValue =>
                  InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
                (lookupVariableValue? left name) (lookupVariableValue? right name))
          -> referencedVariableValuesCoercionFuel left value
              = referencedVariableValuesCoercionFuel right value
    | .null, _hlookups
    | .int _, _hlookups
    | .float _, _hlookups
    | .string _, _hlookups
    | .boolean _, _hlookups
    | .enum _, _hlookups => rfl
    | .variable name, hlookups => by
        have hlookup := hlookups name (by
          simp [Validation.inputValueVariables])
        cases hleft : lookupVariableValue? left name with
        | none =>
            cases hright : lookupVariableValue? right name with
            | none => simp [referencedVariableValuesCoercionFuel, hleft, hright]
            | some rightValue => simp [hleft, hright] at hlookup
        | some leftValue =>
            cases hright : lookupVariableValue? right name with
            | none => simp [hleft, hright] at hlookup
            | some rightValue =>
                have hvalue : leftValue.toInputValue.equivalent
                    rightValue.toInputValue := by
                  simpa [hleft, hright] using hlookup
                simpa [referencedVariableValuesCoercionFuel, hleft, hright] using
                  inputValueCoercionFuel_eq_of_equivalent hvalue
    | .list values, hlookups =>
        referencedVariableValueListCoercionFuel_eq_of_lookup_agreement values
          hlookups
    | .object fields, hlookups =>
        referencedVariableObjectFieldsCoercionFuel_eq_of_lookup_agreement fields
          hlookups

  private theorem referencedVariableValueListCoercionFuel_eq_of_lookup_agreement
      {left right : VariableValues}
      : ∀ values,
          (∀ name,
            name ∈ Validation.inputValuesVariables values
            -> Option.Rel
                (fun leftValue rightValue =>
                  InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
                (lookupVariableValue? left name) (lookupVariableValue? right name))
          -> referencedVariableValueListCoercionFuel left values
              = referencedVariableValueListCoercionFuel right values
    | [], _hlookups => rfl
    | value :: rest, hlookups => by
        simp only [referencedVariableValueListCoercionFuel]
        rw [referencedVariableValuesCoercionFuel_eq_of_lookup_agreement value (by
              intro name hname
              exact hlookups name (List.mem_append_left _ hname)),
          referencedVariableValueListCoercionFuel_eq_of_lookup_agreement rest (by
              intro name hname
              exact hlookups name (List.mem_append_right _ hname))]

  private theorem referencedVariableObjectFieldsCoercionFuel_eq_of_lookup_agreement
      {left right : VariableValues}
      : ∀ fields,
          (∀ name,
            name ∈ Validation.inputObjectFieldsVariables fields
            -> Option.Rel
                (fun leftValue rightValue =>
                  InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
                (lookupVariableValue? left name) (lookupVariableValue? right name))
          -> referencedVariableObjectFieldsCoercionFuel left fields
              = referencedVariableObjectFieldsCoercionFuel right fields
    | [], _hlookups => rfl
    | (_, value) :: rest, hlookups => by
        simp only [referencedVariableObjectFieldsCoercionFuel]
        rw [referencedVariableValuesCoercionFuel_eq_of_lookup_agreement value (by
              intro name hname
              exact hlookups name (List.mem_append_left _ hname)),
          referencedVariableObjectFieldsCoercionFuel_eq_of_lookup_agreement rest (by
              intro name hname
              exact hlookups name (List.mem_append_right _ hname))]
end

mutual
  private def inputValueVariableCount : InputValue -> Nat
    | .variable _name => 1
    | .list values => inputValueListVariableCount values
    | .object fields => inputValueObjectFieldsVariableCount fields
    | _ => 0

  private def inputValueListVariableCount : List InputValue -> Nat
    | [] => 0
    | value :: rest =>
        inputValueVariableCount value + inputValueListVariableCount rest

  private def inputValueObjectFieldsVariableCount : List (Name × InputValue) -> Nat
    | [] => 0
    | (_, value) :: rest =>
        inputValueVariableCount value + inputValueObjectFieldsVariableCount rest
end

private theorem inputValueObjectFieldsVariableCount_insertObjectFieldSorted
    (field : Name × InputValue)
    : ∀ fields,
        inputValueObjectFieldsVariableCount
          (InputValue.insertObjectFieldSorted field fields)
        = inputValueVariableCount field.2 + inputValueObjectFieldsVariableCount fields
  | [] => by
      simp [InputValue.insertObjectFieldSorted,
        inputValueObjectFieldsVariableCount]
  | candidate :: rest => by
      by_cases hname : field.1 <= candidate.1
      · simp [InputValue.insertObjectFieldSorted, hname,
          inputValueObjectFieldsVariableCount]
      · simp [InputValue.insertObjectFieldSorted, hname,
          inputValueObjectFieldsVariableCount,
          inputValueObjectFieldsVariableCount_insertObjectFieldSorted field rest,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem inputValueObjectFieldsVariableCount_sortObjectFieldsByName
    : ∀ fields,
        inputValueObjectFieldsVariableCount (InputValue.sortObjectFieldsByName fields)
        = inputValueObjectFieldsVariableCount fields
  | [] => rfl
  | field :: rest => by
      simp [InputValue.sortObjectFieldsByName,
        inputValueObjectFieldsVariableCount,
        inputValueObjectFieldsVariableCount_insertObjectFieldSorted,
        inputValueObjectFieldsVariableCount_sortObjectFieldsByName rest]

mutual
  private theorem inputValueVariableCount_canonical
      : ∀ value, inputValueVariableCount value.canonical = inputValueVariableCount value
    | .null | .int _ | .float _ | .string _ | .boolean _ | .enum _ | .variable _ => rfl
    | .list values => by
        simp [InputValue.canonical, inputValueVariableCount,
          inputValueListVariableCount_canonical values]
    | .object fields => by
        simp [InputValue.canonical, inputValueVariableCount,
          inputValueObjectFieldsVariableCount_sortObjectFieldsByName,
          inputValueObjectFieldsVariableCount_canonical fields]

  private theorem inputValueListVariableCount_canonical
      : ∀ values,
          inputValueListVariableCount (InputValue.canonicalValues values)
          = inputValueListVariableCount values
    | [] => rfl
    | value :: rest => by
        simp [InputValue.canonicalValues, inputValueListVariableCount,
          inputValueVariableCount_canonical value,
          inputValueListVariableCount_canonical rest]

  private theorem inputValueObjectFieldsVariableCount_canonical
      : ∀ fields,
          inputValueObjectFieldsVariableCount (InputValue.canonicalObjectFields fields)
          = inputValueObjectFieldsVariableCount fields
    | [] => rfl
    | (_, value) :: rest => by
        simp [InputValue.canonicalObjectFields, inputValueObjectFieldsVariableCount,
          inputValueVariableCount_canonical value,
          inputValueObjectFieldsVariableCount_canonical rest]
end

private theorem inputValueVariableCount_eq_of_equivalent
    {left right : InputValue} (hequivalent : left.equivalent right)
    : inputValueVariableCount left = inputValueVariableCount right := by
  calc
    inputValueVariableCount left = inputValueVariableCount left.canonical :=
      (inputValueVariableCount_canonical left).symm
    _ = inputValueVariableCount right.canonical := by
      rw [inputValue_canonical_eq_of_equivalent hequivalent]
    _ = inputValueVariableCount right := inputValueVariableCount_canonical right

mutual
  private theorem constInputValue_variableCount_toInputValue
      : ∀ value : ConstInputValue, inputValueVariableCount value.toInputValue = 0
    | .null | .int _ | .float _ | .string _ | .boolean _ | .enum _ => rfl
    | .list values => by
        simp [ConstInputValue.toInputValue, inputValueVariableCount,
          constInputValues_variableCount_toInputValues values]
    | .object fields => by
        simp [ConstInputValue.toInputValue, inputValueVariableCount,
          constInputObjectFields_variableCount_toInputFields fields]

  private theorem constInputValues_variableCount_toInputValues
      : ∀ values : List ConstInputValue,
          inputValueListVariableCount (ConstInputValue.valuesToInputValues values) = 0
    | [] => rfl
    | value :: rest => by
        simp [ConstInputValue.valuesToInputValues, inputValueListVariableCount,
          constInputValue_variableCount_toInputValue value,
          constInputValues_variableCount_toInputValues rest]

  private theorem constInputObjectFields_variableCount_toInputFields
      : ∀ fields : List (Name × ConstInputValue),
          inputValueObjectFieldsVariableCount
            (ConstInputValue.objectFieldsToInputFields fields)
          = 0
    | [] => rfl
    | (_, value) :: rest => by
        simp [ConstInputValue.objectFieldsToInputFields,
          inputValueObjectFieldsVariableCount,
          constInputValue_variableCount_toInputValue value,
          constInputObjectFields_variableCount_toInputFields rest]
end

mutual
  private theorem constInputValue_toInputValue_ofInputValue?_eq_some
      : ∀ {inputValue : InputValue} {constValue : ConstInputValue},
          ConstInputValue.ofInputValue? inputValue = some constValue
          -> constValue.toInputValue = inputValue
    | .null, constValue, h => by
        simp [ConstInputValue.ofInputValue?] at h
        subst constValue
        rfl
    | .int value, constValue, h => by
        simp [ConstInputValue.ofInputValue?] at h
        subst constValue
        rfl
    | .float value, constValue, h => by
        simp [ConstInputValue.ofInputValue?] at h
        subst constValue
        rfl
    | .string value, constValue, h => by
        simp [ConstInputValue.ofInputValue?] at h
        subst constValue
        rfl
    | .boolean value, constValue, h => by
        simp [ConstInputValue.ofInputValue?] at h
        subst constValue
        rfl
    | .enum value, constValue, h => by
        simp [ConstInputValue.ofInputValue?] at h
        subst constValue
        rfl
    | .variable _, constValue, h => by simp [ConstInputValue.ofInputValue?] at h
    | .list values, constValue, h => by
        simp only [ConstInputValue.ofInputValue?] at h
        cases hvalues : ConstInputValue.inputValuesToConstInputValues? values with
        | none => simp [hvalues] at h
        | some constValues =>
            simp [hvalues] at h
            subst constValue
            simp [ConstInputValue.toInputValue]
            exact constInputValues_toInputValues_ofInputValues?_eq_some hvalues
    | .object fields, constValue, h => by
        simp only [ConstInputValue.ofInputValue?] at h
        cases hfields : ConstInputValue.inputFieldsToConstInputFields? fields with
        | none => simp [hfields] at h
        | some constFields =>
            simp [hfields] at h
            subst constValue
            simp [ConstInputValue.toInputValue]
            exact constInputFields_toInputFields_ofInputFields?_eq_some hfields

  private theorem constInputValues_toInputValues_ofInputValues?_eq_some
      : ∀ {inputValues : List InputValue} {constValues : List ConstInputValue},
          ConstInputValue.inputValuesToConstInputValues? inputValues = some constValues
          -> ConstInputValue.valuesToInputValues constValues = inputValues
    | [], constValues, h => by
        simp [ConstInputValue.inputValuesToConstInputValues?] at h
        subst constValues
        rfl
    | value :: rest, constValues, h => by
        simp only [ConstInputValue.inputValuesToConstInputValues?] at h
        cases hvalue : ConstInputValue.ofInputValue? value with
        | none => simp [hvalue] at h
        | some constValue =>
            cases hrest : ConstInputValue.inputValuesToConstInputValues? rest with
            | none => simp [hvalue, hrest] at h
            | some constRest =>
                simp [hvalue, hrest] at h
                subst constValues
                simp [ConstInputValue.valuesToInputValues,
                  constInputValue_toInputValue_ofInputValue?_eq_some hvalue,
                  constInputValues_toInputValues_ofInputValues?_eq_some hrest]

  private theorem constInputFields_toInputFields_ofInputFields?_eq_some
      : ∀ {inputFields : List (Name × InputValue)}
          {constFields : List (Name × ConstInputValue)},
          ConstInputValue.inputFieldsToConstInputFields? inputFields = some constFields
          -> ConstInputValue.objectFieldsToInputFields constFields = inputFields
    | [], constFields, h => by
        simp [ConstInputValue.inputFieldsToConstInputFields?] at h
        subst constFields
        rfl
    | (name, value) :: rest, constFields, h => by
        simp only [ConstInputValue.inputFieldsToConstInputFields?] at h
        cases hvalue : ConstInputValue.ofInputValue? value with
        | none => simp [hvalue] at h
        | some constValue =>
            cases hrest : ConstInputValue.inputFieldsToConstInputFields? rest with
            | none => simp [hvalue, hrest] at h
            | some constRest =>
                simp [hvalue, hrest] at h
                subst constFields
                simp [ConstInputValue.objectFieldsToInputFields,
                  constInputValue_toInputValue_ofInputValue?_eq_some hvalue,
                  constInputFields_toInputFields_ofInputFields?_eq_some hrest]
end

mutual
  private theorem constInputValue_ofInputValue?_exists_of_variableCount_eq_zero
      : ∀ value,
          inputValueVariableCount value = 0
          -> ∃ constValue, ConstInputValue.ofInputValue? value = some constValue
    | .null => fun _ => ⟨.null, rfl⟩
    | .int value => fun _ => ⟨.int value, rfl⟩
    | .float value => fun _ => ⟨.float value, rfl⟩
    | .string value => fun _ => ⟨.string value, rfl⟩
    | .boolean value => fun _ => ⟨.boolean value, rfl⟩
    | .enum value => fun _ => ⟨.enum value, rfl⟩
    | .variable name => by simp [inputValueVariableCount]
    | .list values => by
        intro hcount
        rcases constInputValues_ofInputValues?_exists_of_variableCount_eq_zero
            values hcount with ⟨constValues, hvalues⟩
        exact ⟨.list constValues, by simp [ConstInputValue.ofInputValue?, hvalues]⟩
    | .object fields => by
        intro hcount
        rcases constInputFields_ofInputFields?_exists_of_variableCount_eq_zero
            fields hcount with ⟨constFields, hfields⟩
        exact ⟨.object constFields, by simp [ConstInputValue.ofInputValue?, hfields]⟩

  private theorem constInputValues_ofInputValues?_exists_of_variableCount_eq_zero
      : ∀ values,
          inputValueListVariableCount values = 0
          -> ∃ constValues,
              ConstInputValue.inputValuesToConstInputValues? values = some constValues
    | [] => fun _ => ⟨[], rfl⟩
    | value :: rest => by
        intro hcount
        simp only [inputValueListVariableCount, Nat.add_eq_zero_iff] at hcount
        rcases constInputValue_ofInputValue?_exists_of_variableCount_eq_zero
            value hcount.1 with ⟨constValue, hvalue⟩
        rcases constInputValues_ofInputValues?_exists_of_variableCount_eq_zero
            rest hcount.2 with ⟨constRest, hrest⟩
        exact ⟨constValue :: constRest, by
          simp [ConstInputValue.inputValuesToConstInputValues?, hvalue, hrest]⟩

  private theorem constInputFields_ofInputFields?_exists_of_variableCount_eq_zero
      : ∀ fields,
          inputValueObjectFieldsVariableCount fields = 0
          -> ∃ constFields,
              ConstInputValue.inputFieldsToConstInputFields? fields = some constFields
    | [] => fun _ => ⟨[], rfl⟩
    | (name, value) :: rest => by
        intro hcount
        simp only [inputValueObjectFieldsVariableCount, Nat.add_eq_zero_iff] at hcount
        rcases constInputValue_ofInputValue?_exists_of_variableCount_eq_zero
            value hcount.1 with ⟨constValue, hvalue⟩
        rcases constInputFields_ofInputFields?_exists_of_variableCount_eq_zero
            rest hcount.2 with ⟨constRest, hrest⟩
        exact ⟨(name, constValue) :: constRest, by
          simp [ConstInputValue.inputFieldsToConstInputFields?, hvalue, hrest]⟩
end

private def coercedInputValuesEquivalent (left right : CoercedInputValue) : Prop :=
  left.toInputValue.equivalent right.toInputValue

private theorem constInputValue_ofInputValue?_rel_of_equivalent
    {left right : InputValue} (hequivalent : left.equivalent right)
    : Option.Rel coercedInputValuesEquivalent
        (ConstInputValue.ofInputValue? left)
        (ConstInputValue.ofInputValue? right) := by
  have hcount := inputValueVariableCount_eq_of_equivalent hequivalent
  cases hleft : ConstInputValue.ofInputValue? left with
  | none =>
      cases hright : ConstInputValue.ofInputValue? right with
      | none => exact .none
      | some rightValue =>
          have hrightCount : inputValueVariableCount right = 0 := by
            rw [← constInputValue_toInputValue_ofInputValue?_eq_some hright]
            exact constInputValue_variableCount_toInputValue rightValue
          have hleftCount : inputValueVariableCount left = 0 := hcount.trans hrightCount
          rcases constInputValue_ofInputValue?_exists_of_variableCount_eq_zero
              left hleftCount with ⟨leftValue, hsome⟩
          rw [hleft] at hsome
          contradiction
  | some leftValue =>
      have hleftCount : inputValueVariableCount left = 0 := by
        rw [← constInputValue_toInputValue_ofInputValue?_eq_some hleft]
        exact constInputValue_variableCount_toInputValue leftValue
      have hrightCount : inputValueVariableCount right = 0 := hcount.symm.trans hleftCount
      rcases constInputValue_ofInputValue?_exists_of_variableCount_eq_zero
          right hrightCount with ⟨rightValue, hright⟩
      simp only [hright]
      apply Option.Rel.some
      unfold coercedInputValuesEquivalent
      rw [constInputValue_toInputValue_ofInputValue?_eq_some hleft,
        constInputValue_toInputValue_ofInputValue?_eq_some hright]
      exact hequivalent

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

private def inputCoercionResultsEquivalent
    : InputCoercionResult -> InputCoercionResult -> Prop
  | .undefined, .undefined => True
  | .success left, .success right => coercedInputValuesEquivalent left right
  | .error, .error => True
  | _, _ => False

private inductive CoercedInputValueListsEquivalent
    : List CoercedInputValue -> List CoercedInputValue -> Prop where
  | nil : CoercedInputValueListsEquivalent [] []
  | cons
    : coercedInputValuesEquivalent left right
      -> CoercedInputValueListsEquivalent leftRest rightRest
      -> CoercedInputValueListsEquivalent (left :: leftRest) (right :: rightRest)

private def coercedInputValueListResultsEquivalent
    : Except Unit (List CoercedInputValue) -> Except Unit (List CoercedInputValue) -> Prop
  | .ok left, .ok right => CoercedInputValueListsEquivalent left right
  | .error _, .error _ => True
  | _, _ => False

private def coercedInputObjectFieldEquivalent (left right : Name × CoercedInputValue)
    : Prop :=
  left.1 = right.1 ∧ coercedInputValuesEquivalent left.2 right.2

private inductive CoercedInputObjectFieldsEquivalent
    : List (Name × CoercedInputValue) -> List (Name × CoercedInputValue) -> Prop where
  | nil : CoercedInputObjectFieldsEquivalent [] []
  | cons
    : coercedInputObjectFieldEquivalent left right
      -> CoercedInputObjectFieldsEquivalent leftRest rightRest
      -> CoercedInputObjectFieldsEquivalent (left :: leftRest) (right :: rightRest)

private def coercedInputObjectFieldResultsEquivalent
    : Except Unit (List (Name × CoercedInputValue))
      -> Except Unit (List (Name × CoercedInputValue)) -> Prop
  | .ok left, .ok right => CoercedInputObjectFieldsEquivalent left right
  | .error _, .error _ => True
  | _, _ => False

private theorem coercedInputValueLists_canonical_eq
    {left right : List CoercedInputValue}
    (hequivalent : CoercedInputValueListsEquivalent left right)
    : InputValue.canonicalValues (ConstInputValue.valuesToInputValues left)
      = InputValue.canonicalValues (ConstInputValue.valuesToInputValues right) := by
  induction hequivalent with
  | nil => rfl
  | cons hvalue _hrest ih =>
      simp only [ConstInputValue.valuesToInputValues,
        InputValue.canonicalValues]
      rw [inputValue_canonical_eq_of_equivalent hvalue, ih]

private theorem coercedInputValuesEquivalent_list
    {left right : List CoercedInputValue}
    (hequivalent : CoercedInputValueListsEquivalent left right)
    : coercedInputValuesEquivalent (.list left) (.list right) := by
  unfold coercedInputValuesEquivalent
  apply inputValue_equivalent_of_canonical_eq_forCoercion
  simp only [ConstInputValue.toInputValue, InputValue.canonical]
  rw [coercedInputValueLists_canonical_eq hequivalent]

private theorem coercedInputObjectFields_canonical_eq
    {left right : List (Name × CoercedInputValue)}
    (hequivalent : CoercedInputObjectFieldsEquivalent left right)
    : InputValue.canonicalObjectFields (ConstInputValue.objectFieldsToInputFields left)
      = InputValue.canonicalObjectFields
          (ConstInputValue.objectFieldsToInputFields right) := by
  induction hequivalent with
  | nil => rfl
  | @cons leftField rightField leftRest rightRest hfield _hrest ih =>
      rcases leftField with ⟨leftName, leftValue⟩
      rcases rightField with ⟨rightName, rightValue⟩
      rcases hfield with ⟨hname, hvalue⟩
      change leftName = rightName at hname
      change coercedInputValuesEquivalent leftValue rightValue at hvalue
      subst rightName
      simp only [ConstInputValue.objectFieldsToInputFields,
        InputValue.canonicalObjectFields]
      rw [inputValue_canonical_eq_of_equivalent hvalue, ih]

private theorem coercedInputValuesEquivalent_object
    {left right : List (Name × CoercedInputValue)}
    (hequivalent : CoercedInputObjectFieldsEquivalent left right)
    : coercedInputValuesEquivalent (.object left) (.object right) := by
  unfold coercedInputValuesEquivalent
  apply inputValue_equivalent_of_canonical_eq_forCoercion
  simp only [ConstInputValue.toInputValue, InputValue.canonical]
  rw [coercedInputObjectFields_canonical_eq hequivalent]

private def coerceInputObjectFieldValueBounded
    (schema : Schema) (variableValues : VariableValues) (fuel : Nat)
    (definition : InputValueDefinition) (fields : List (Name × InputValue))
    : InputCoercionResult :=
  let suppliedResult :=
    match lookupInputObjectFieldValue? fields definition.name with
    | some value =>
        coerceInputValueBounded schema variableValues fuel definition.inputType value
    | none => .undefined
  match suppliedResult with
  | .success value => .success value
  | .error => .error
  | .undefined =>
      match definition.defaultValue with
      | some value =>
          coerceInputValueBounded schema variableValues fuel definition.inputType
            value.toInputValue
      | none => if definition.inputType.isNonNull then .error else .undefined

private theorem coerceInputObjectFieldsBounded_cons
    (schema : Schema) (variableValues : VariableValues) (fuel : Nat)
    (definition : InputValueDefinition) (definitions : List InputValueDefinition)
    (fields : List (Name × InputValue))
    : coerceInputObjectFieldsBounded schema variableValues fuel
        (definition :: definitions) fields
      = match coerceInputObjectFieldValueBounded schema variableValues fuel definition
                fields with
        | .error => .error ()
        | .undefined =>
            coerceInputObjectFieldsBounded schema variableValues fuel definitions fields
        | .success value =>
            match coerceInputObjectFieldsBounded schema variableValues fuel definitions
                    fields with
            | .error _ => .error ()
            | .ok coerced => .ok ((definition.name, value) :: coerced) := by
  cases hlookup : lookupInputObjectFieldValue? fields definition.name with
  | some value =>
      cases hvalue
            : coerceInputValueBounded schema variableValues fuel
                definition.inputType value with
      | success coerced =>
          simp [coerceInputObjectFieldsBounded, coerceInputObjectFieldValueBounded,
            hlookup, hvalue] <;> rfl
      | error =>
          simp [coerceInputObjectFieldsBounded, coerceInputObjectFieldValueBounded,
            hlookup, hvalue]
      | undefined =>
          cases hdefault : definition.defaultValue with
          | some defaultValue =>
              cases hdefaultResult : coerceInputValueBounded schema variableValues fuel
                  definition.inputType defaultValue.toInputValue <;>
                simp [coerceInputObjectFieldsBounded,
                  coerceInputObjectFieldValueBounded, hlookup, hvalue, hdefault,
                  hdefaultResult] <;> rfl
          | none =>
              cases hnonNull : definition.inputType.isNonNull <;>
                simp [coerceInputObjectFieldsBounded,
                  coerceInputObjectFieldValueBounded, hlookup, hvalue, hdefault,
                  hnonNull]
  | none =>
      cases hdefault : definition.defaultValue with
      | some defaultValue =>
          cases hdefaultResult : coerceInputValueBounded schema variableValues fuel
              definition.inputType defaultValue.toInputValue <;>
            simp [coerceInputObjectFieldsBounded, coerceInputObjectFieldValueBounded,
              hlookup, hdefault, hdefaultResult] <;> rfl
      | none =>
          cases hnonNull : definition.inputType.isNonNull <;>
            simp [coerceInputObjectFieldsBounded, coerceInputObjectFieldValueBounded,
              hlookup, hdefault, hnonNull]

private theorem inputValueVariables_mem_inputObjectFieldsVariables_of_lookup
    {fields : List (Name × InputValue)} {fieldName : Name} {value : InputValue}
    (hlookup : lookupInputObjectFieldValue? fields fieldName = some value)
    {variableName : Name}
    (hvariable : variableName ∈ Validation.inputValueVariables value)
    : variableName ∈ Validation.inputObjectFieldsVariables fields := by
  induction fields generalizing value with
  | nil => simp [lookupInputObjectFieldValue?] at hlookup
  | cons field rest ih =>
      rcases field with ⟨candidateName, candidateValue⟩
      by_cases hname : candidateName = fieldName
      · simp [lookupInputObjectFieldValue?, hname] at hlookup
        subst value
        exact List.mem_append_left _ hvariable
      · simp only [lookupInputObjectFieldValue?, hname, if_false] at hlookup
        exact List.mem_append_right _ (ih hlookup hvariable)

mutual
  private theorem constInputValue_toInputValue_has_no_variables
      : ∀ (value : ConstInputValue) variableName,
          variableName ∉ Validation.inputValueVariables value.toInputValue
    | .null, _
    | .int _, _
    | .float _, _
    | .string _, _
    | .boolean _, _
    | .enum _, _ => by simp [ConstInputValue.toInputValue,
        Validation.inputValueVariables]
    | .list values, variableName => by
        simpa [ConstInputValue.toInputValue, Validation.inputValueVariables] using
          constInputValues_toInputValues_have_no_variables values variableName
    | .object fields, variableName => by
        simpa [ConstInputValue.toInputValue, Validation.inputValueVariables] using
          constInputObjectFields_toInputFields_have_no_variables fields variableName

  private theorem constInputValues_toInputValues_have_no_variables
      : ∀ (values : List ConstInputValue) variableName,
          variableName
          ∉ Validation.inputValuesVariables (ConstInputValue.valuesToInputValues values)
    | [], _ => by simp [ConstInputValue.valuesToInputValues,
        Validation.inputValuesVariables]
    | value :: rest, variableName => by
        simp only [ConstInputValue.valuesToInputValues,
          Validation.inputValuesVariables, List.mem_append, not_or]
        exact ⟨constInputValue_toInputValue_has_no_variables value variableName,
          constInputValues_toInputValues_have_no_variables rest variableName⟩

  private theorem constInputObjectFields_toInputFields_have_no_variables
      : ∀ (fields : List (Name × ConstInputValue)) variableName,
          variableName
          ∉ Validation.inputObjectFieldsVariables
              (ConstInputValue.objectFieldsToInputFields fields)
    | [], _ => by simp [ConstInputValue.objectFieldsToInputFields,
        Validation.inputObjectFieldsVariables]
    | (name, value) :: rest, variableName => by
        simp only [ConstInputValue.objectFieldsToInputFields,
          Validation.inputObjectFieldsVariables, List.mem_append, not_or]
        exact ⟨constInputValue_toInputValue_has_no_variables value variableName,
          constInputObjectFields_toInputFields_have_no_variables rest variableName⟩
end

private theorem coerceInputValueBounded_equivalent
    (schema : Schema) {left right : VariableValues}
    : ∀ fuel inputType leftValue rightValue,
        leftValue.equivalent rightValue
        -> (∀ name,
              name ∈ Validation.inputValueVariables leftValue
              -> Option.Rel
                  (fun leftValue rightValue =>
                    InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
                  (lookupVariableValue? left name) (lookupVariableValue? right name))
        -> inputCoercionResultsEquivalent
            (coerceInputValueBounded schema left fuel inputType leftValue)
            (coerceInputValueBounded schema right fuel inputType rightValue) := by
  intro fuel
  induction fuel with
  | zero =>
      intro inputType leftValue rightValue hequivalent _hlookups
      simp [coerceInputValueBounded, inputCoercionResultsEquivalent]
  | succ fuel ih =>
      have hlist : ∀ inputType leftValues rightValues,
          InputValue.structuralValuesEquivalent
              (InputValue.canonicalValues leftValues)
              (InputValue.canonicalValues rightValues)
          -> (∀ name,
            name ∈ Validation.inputValuesVariables leftValues
            -> Option.Rel
                (fun leftValue rightValue =>
                  InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
                (lookupVariableValue? left name) (lookupVariableValue? right name))
          -> coercedInputValueListResultsEquivalent
              (coerceInputValueListBounded schema left fuel inputType leftValues)
              (coerceInputValueListBounded schema right fuel inputType rightValues) := by
        intro inputType leftValues
        induction leftValues with
        | nil =>
            intro rightValues hequivalent _hlookups
            cases rightValues with
            | nil =>
                simp only [coerceInputValueListBounded,
                  coercedInputValueListResultsEquivalent]
                exact .nil
            | cons rightValue rightRest =>
                simp [InputValue.canonicalValues,
                  InputValue.structuralValuesEquivalent] at hequivalent
        | cons leftValue leftRest ihRest =>
            intro rightValues hequivalent hlookups
            cases rightValues with
            | nil =>
                simp [InputValue.canonicalValues,
                  InputValue.structuralValuesEquivalent] at hequivalent
            | cons rightValue rightRest =>
                simp only [InputValue.canonicalValues,
                  InputValue.structuralValuesEquivalent] at hequivalent
                have hhead := ih inputType leftValue rightValue hequivalent.1 (by
                  intro name hname
                  exact hlookups name (by
                    exact List.mem_append_left _ hname))
                have htail := ihRest rightRest hequivalent.2 (by
                  intro name hname
                  exact hlookups name (by
                    exact List.mem_append_right _ hname))
                cases hleftHead : coerceInputValueBounded schema left fuel inputType
                    leftValue <;>
                  cases hrightHead : coerceInputValueBounded schema right fuel inputType
                    rightValue <;>
                  simp [hleftHead, hrightHead, inputCoercionResultsEquivalent] at hhead
                all_goals
                  cases hnonNull : inputType.isNonNull <;>
                    cases hleftTail : coerceInputValueListBounded schema left fuel
                        inputType leftRest <;>
                    cases hrightTail : coerceInputValueListBounded schema right fuel
                        inputType rightRest <;>
                    simp [coerceInputValueListBounded, hleftHead, hrightHead,
                      hnonNull, hleftTail, hrightTail,
                      coercedInputValueListResultsEquivalent] at htail ⊢
                  all_goals
                    first
                    | exact .cons hhead htail
                    | exact .cons
                        (inputValue_equivalent_refl_forCoercion
                          ConstInputValue.null.toInputValue)
                        htail
      have hobject : ∀ definitions leftFields rightFields,
          (∀ name,
            Option.Rel InputValue.equivalent
              (lookupInputObjectFieldValue? leftFields name)
              (lookupInputObjectFieldValue? rightFields name))
          -> (∀ name,
            name ∈ Validation.inputObjectFieldsVariables leftFields
            -> Option.Rel
                (fun leftValue rightValue =>
                  InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
                (lookupVariableValue? left name) (lookupVariableValue? right name))
          -> coercedInputObjectFieldResultsEquivalent
              (coerceInputObjectFieldsBounded schema left fuel definitions leftFields)
              (coerceInputObjectFieldsBounded schema right fuel definitions
                rightFields) := by
        intro definitions
        induction definitions with
        | nil =>
            intro leftFields rightFields hfields _hlookups
            simp only [coerceInputObjectFieldsBounded,
              coercedInputObjectFieldResultsEquivalent]
            exact .nil
        | cons definition rest ihRest =>
            intro leftFields rightFields hfields hlookups
            have hfield : inputCoercionResultsEquivalent
                (coerceInputObjectFieldValueBounded schema left fuel definition
                  leftFields)
                (coerceInputObjectFieldValueBounded schema right fuel definition
                  rightFields) := by
              have hlookup := hfields definition.name
              cases hleftLookup
                    : lookupInputObjectFieldValue? leftFields definition.name with
              | none =>
                  cases hrightLookup
                        : lookupInputObjectFieldValue? rightFields definition.name with
                  | some rightValue => simp [hleftLookup, hrightLookup] at hlookup
                  | none =>
                      cases hdefault : definition.defaultValue with
                      | none =>
                          cases hnonNull : definition.inputType.isNonNull <;>
                            simp [coerceInputObjectFieldValueBounded, hleftLookup,
                              hrightLookup, hdefault, hnonNull,
                              inputCoercionResultsEquivalent]
                      | some defaultValue =>
                          simpa [coerceInputObjectFieldValueBounded, hleftLookup,
                            hrightLookup, hdefault] using
                            ih definition.inputType defaultValue.toInputValue
                              defaultValue.toInputValue
                              (inputValue_equivalent_refl_forCoercion
                                defaultValue.toInputValue) (by
                                  intro name hname
                                  exact False.elim
                                    (constInputValue_toInputValue_has_no_variables
                                      defaultValue name hname))
              | some leftValue =>
                  cases hrightLookup
                        : lookupInputObjectFieldValue? rightFields definition.name with
                  | none => simp [hleftLookup, hrightLookup] at hlookup
                  | some rightValue =>
                      have hvalue : leftValue.equivalent rightValue := by
                        simpa [hleftLookup, hrightLookup] using hlookup
                      have hsupplied :=
                        ih definition.inputType leftValue rightValue hvalue (by
                          intro name hname
                          exact hlookups name
                            (inputValueVariables_mem_inputObjectFieldsVariables_of_lookup
                              hleftLookup hname))
                      have hdefault : inputCoercionResultsEquivalent
                          (match definition.defaultValue with
                          | some defaultValue =>
                              coerceInputValueBounded schema left fuel
                                definition.inputType defaultValue.toInputValue
                          | none =>
                              if definition.inputType.isNonNull then .error
                              else .undefined)
                          (match definition.defaultValue with
                          | some defaultValue =>
                              coerceInputValueBounded schema right fuel
                                definition.inputType defaultValue.toInputValue
                          | none =>
                              if definition.inputType.isNonNull then .error
                              else .undefined) := by
                        cases hdefaultValue : definition.defaultValue with
                        | none =>
                            cases hnonNull : definition.inputType.isNonNull <;>
                              simp [inputCoercionResultsEquivalent]
                        | some defaultValue =>
                            simpa [hdefaultValue] using
                              ih definition.inputType defaultValue.toInputValue
                                defaultValue.toInputValue
                                (inputValue_equivalent_refl_forCoercion
                                  defaultValue.toInputValue) (by
                                    intro name hname
                                    exact False.elim
                                      (constInputValue_toInputValue_has_no_variables
                                        defaultValue name hname))
                      cases hleftSupplied : coerceInputValueBounded schema left fuel
                              definition.inputType leftValue
                      <;>
                        cases hrightSupplied : coerceInputValueBounded schema right fuel
                              definition.inputType rightValue
                      <;>
                          simp [hleftSupplied, hrightSupplied,
                            inputCoercionResultsEquivalent] at hsupplied
                      all_goals
                        simp [coerceInputObjectFieldValueBounded, hleftLookup,
                          hrightLookup, hleftSupplied, hrightSupplied]
                      all_goals first | exact hsupplied | exact hdefault | trivial
            have hrest := ihRest leftFields rightFields hfields hlookups
            rw [coerceInputObjectFieldsBounded_cons,
              coerceInputObjectFieldsBounded_cons]
            cases hleftField : coerceInputObjectFieldValueBounded schema left fuel
                    definition leftFields
            <;>
              cases hrightField : coerceInputObjectFieldValueBounded schema right fuel
                    definition rightFields
            <;>
                simp [hleftField, hrightField, inputCoercionResultsEquivalent] at hfield
            all_goals
              cases hleftRest : coerceInputObjectFieldsBounded schema left fuel rest
                      leftFields <;>
                cases hrightRest : coerceInputObjectFieldsBounded schema right fuel rest
                      rightFields <;>
                simp [hleftRest, hrightRest,
                  coercedInputObjectFieldResultsEquivalent] at hrest ⊢
            all_goals first | exact .cons ⟨rfl, hfield⟩ hrest | exact hrest | trivial
      intro inputType leftValue rightValue hequivalent hlookups
      have hcanonical := inputValue_canonical_eq_of_equivalent hequivalent
      cases leftValue <;> cases rightValue <;>
        simp [InputValue.canonical] at hcanonical
      case null.null =>
        cases inputType <;>
          simp [coerceInputValueBounded, inputCoercionResultsEquivalent,
            coercedInputValuesEquivalent,
            inputValue_equivalent_refl_forCoercion]
      case int.int leftInt rightInt =>
        subst rightInt
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.int leftInt) (.int leftInt)
                (inputValue_equivalent_refl_forCoercion (.int leftInt)) hlookups
        | list inner =>
            have hcoerced := ih inner (.int leftInt) (.int leftInt)
              (inputValue_equivalent_refl_forCoercion (.int leftInt)) hlookups
            cases hleft : coerceInputValueBounded schema left fuel inner
                    (.int leftInt) <;>
              cases hright : coerceInputValueBounded schema right fuel inner
                    (.int leftInt) <;>
              simp [coerceInputValueBounded, hleft, hright,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list (.cons hcoerced .nil)
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName <;>
              simp [coerceInputValueBounded, hinputObject,
                ConstInputValue.ofInputValue?,
                inputCoercionResultsEquivalent, coercedInputValuesEquivalent,
                inputValue_equivalent_refl_forCoercion]
      case float.float leftFloat rightFloat =>
        subst rightFloat
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.float leftFloat) (.float leftFloat)
                (inputValue_equivalent_refl_forCoercion (.float leftFloat)) hlookups
        | list inner =>
            have hcoerced := ih inner (.float leftFloat) (.float leftFloat)
              (inputValue_equivalent_refl_forCoercion (.float leftFloat)) hlookups
            cases hleft : coerceInputValueBounded schema left fuel inner
                    (.float leftFloat) <;>
              cases hright : coerceInputValueBounded schema right fuel inner
                    (.float leftFloat) <;>
              simp [coerceInputValueBounded, hleft, hright,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list (.cons hcoerced .nil)
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName <;>
              simp [coerceInputValueBounded, hinputObject,
                ConstInputValue.ofInputValue?,
                inputCoercionResultsEquivalent, coercedInputValuesEquivalent,
                inputValue_equivalent_refl_forCoercion]
      case string.string leftString rightString =>
        subst rightString
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.string leftString) (.string leftString)
                (inputValue_equivalent_refl_forCoercion (.string leftString)) hlookups
        | list inner =>
            have hcoerced := ih inner (.string leftString) (.string leftString)
              (inputValue_equivalent_refl_forCoercion (.string leftString)) hlookups
            cases hleft : coerceInputValueBounded schema left fuel inner
                    (.string leftString) <;>
              cases hright : coerceInputValueBounded schema right fuel inner
                    (.string leftString) <;>
              simp [coerceInputValueBounded, hleft, hright,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list (.cons hcoerced .nil)
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName <;>
              simp [coerceInputValueBounded, hinputObject,
                ConstInputValue.ofInputValue?,
                inputCoercionResultsEquivalent, coercedInputValuesEquivalent,
                inputValue_equivalent_refl_forCoercion]
      case boolean.boolean leftBool rightBool =>
        subst rightBool
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.boolean leftBool) (.boolean leftBool)
                (inputValue_equivalent_refl_forCoercion (.boolean leftBool)) hlookups
        | list inner =>
            have hcoerced := ih inner (.boolean leftBool) (.boolean leftBool)
              (inputValue_equivalent_refl_forCoercion (.boolean leftBool)) hlookups
            cases hleft : coerceInputValueBounded schema left fuel inner
                    (.boolean leftBool) <;>
              cases hright : coerceInputValueBounded schema right fuel inner
                    (.boolean leftBool) <;>
              simp [coerceInputValueBounded, hleft, hright,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list (.cons hcoerced .nil)
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName <;>
              simp [coerceInputValueBounded, hinputObject,
                ConstInputValue.ofInputValue?,
                inputCoercionResultsEquivalent, coercedInputValuesEquivalent,
                inputValue_equivalent_refl_forCoercion]
      case enum.enum leftEnum rightEnum =>
        subst rightEnum
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.enum leftEnum) (.enum leftEnum)
                (inputValue_equivalent_refl_forCoercion (.enum leftEnum)) hlookups
        | list inner =>
            have hcoerced := ih inner (.enum leftEnum) (.enum leftEnum)
              (inputValue_equivalent_refl_forCoercion (.enum leftEnum)) hlookups
            cases hleft : coerceInputValueBounded schema left fuel inner
                    (.enum leftEnum) <;>
              cases hright : coerceInputValueBounded schema right fuel inner
                    (.enum leftEnum) <;>
              simp [coerceInputValueBounded, hleft, hright,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list (.cons hcoerced .nil)
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName <;>
              simp [coerceInputValueBounded, hinputObject,
                ConstInputValue.ofInputValue?,
                inputCoercionResultsEquivalent, coercedInputValuesEquivalent,
                inputValue_equivalent_refl_forCoercion]
      case list.list leftValues rightValues =>
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.list leftValues) (.list rightValues)
                (inputValue_equivalent_of_canonical_eq_forCoercion (by
                  simpa [InputValue.canonical] using hcanonical)) hlookups
        | list inner =>
            have hcoerced := hlist inner leftValues rightValues (by
              simpa [InputValue.equivalent, InputValue.canonical,
                InputValue.structuralEquivalent] using hequivalent) hlookups
            cases hleft : coerceInputValueListBounded schema left fuel inner
                    leftValues <;>
              cases hright : coerceInputValueListBounded schema right fuel inner
                    rightValues <;>
              simp [coerceInputValueBounded, hleft, hright,
                coercedInputValueListResultsEquivalent,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list hcoerced
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName with
            | some inputObject =>
                simp [coerceInputValueBounded, hinputObject,
                  inputCoercionResultsEquivalent]
            | none =>
                have hvalue : (InputValue.list leftValues).equivalent
                    (.list rightValues) :=
                  inputValue_equivalent_of_canonical_eq_forCoercion (by
                    simpa [InputValue.canonical] using hcanonical)
                have hconst :=
                  constInputValue_ofInputValue?_rel_of_equivalent hvalue
                cases hleft : ConstInputValue.ofInputValue? (.list leftValues) <;>
                  cases hright : ConstInputValue.ofInputValue? (.list rightValues) <;>
                  simp [coerceInputValueBounded, hinputObject, hleft, hright,
                    inputCoercionResultsEquivalent] at hconst ⊢
                exact hconst
      case object.object leftFields rightFields =>
        cases inputType with
        | nonNull inner =>
            simpa [coerceInputValueBounded] using
              ih inner (.object leftFields) (.object rightFields)
                (inputValue_equivalent_of_canonical_eq_forCoercion (by
                  simpa [InputValue.canonical] using hcanonical)) hlookups
        | list inner =>
            have hvalue : (InputValue.object leftFields).equivalent
                (.object rightFields) :=
              inputValue_equivalent_of_canonical_eq_forCoercion (by
                simpa [InputValue.canonical] using hcanonical)
            have hcoerced := ih inner (.object leftFields) (.object rightFields) hvalue
              hlookups
            cases hleft : coerceInputValueBounded schema left fuel inner
                    (.object leftFields) <;>
              cases hright : coerceInputValueBounded schema right fuel inner
                    (.object rightFields) <;>
              simp [coerceInputValueBounded, hleft, hright,
                inputCoercionResultsEquivalent] at hcoerced ⊢
            exact coercedInputValuesEquivalent_list (.cons hcoerced .nil)
        | named typeName =>
            cases hinputObject : schema.lookupInputObject typeName with
            | none =>
                simp [coerceInputValueBounded, hinputObject,
                  inputCoercionResultsEquivalent]
            | some inputObject =>
                have hcanonicalFields :
                    InputValue.sortObjectFieldsByName
                        (InputValue.canonicalObjectFields leftFields)
                      = InputValue.sortObjectFieldsByName
                        (InputValue.canonicalObjectFields rightFields) := by
                  simpa [InputValue.canonical] using hcanonical
                have hknown :
                    inputObjectFieldsKnownBool inputObject.inputFields leftFields
                      = inputObjectFieldsKnownBool inputObject.inputFields
                        rightFields := by
                  calc
                    inputObjectFieldsKnownBool inputObject.inputFields leftFields
                        = inputObjectFieldsKnownBool inputObject.inputFields
                            (InputValue.sortObjectFieldsByName
                              (InputValue.canonicalObjectFields leftFields)) :=
                      (inputObjectFieldsKnownBool_canonical
                        inputObject.inputFields leftFields).symm
                    _ = inputObjectFieldsKnownBool inputObject.inputFields
                          (InputValue.sortObjectFieldsByName
                            (InputValue.canonicalObjectFields rightFields)) := by
                      rw [hcanonicalFields]
                    _ = inputObjectFieldsKnownBool inputObject.inputFields rightFields :=
                      inputObjectFieldsKnownBool_canonical
                        inputObject.inputFields rightFields
                have hfields : ∀ name,
                    Option.Rel InputValue.equivalent
                      (lookupInputObjectFieldValue? leftFields name)
                      (lookupInputObjectFieldValue? rightFields name) := by
                  intro name
                  exact optionRel_inputValueEquivalent_iff_canonical_map_eq.mpr
                    (lookupInputObjectFieldValue?_canonical_map_eq
                      hcanonicalFields name)
                have hcoerced := hobject inputObject.inputFields leftFields
                  rightFields hfields hlookups
                cases hknownLeft : inputObjectFieldsKnownBool
                        inputObject.inputFields leftFields <;>
                  cases hknownRight : inputObjectFieldsKnownBool
                        inputObject.inputFields rightFields <;>
                  simp [hknownLeft, hknownRight] at hknown
                all_goals
                  cases hleftFields : coerceInputObjectFieldsBounded schema left fuel
                          inputObject.inputFields leftFields <;>
                    cases hrightFields : coerceInputObjectFieldsBounded schema right fuel
                          inputObject.inputFields rightFields <;>
                    simp [coerceInputValueBounded, hinputObject, hknownLeft,
                      hknownRight, hleftFields, hrightFields,
                      coercedInputObjectFieldResultsEquivalent,
                      inputCoercionResultsEquivalent] at hcoerced ⊢
                exact coercedInputValuesEquivalent_object hcoerced
      case variable.variable leftName rightName =>
        subst rightName
        have hrelated := hlookups leftName (by
          simp [Validation.inputValueVariables])
        cases hleft : lookupVariableValue? left leftName with
        | none =>
            cases hright : lookupVariableValue? right leftName with
            | none =>
                simp [coerceInputValueBounded, hleft, hright,
                  inputCoercionResultsEquivalent]
            | some rightValue => simp [hleft, hright] at hrelated
        | some leftValue =>
            cases hright : lookupVariableValue? right leftName with
            | none => simp [hleft, hright] at hrelated
            | some rightValue =>
                have hvalue : leftValue.toInputValue.equivalent
                    rightValue.toInputValue := by
                  simpa [hleft, hright] using hrelated
                simpa [coerceInputValueBounded, hleft, hright] using
                  ih inputType leftValue.toInputValue rightValue.toInputValue hvalue (by
                    intro name hname
                    exact False.elim
                      (constInputValue_toInputValue_has_no_variables leftValue name
                        hname))

theorem coerceInputValue_equivalent_of_equivalent
    (schema : Schema) {left right : VariableValues}
    (hvalues : variableValuesCoercionEquivalent left right)
    (inputType : TypeRef) {leftValue rightValue : InputValue}
    (hvalue : leftValue.equivalent rightValue)
    : inputCoercionResultsEquivalent
        (coerceInputValue schema left inputType leftValue)
        (coerceInputValue schema right inputType rightValue) := by
  have hfuel := referencedVariableValuesCoercionFuel_eq_of_equivalent
    hvalues.1 hvalue
  have hvalueFuel := inputValueCoercionFuel_eq_of_equivalent hvalue
  simpa [coerceInputValue, coerceInputValueFuel, hfuel, hvalueFuel] using
    coerceInputValueBounded_equivalent schema
      (schemaInputCoercionFuel schema
        + referencedVariableValuesCoercionFuel right rightValue
        + inputValueCoercionFuel rightValue)
      inputType leftValue rightValue hvalue (fun name _hname => hvalues.1 name)

theorem coerceInputValue_equivalent_of_variableValuesCoercionEquivalent
    (schema : Schema) {left right : VariableValues}
    (hvalues : variableValuesCoercionEquivalent left right)
    (inputType : TypeRef) (value : InputValue)
    : inputCoercionResultsEquivalent
        (coerceInputValue schema left inputType value)
        (coerceInputValue schema right inputType value) :=
  coerceInputValue_equivalent_of_equivalent schema hvalues inputType
    (inputValue_equivalent_refl_forCoercion value)

theorem coerceInputValue_equivalent_of_lookup_agreement
    (schema : Schema) {left right : VariableValues}
    (inputType : TypeRef) (value : InputValue)
    (hlookups
      : ∀ name,
          name ∈ Validation.inputValueVariables value
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? left name) (lookupVariableValue? right name))
    : inputCoercionResultsEquivalent
        (coerceInputValue schema left inputType value)
        (coerceInputValue schema right inputType value) := by
  have hfuel := referencedVariableValuesCoercionFuel_eq_of_lookup_agreement value
    hlookups
  simpa [coerceInputValue, coerceInputValueFuel, hfuel] using
    coerceInputValueBounded_equivalent schema
      (schemaInputCoercionFuel schema
        + referencedVariableValuesCoercionFuel right value
        + inputValueCoercionFuel value)
      inputType value value (inputValue_equivalent_refl_forCoercion value) hlookups

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

private theorem coercedArgumentsEquivalent_nil
    : CoercedArgument.argumentsEquivalent [] [] := by
  simp [CoercedArgument.argumentsEquivalent]

private theorem coercedArgumentsEquivalent_cons
    {leftArgument rightArgument : CoercedArgument}
    {leftRest rightRest : CoercedArguments}
    (hargument : leftArgument.equivalent rightArgument)
    (hrest : CoercedArgument.argumentsEquivalent leftRest rightRest)
    : CoercedArgument.argumentsEquivalent (leftArgument :: leftRest)
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

theorem CoercedArgument.argumentsEquivalent_refl (arguments : CoercedArguments)
    : CoercedArgument.argumentsEquivalent arguments arguments := by
  constructor <;> intro argument hargument <;>
    exact ⟨argument, hargument,
      ⟨rfl, inputValue_equivalent_refl_forCoercion argument.value.toInputValue⟩⟩

theorem CoercedArgument.argumentsEquivalent_symm
    {left right : CoercedArguments}
    (hequivalent : CoercedArgument.argumentsEquivalent left right)
    : CoercedArgument.argumentsEquivalent right left := by
  constructor
  · intro argument hargument
    rcases hequivalent.2 argument hargument with
      ⟨other, hother, hargumentEquivalent⟩
    exact ⟨other, hother,
      ⟨hargumentEquivalent.1.symm,
        inputValue_equivalent_symm_forCoercion hargumentEquivalent.2⟩⟩
  · intro argument hargument
    rcases hequivalent.1 argument hargument with
      ⟨other, hother, hargumentEquivalent⟩
    exact ⟨other, hother,
      ⟨hargumentEquivalent.1.symm,
        inputValue_equivalent_symm_forCoercion hargumentEquivalent.2⟩⟩

theorem ArgumentCoercionResult.equivalent_trans
    {left middle right : ArgumentCoercionResult}
    (hleft : left.equivalent middle) (hright : middle.equivalent right)
    : left.equivalent right := by
  cases left <;> cases middle <;> cases right <;>
    simp [ArgumentCoercionResult.equivalent] at hleft hright ⊢
  exact CoercedArgument.argumentsEquivalent_trans hleft hright

theorem ArgumentCoercionResult.equivalent_symm
    {left right : ArgumentCoercionResult}
    (hequivalent : left.equivalent right)
    : right.equivalent left := by
  cases left <;> cases right <;>
    simp [ArgumentCoercionResult.equivalent] at hequivalent ⊢
  exact CoercedArgument.argumentsEquivalent_symm hequivalent

private theorem coerceArgumentDefault_equivalent
    (schema : Schema) {left right : VariableValues}
    (hvalues : variableValuesCoercionEquivalent left right)
    (definition : InputValueDefinition)
    : inputCoercionResultsEquivalent
        (coerceArgumentDefault schema left definition)
        (coerceArgumentDefault schema right definition) := by
  cases hdefault : definition.defaultValue with
  | none =>
      cases hnonNull : definition.inputType.isNonNull <;>
        simp [coerceArgumentDefault, hdefault, hnonNull,
          inputCoercionResultsEquivalent]
  | some defaultValue =>
      simpa [coerceArgumentDefault, hdefault] using
        coerceInputValue_equivalent_of_variableValuesCoercionEquivalent
          schema hvalues definition.inputType defaultValue.toInputValue

private theorem coerceArgumentValue_equivalent_of_lookup
    (schema : Schema) {leftValues rightValues : VariableValues}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (definition : InputValueDefinition) {leftArguments rightArguments : List Argument}
    (hlookup
      : Option.Rel InputValue.equivalent
          (Argument.lookupValue? leftArguments definition.name)
          (Argument.lookupValue? rightArguments definition.name))
    : inputCoercionResultsEquivalent
        (coerceArgumentValue schema leftValues definition leftArguments)
        (coerceArgumentValue schema rightValues definition rightArguments) := by
  cases hleftLookup : Argument.lookupValue? leftArguments definition.name with
  | none =>
      cases hrightLookup : Argument.lookupValue? rightArguments definition.name with
      | none =>
          simpa [coerceArgumentValue, hleftLookup, hrightLookup] using
            coerceArgumentDefault_equivalent schema hvalues definition
      | some rightValue => simp [hleftLookup, hrightLookup] at hlookup
  | some leftValue =>
      cases hrightLookup : Argument.lookupValue? rightArguments definition.name with
      | none => simp [hleftLookup, hrightLookup] at hlookup
      | some rightValue =>
          have hvalue : leftValue.equivalent rightValue := by
            simpa [hleftLookup, hrightLookup] using hlookup
          have hsupplied := coerceInputValue_equivalent_of_equivalent
            schema hvalues definition.inputType hvalue
          have hdefault := coerceArgumentDefault_equivalent schema hvalues definition
          cases hleftSupplied : coerceInputValue schema leftValues
                  definition.inputType leftValue <;>
            cases hrightSupplied : coerceInputValue schema rightValues
                  definition.inputType rightValue <;>
            simp [hleftSupplied, hrightSupplied, inputCoercionResultsEquivalent]
              at hsupplied
          all_goals
            simp [coerceArgumentValue, hleftLookup, hrightLookup, hleftSupplied,
              hrightSupplied]
          all_goals first | exact hsupplied | exact hdefault | trivial

private theorem coerceArgumentValues_equivalent_of_lookups
    (schema : Schema) {leftValues rightValues : VariableValues}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    : ∀ definitions leftArguments rightArguments,
        (∀ name,
          Option.Rel InputValue.equivalent
            (Argument.lookupValue? leftArguments name)
            (Argument.lookupValue? rightArguments name))
        -> ArgumentCoercionResult.equivalent
            (coerceArgumentValues schema leftValues definitions leftArguments)
            (coerceArgumentValues schema rightValues definitions rightArguments)
  | [], _leftArguments, _rightArguments, _hlookup =>
      coercedArgumentsEquivalent_nil
  | definition :: definitions, leftArguments, rightArguments, hlookup => by
      have hrest := coerceArgumentValues_equivalent_of_lookups schema hvalues
        definitions leftArguments rightArguments hlookup
      cases hleftRest : coerceArgumentValues schema leftValues definitions
              leftArguments <;>
        cases hrightRest : coerceArgumentValues schema rightValues definitions
              rightArguments <;>
        simp [hleftRest, hrightRest, ArgumentCoercionResult.equivalent] at hrest
      case error.error =>
        simp [coerceArgumentValues, hleftRest, hrightRest,
          ArgumentCoercionResult.equivalent]
      case success.success leftRest rightRest =>
        have heffective := coerceArgumentValue_equivalent_of_lookup schema hvalues
          definition (hlookup definition.name)
        cases hleftEffective : coerceArgumentValue schema leftValues definition
                leftArguments <;>
          cases hrightEffective : coerceArgumentValue schema rightValues definition
                rightArguments <;>
          simp [hleftEffective, hrightEffective, inputCoercionResultsEquivalent]
            at heffective
        · simpa [coerceArgumentValues, hleftRest, hrightRest, hleftEffective,
            hrightEffective, ArgumentCoercionResult.equivalent] using hrest
        · simpa [coerceArgumentValues, hleftRest, hrightRest, hleftEffective,
            hrightEffective, ArgumentCoercionResult.equivalent] using
            coercedArgumentsEquivalent_cons
              (leftArgument := ⟨definition.name, _⟩)
              (rightArgument := ⟨definition.name, _⟩)
              (by exact ⟨rfl, heffective⟩) hrest
        · simp [coerceArgumentValues, hleftRest, hrightRest, hleftEffective,
            hrightEffective, ArgumentCoercionResult.equivalent]

theorem coerceArgumentValues_equivalent_of_equivalent
    (schema : Schema) (variableValues : VariableValues)
    (definitions : List InputValueDefinition) {left right : List Argument}
    (hleft : (left.map Argument.name).Nodup)
    (hright : (right.map Argument.name).Nodup)
    (hequivalent : Argument.argumentsEquivalent left right)
    : ArgumentCoercionResult.equivalent
        (coerceArgumentValues schema variableValues definitions left)
        (coerceArgumentValues schema variableValues definitions right) := by
  apply coerceArgumentValues_equivalent_of_lookups schema
    (variableValuesCoercionEquivalent_refl variableValues)
  exact lookupValue_equivalent hleft hright hequivalent

theorem coerceArgumentValues_equivalent_of_variableValuesCoercionEquivalent
    (schema : Schema) {left right : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent left right)
    (definitions : List InputValueDefinition) (arguments : List Argument)
    : ArgumentCoercionResult.equivalent
        (coerceArgumentValues schema left definitions arguments)
        (coerceArgumentValues schema right definitions arguments) := by
  apply coerceArgumentValues_equivalent_of_lookups schema hequivalent
  intro name
  cases Argument.lookupValue? arguments name with
  | none => exact .none
  | some value => exact .some (inputValue_equivalent_refl_forCoercion value)

private theorem coerceArgumentDefault_equivalent_of_lookup_agreement
    (schema : Schema) {left right : VariableValues}
    (definition : InputValueDefinition)
    : inputCoercionResultsEquivalent
        (coerceArgumentDefault schema left definition)
        (coerceArgumentDefault schema right definition) := by
  cases hdefault : definition.defaultValue with
  | none =>
      cases hnonNull : definition.inputType.isNonNull <;>
        simp [coerceArgumentDefault, hdefault, hnonNull,
          inputCoercionResultsEquivalent]
  | some defaultValue =>
      simpa [coerceArgumentDefault, hdefault] using
        coerceInputValue_equivalent_of_lookup_agreement schema definition.inputType
          defaultValue.toInputValue (by
            intro name hname
            exact False.elim
              (constInputValue_toInputValue_has_no_variables defaultValue name hname))

private theorem coerceArgumentValue_equivalent_of_lookup_agreement
    (schema : Schema) {left right : VariableValues}
    (definition : InputValueDefinition) (arguments : List Argument)
    (hlookups
      : ∀ name,
          name ∈ Validation.argumentsVariables arguments
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? left name) (lookupVariableValue? right name))
    : inputCoercionResultsEquivalent
        (coerceArgumentValue schema left definition arguments)
        (coerceArgumentValue schema right definition arguments) := by
  cases hlookup : Argument.lookupValue? arguments definition.name with
  | none =>
      simpa [coerceArgumentValue, hlookup] using
        coerceArgumentDefault_equivalent_of_lookup_agreement schema definition
  | some value =>
      have hsupplied := coerceInputValue_equivalent_of_lookup_agreement schema
        definition.inputType value (by
          intro name hname
          rcases lookupValue_eq_some_mem hlookup with
            ⟨argument, hargument, _hargumentName, hargumentValue⟩
          subst value
          exact hlookups name
            ((Validation.argumentsVariables_mem_iff name arguments).2
              ⟨argument, hargument, hname⟩))
      have hdefault :=
        coerceArgumentDefault_equivalent_of_lookup_agreement
          (left := left) (right := right) schema definition
      cases hleftSupplied : coerceInputValue schema left definition.inputType value <;>
        cases hrightSupplied : coerceInputValue schema right definition.inputType value <;>
        simp [hleftSupplied, hrightSupplied, inputCoercionResultsEquivalent] at hsupplied
      all_goals
        simp [coerceArgumentValue, hlookup, hleftSupplied, hrightSupplied]
      all_goals first | exact hsupplied | exact hdefault | trivial

theorem coerceArgumentValues_equivalent_of_lookup_agreement
    (schema : Schema) {left right : VariableValues}
    (definitions : List InputValueDefinition) (arguments : List Argument)
    (hlookups
      : ∀ name,
          name ∈ Validation.argumentsVariables arguments
          -> Option.Rel
              (fun leftValue rightValue =>
                InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
              (lookupVariableValue? left name) (lookupVariableValue? right name))
    : ArgumentCoercionResult.equivalent
        (coerceArgumentValues schema left definitions arguments)
        (coerceArgumentValues schema right definitions arguments) := by
  induction definitions with
  | nil => exact coercedArgumentsEquivalent_nil
  | cons definition rest ih =>
      cases hleftRest : coerceArgumentValues schema left rest arguments <;>
        cases hrightRest : coerceArgumentValues schema right rest arguments <;>
        simp [hleftRest, hrightRest, ArgumentCoercionResult.equivalent] at ih
      case error.error =>
        simp [coerceArgumentValues, hleftRest, hrightRest,
          ArgumentCoercionResult.equivalent]
      case success.success leftRest rightRest =>
        have heffective := coerceArgumentValue_equivalent_of_lookup_agreement
          schema definition arguments hlookups
        cases hleftEffective : coerceArgumentValue schema left definition arguments <;>
          cases hrightEffective : coerceArgumentValue schema right definition arguments <;>
          simp [hleftEffective, hrightEffective, inputCoercionResultsEquivalent]
            at heffective
        · simpa [coerceArgumentValues, hleftRest, hrightRest, hleftEffective,
            hrightEffective, ArgumentCoercionResult.equivalent] using ih
        · simpa [coerceArgumentValues, hleftRest, hrightRest, hleftEffective,
            hrightEffective, ArgumentCoercionResult.equivalent] using
            coercedArgumentsEquivalent_cons
              (leftArgument := ⟨definition.name, _⟩)
              (rightArgument := ⟨definition.name, _⟩)
              (by exact ⟨rfl, heffective⟩) ih
        · simp [coerceArgumentValues, hleftRest, hrightRest, hleftEffective,
            hrightEffective, ArgumentCoercionResult.equivalent]

theorem ArgumentCoercionResult.isSuccess_eq_of_equivalent
    {left right : ArgumentCoercionResult} (hequivalent : left.equivalent right)
    : left.isSuccess = right.isSuccess := by
  cases left <;> cases right <;>
    simp [ArgumentCoercionResult.equivalent] at hequivalent ⊢

theorem coerceArgumentValues_isSuccess_eq_of_variableValuesCoercionEquivalent
    (schema : Schema) {left right : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent left right)
    (definitions : List InputValueDefinition) (arguments : List Argument)
    : (coerceArgumentValues schema left definitions arguments).isSuccess
      = (coerceArgumentValues schema right definitions arguments).isSuccess :=
  ArgumentCoercionResult.isSuccess_eq_of_equivalent
    (coerceArgumentValues_equivalent_of_variableValuesCoercionEquivalent
      schema hequivalent definitions arguments)

theorem coerceArgumentValues_isSuccess_eq_of_equivalent
    (schema : Schema) (variableValues : VariableValues)
    (definitions : List InputValueDefinition) {left right : List Argument}
    (hleft : (left.map Argument.name).Nodup)
    (hright : (right.map Argument.name).Nodup)
    (hequivalent : Argument.argumentsEquivalent left right)
    : (coerceArgumentValues schema variableValues definitions left).isSuccess
      = (coerceArgumentValues schema variableValues definitions right).isSuccess :=
  ArgumentCoercionResult.isSuccess_eq_of_equivalent
    (coerceArgumentValues_equivalent_of_equivalent schema variableValues definitions
      hleft hright hequivalent)

def validArgumentsCoercionSucceeds (schema : Schema) (variableValues : VariableValues)
    (variableDefinitions : List VariableDefinition)
    : Prop :=
  ∀ definitions arguments,
    Validation.argumentsValid schema definitions variableDefinitions arguments
    -> (coerceArgumentValues schema variableValues definitions arguments).isSuccess = true

theorem validArgumentsCoercionSucceeds_of_variableValuesCoercionEquivalent
    (schema : Schema) {left right : VariableValues}
    (hequivalent : variableValuesCoercionEquivalent left right)
    {variableDefinitions : List VariableDefinition}
    : validArgumentsCoercionSucceeds schema right variableDefinitions
      -> validArgumentsCoercionSucceeds schema left variableDefinitions := by
  intro hright definitions arguments hvalid
  rw [coerceArgumentValues_isSuccess_eq_of_variableValuesCoercionEquivalent
    schema hequivalent definitions arguments]
  exact hright definitions arguments hvalid

private theorem variableValuesCoercionEquivalent_cons
    {left right : VariableValues} {leftValue rightValue : ConstInputValue}
    (hequivalent : variableValuesCoercionEquivalent left right)
    (name : Name) (hvalue : leftValue.toInputValue.equivalent rightValue.toInputValue)
    : variableValuesCoercionEquivalent ((name, leftValue) :: left)
        ((name, rightValue) :: right) := by
  constructor
  · intro candidate
    by_cases hname : name = candidate
    · simpa [lookupVariableValue?, hname] using hvalue
    · simpa [lookupVariableValue?, hname] using hequivalent.1 candidate
  · simp [variableValuesCoercionFuel, hequivalent.2,
      inputValueCoercionFuel_eq_of_equivalent hvalue]

private def materializeVariableDefault (values : VariableValues)
    (definition : VariableDefinition)
    : VariableValues :=
  match lookupVariableValue? values definition.name with
  | some _value => values
  | none =>
      match definition.defaultValue with
      | some defaultValue => (definition.name, defaultValue) :: values
      | none => values

private def variableDefaultFuelContribution (values : VariableValues)
    (definition : VariableDefinition)
    : Nat :=
  match lookupVariableValue? values definition.name, definition.defaultValue with
  | none, some defaultValue => inputValueCoercionFuel defaultValue.toInputValue
  | _, _ => 0

private theorem lookupVariableValue?_foldl_materializeVariableDefault_of_name_not_mem
    (definitions : List VariableDefinition) (variableValues : VariableValues)
    (name : Name) (hname : name ∉ definitions.map VariableDefinition.name)
    : lookupVariableValue?
        (definitions.foldl materializeVariableDefault variableValues) name
      = lookupVariableValue? variableValues name := by
  induction definitions generalizing variableValues with
  | nil => rfl
  | cons definition rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at hname
      simp only [List.foldl_cons]
      apply (ih _ hname.2).trans
      simp only [materializeVariableDefault]
      split
      · rfl
      · split
        · simp only [lookupVariableValue?]
          split
          · rename_i heq
            exact (hname.1 heq.symm).elim
          · rfl
        · rfl

private theorem lookupVariableValue?_foldl_materializeVariableDefault_at_definition
    {definitions : List VariableDefinition} {definition : VariableDefinition}
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    (hdefinition : definition ∈ definitions) (variableValues : VariableValues)
    : lookupVariableValue?
        (definitions.foldl materializeVariableDefault variableValues) definition.name
      = match lookupVariableValue? variableValues definition.name with
        | some value => some value
        | none => definition.defaultValue := by
  induction definitions generalizing variableValues with
  | nil => simp at hdefinition
  | cons candidate rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hdefinition with rfl | hrest
      · simp only [List.foldl_cons, materializeVariableDefault]
        cases hlookup : lookupVariableValue? variableValues definition.name with
        | some value =>
            simpa [hlookup] using
              lookupVariableValue?_foldl_materializeVariableDefault_of_name_not_mem
                rest variableValues definition.name hnodup.1
        | none =>
            cases hdefault : definition.defaultValue with
            | none =>
                simpa [hlookup, hdefault] using
                  lookupVariableValue?_foldl_materializeVariableDefault_of_name_not_mem
                    rest variableValues definition.name hnodup.1
            | some defaultValue =>
                have hadded : lookupVariableValue?
                    ((definition.name, defaultValue) :: variableValues)
                    definition.name = some defaultValue := by
                  simp [lookupVariableValue?]
                simpa [hlookup, hdefault] using
                  (lookupVariableValue?_foldl_materializeVariableDefault_of_name_not_mem
                    rest ((definition.name, defaultValue) :: variableValues)
                    definition.name hnodup.1).trans hadded
      · simp only [List.foldl_cons]
        let nextValues := materializeVariableDefault variableValues candidate
        have hne : candidate.name ≠ definition.name := by
          intro heq
          apply hnodup.1
          rw [heq]
          exact List.mem_map.mpr ⟨definition, hrest, rfl⟩
        have hnextLookup : lookupVariableValue? nextValues definition.name
            = lookupVariableValue? variableValues definition.name := by
          simp only [nextValues, materializeVariableDefault]
          split
          · rfl
          · split
            · simp [lookupVariableValue?, hne]
            · rfl
        rw [ih hnodup.2 hrest nextValues, hnextLookup]

private theorem variableValuesCoercionFuel_foldl_materializeVariableDefault
    {definitions : List VariableDefinition}
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    (values : VariableValues)
    : variableValuesCoercionFuel (definitions.foldl materializeVariableDefault values)
      = variableValuesCoercionFuel values
        + (definitions.map (variableDefaultFuelContribution values)).sum := by
  induction definitions generalizing values with
  | nil => simp
  | cons definition rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.foldl_cons]
      let nextValues := materializeVariableDefault values definition
      rw [ih hnodup.2 nextValues]
      have hcontributions :
          rest.map (variableDefaultFuelContribution nextValues)
            = rest.map (variableDefaultFuelContribution values) := by
        apply List.map_congr_left
        intro candidate hcandidate
        have hne : definition.name ≠ candidate.name := by
          intro heq
          apply hnodup.1
          exact List.mem_map.mpr ⟨candidate, hcandidate, heq.symm⟩
        simp only [nextValues, materializeVariableDefault]
        split
        · rfl
        · split
          · simp [variableDefaultFuelContribution, lookupVariableValue?, hne]
          · rfl
      rw [hcontributions]
      simp only [nextValues, materializeVariableDefault]
      split <;> rename_i hlookup
      · simp [variableDefaultFuelContribution, hlookup]
      · split <;> rename_i hdefault
        · simp [variableDefaultFuelContribution, variableValuesCoercionFuel,
            hlookup, hdefault, Nat.add_assoc, Nat.add_left_comm]
        · simp [variableDefaultFuelContribution, hlookup, hdefault]

private theorem mem_erase_of_ne_of_mem_forVariableDefinitions
    {α : Type} [BEq α] [LawfulBEq α] {a b : α} {items : List α}
    : a ≠ b -> a ∈ items -> a ∈ items.erase b := by
  intro hne hmem
  induction items with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases hhead : head = b
      · subst head
        rw [List.erase_cons_head]
        rcases List.mem_cons.mp hmem with hsame | htail
        · exact False.elim (hne hsame)
        · exact htail
      · have htailErase : ¬(head == b) = true := by
          have hbeq : (head == b) = false := (beq_eq_false_iff_ne).2 hhead
          simp [hbeq]
        rw [List.erase_cons_tail htailErase]
        rcases List.mem_cons.mp hmem with hsame | htail
        · exact List.mem_cons.mpr (Or.inl hsame)
        · exact List.mem_cons_of_mem head (ih htail)

private theorem not_mem_erase_self_forVariableDefinitions
    {α : Type} [BEq α] [LawfulBEq α] (a : α)
    : ∀ items : List α, items.Nodup -> a ∉ items.erase a
  | [], _hnodup => by simp
  | head :: tail, hnodup => by
      have hparts : head ∉ tail ∧ tail.Nodup := by simpa using hnodup
      by_cases hhead : head = a
      · subst head
        rw [List.erase_cons_head]
        exact hparts.1
      · have htailErase : ¬(head == a) = true := by
          have hbeq : (head == a) = false := (beq_eq_false_iff_ne).2 hhead
          simp [hbeq]
        rw [List.erase_cons_tail htailErase]
        intro hmem
        rcases List.mem_cons.mp hmem with hheadMem | htailMem
        · exact hhead hheadMem.symm
        · exact not_mem_erase_self_forVariableDefinitions a tail hparts.2 htailMem

private theorem listPermOfNodupSubsetSubset_forVariableDefinitions
    {α : Type} [BEq α] [LawfulBEq α] {left right : List α}
    : left.Nodup
      -> right.Nodup
      -> (∀ item, item ∈ left -> item ∈ right)
      -> (∀ item, item ∈ right -> item ∈ left)
      -> left.Perm right := by
  intro hleftNodup
  induction left generalizing right with
  | nil =>
      intro _hrightNodup _hleftSubset hrightSubset
      cases right with
      | nil => exact List.Perm.nil
      | cons head tail =>
          have hfalse : False := by
            have hmember := hrightSubset head (by simp)
            simpa using hmember
          exact hfalse.elim
  | cons head tail ih =>
      intro hrightNodup hleftSubset hrightSubset
      have hleftParts : head ∉ tail ∧ tail.Nodup := by simpa using hleftNodup
      have hheadRight : head ∈ right := hleftSubset head (by simp)
      have htailSubset : ∀ item, item ∈ tail -> item ∈ right.erase head := by
        intro item hitem
        apply mem_erase_of_ne_of_mem_forVariableDefinitions
        · intro heq
          subst item
          exact hleftParts.1 hitem
        · exact hleftSubset item (List.mem_cons_of_mem head hitem)
      have hrightEraseSubset : ∀ item, item ∈ right.erase head -> item ∈ tail := by
        intro item hitemErase
        rcases List.mem_cons.mp
            (hrightSubset item (List.mem_of_mem_erase hitemErase)) with hitemHead | hitemTail
        · subst item
          exact False.elim
            ((not_mem_erase_self_forVariableDefinitions head right hrightNodup)
              hitemErase)
        · exact hitemTail
      have htailPerm : tail.Perm (right.erase head) :=
        ih hleftParts.2 (List.Nodup.erase head hrightNodup) htailSubset
          hrightEraseSubset
      exact (List.Perm.cons head htailPerm).trans
        (List.perm_cons_erase hheadRight).symm

private theorem variableDefinitionContributionPairs_nodup
    (definitions : List VariableDefinition) (contribution : VariableDefinition -> Nat)
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    : (definitions.map
        fun definition => (definition.name, contribution definition)).Nodup := by
  induction definitions with
  | nil => simp
  | cons definition rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      constructor
      · intro hmember
        rcases List.mem_map.mp hmember with ⟨candidate, hcandidate, heq⟩
        apply hnodup.1
        exact List.mem_map.mpr ⟨candidate, hcandidate, congrArg Prod.fst heq⟩
      · exact ih hnodup.2

private theorem variableValuesCoercionFuel_eq_of_perm
    {left right : List Nat} (hperm : left.Perm right)
    : left.sum = right.sum := by
  induction hperm with
  | nil => rfl
  | cons value _hperm ih => simp [ih]
  | swap first second rest => simp [Nat.add_left_comm]
  | trans _ _ ihLeft ihRight => exact ihLeft.trans ihRight

private theorem variableDefaultFuelContribution_eq_of_equivalent
    {leftValues rightValues : VariableValues} {left right : VariableDefinition}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (hequivalent : VariableDefinition.equivalent left right)
    : variableDefaultFuelContribution leftValues left
      = variableDefaultFuelContribution rightValues right := by
  rcases left with ⟨leftName, leftType, leftDefault⟩
  rcases right with ⟨rightName, rightType, rightDefault⟩
  simp only [VariableDefinition.equivalent] at hequivalent
  rcases hequivalent with ⟨rfl, _htype, hdefault⟩
  have hlookup := hvalues.1 leftName
  cases hleftLookup : lookupVariableValue? leftValues leftName with
  | none =>
      cases hrightLookup : lookupVariableValue? rightValues leftName with
      | none =>
          cases leftDefault <;> cases rightDefault <;>
            simp [variableDefaultFuelContribution, hleftLookup, hrightLookup] at hdefault ⊢
          exact inputValueCoercionFuel_eq_of_equivalent hdefault
      | some rightValue => simp [hleftLookup, hrightLookup] at hlookup
  | some leftValue =>
      cases hrightLookup : lookupVariableValue? rightValues leftName with
      | none => simp [hleftLookup, hrightLookup] at hlookup
      | some rightValue =>
          simp [variableDefaultFuelContribution, hleftLookup, hrightLookup]

private theorem variableLookupWithDefault_equivalent
    {leftValues rightValues : VariableValues} {left right : VariableDefinition}
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (hequivalent : VariableDefinition.equivalent left right)
    : Option.Rel
        (fun leftValue rightValue =>
          InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
        (match lookupVariableValue? leftValues left.name with
          | some value => some value
          | none => left.defaultValue)
        (match lookupVariableValue? rightValues right.name with
          | some value => some value
          | none => right.defaultValue) := by
  rcases left with ⟨leftName, leftType, leftDefault⟩
  rcases right with ⟨rightName, rightType, rightDefault⟩
  simp only [VariableDefinition.equivalent] at hequivalent
  rcases hequivalent with ⟨rfl, _htype, hdefault⟩
  have hlookup := hvalues.1 leftName
  cases hleftLookup : lookupVariableValue? leftValues leftName with
  | none =>
      cases hrightLookup : lookupVariableValue? rightValues leftName with
      | none =>
          cases leftDefault <;> cases rightDefault <;>
            simp at hdefault ⊢
          exact hdefault
      | some rightValue => simp [hleftLookup, hrightLookup] at hlookup
  | some leftValue =>
      cases hrightLookup : lookupVariableValue? rightValues leftName with
      | none => simp [hleftLookup, hrightLookup] at hlookup
      | some rightValue => simpa [hleftLookup, hrightLookup] using hlookup

private theorem
    variableDefinitionsSyntacticallyEquivalent_foldl_defaults_coercionEquivalent
    {left right : List VariableDefinition} {leftValues rightValues : VariableValues}
    (hleftNodup : (left.map VariableDefinition.name).Nodup)
    (hrightNodup : (right.map VariableDefinition.name).Nodup)
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (hdefinitions : variableDefinitionsSyntacticallyEquivalent left right)
    : variableValuesCoercionEquivalent
        (left.foldl materializeVariableDefault leftValues)
        (right.foldl materializeVariableDefault rightValues) := by
  constructor
  · intro name
    by_cases hleftName : name ∈ left.map VariableDefinition.name
    · rcases List.mem_map.mp hleftName with
        ⟨leftDefinition, hleftDefinition, hleftDefinitionName⟩
      rcases hdefinitions.1 leftDefinition hleftDefinition with
        ⟨rightDefinition, hrightDefinition, hequivalent⟩
      have hrightDefinitionName : rightDefinition.name = name :=
        hequivalent.1.symm.trans hleftDefinitionName
      have hleftLookup :
          lookupVariableValue? (left.foldl materializeVariableDefault leftValues) name
            = match lookupVariableValue? leftValues name with
              | some value => some value
              | none => leftDefinition.defaultValue := by
        simpa only [hleftDefinitionName] using
          lookupVariableValue?_foldl_materializeVariableDefault_at_definition
            hleftNodup hleftDefinition leftValues
      have hrightLookup :
          lookupVariableValue? (right.foldl materializeVariableDefault rightValues) name
            = match lookupVariableValue? rightValues name with
              | some value => some value
              | none => rightDefinition.defaultValue := by
        simpa only [hrightDefinitionName] using
          lookupVariableValue?_foldl_materializeVariableDefault_at_definition
            hrightNodup hrightDefinition rightValues
      rw [hleftLookup, hrightLookup]
      simpa only [hleftDefinitionName, hrightDefinitionName] using
        variableLookupWithDefault_equivalent hvalues hequivalent
    · have hrightName : name ∉ right.map VariableDefinition.name := by
        intro hmember
        rcases List.mem_map.mp hmember with
          ⟨rightDefinition, hrightDefinition, hrightDefinitionName⟩
        rcases hdefinitions.2 rightDefinition hrightDefinition with
          ⟨leftDefinition, hleftDefinition, hequivalent⟩
        apply hleftName
        exact List.mem_map.mpr
          ⟨leftDefinition, hleftDefinition,
            hequivalent.1.trans hrightDefinitionName⟩
      rw [lookupVariableValue?_foldl_materializeVariableDefault_of_name_not_mem
          left leftValues name hleftName,
        lookupVariableValue?_foldl_materializeVariableDefault_of_name_not_mem
          right rightValues name hrightName]
      exact hvalues.1 name
  · rw [variableValuesCoercionFuel_foldl_materializeVariableDefault hleftNodup,
      variableValuesCoercionFuel_foldl_materializeVariableDefault hrightNodup,
      hvalues.2]
    let leftPairs := left.map
      (fun definition =>
        (definition.name, variableDefaultFuelContribution leftValues definition))
    let rightPairs := right.map
      (fun definition =>
        (definition.name, variableDefaultFuelContribution rightValues definition))
    have hleftPairsNodup : leftPairs.Nodup :=
      variableDefinitionContributionPairs_nodup left
        (variableDefaultFuelContribution leftValues) hleftNodup
    have hrightPairsNodup : rightPairs.Nodup :=
      variableDefinitionContributionPairs_nodup right
        (variableDefaultFuelContribution rightValues) hrightNodup
    have hleftSubset : ∀ pair, pair ∈ leftPairs -> pair ∈ rightPairs := by
      intro pair hpair
      rcases List.mem_map.mp hpair with ⟨definition, hdefinition, rfl⟩
      rcases hdefinitions.1 definition hdefinition with
        ⟨definition', hdefinition', hequivalent⟩
      apply List.mem_map.mpr
      refine ⟨definition', hdefinition', ?_⟩
      apply Prod.ext
      · exact hequivalent.1.symm
      · exact (variableDefaultFuelContribution_eq_of_equivalent hvalues
          hequivalent).symm
    have hrightSubset : ∀ pair, pair ∈ rightPairs -> pair ∈ leftPairs := by
      intro pair hpair
      rcases List.mem_map.mp hpair with ⟨definition, hdefinition, rfl⟩
      rcases hdefinitions.2 definition hdefinition with
        ⟨definition', hdefinition', hequivalent⟩
      apply List.mem_map.mpr
      refine ⟨definition', hdefinition', ?_⟩
      apply Prod.ext
      · exact hequivalent.1
      · exact variableDefaultFuelContribution_eq_of_equivalent hvalues hequivalent
    have hpairs : leftPairs.Perm rightPairs :=
      listPermOfNodupSubsetSubset_forVariableDefinitions hleftPairsNodup
        hrightPairsNodup hleftSubset hrightSubset
    have hcontributions :
        (left.map (variableDefaultFuelContribution leftValues)).Perm
          (right.map (variableDefaultFuelContribution rightValues)) := by
      change (left.map
                (Prod.snd
                  ∘ fun definition =>
                      (
                        definition.name,
                        variableDefaultFuelContribution leftValues definition
                      ))).Perm
              (right.map
                (Prod.snd
                  ∘ fun definition =>
                      (
                        definition.name,
                        variableDefaultFuelContribution rightValues definition
                      )))
      simpa only [leftPairs, rightPairs, List.map_map] using hpairs.map Prod.snd
    exact congrArg (variableValuesCoercionFuel rightValues + ·)
      (variableValuesCoercionFuel_eq_of_perm hcontributions)

theorem
    coerceVariableValues_coercionEquivalent_of_variableDefinitionsSyntacticallyEquivalent
    {left right : Operation} {leftValues rightValues : VariableValues}
    (hleftNodup : (left.variableDefinitions.map VariableDefinition.name).Nodup)
    (hrightNodup : (right.variableDefinitions.map VariableDefinition.name).Nodup)
    (hvalues : variableValuesCoercionEquivalent leftValues rightValues)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
          right.variableDefinitions)
    : variableValuesCoercionEquivalent
        (coerceVariableValues left leftValues)
        (coerceVariableValues right rightValues) := by
  exact variableDefinitionsSyntacticallyEquivalent_foldl_defaults_coercionEquivalent
    hleftNodup hrightNodup hvalues hdefinitions

-- Proof-facing wrapper for statements that reason about field-argument coercion and
-- resolver dispatch as one step. Spec-facing executors keep the two steps explicit.
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

@[simp]
theorem coerceAndResolveFieldValue_eq_none_of_error
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fieldDefinition : FieldDefinition)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : ResolverValue ObjectRef)
    (hcoerce
      : coerceArgumentValues schema variableValues fieldDefinition.arguments arguments
        = .error)
    : coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
        parentType fieldName arguments source
      = none := by
  simp [coerceAndResolveFieldValue, hcoerce]

@[simp]
theorem coerceAndResolveFieldValue_eq_of_success
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fieldDefinition : FieldDefinition)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : ResolverValue ObjectRef) (coercedArguments : CoercedArguments)
    (hcoerce
      : coerceArgumentValues schema variableValues fieldDefinition.arguments arguments
        = .success coercedArguments)
    : coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
        parentType fieldName arguments source
      = resolveFieldValue resolvers parentType fieldName coercedArguments source := by
  simp [coerceAndResolveFieldValue, hcoerce]

theorem coerceAndResolveFieldValue_eq_some_iff
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fieldDefinition : FieldDefinition)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : ResolverValue ObjectRef) (resolved : ResolverValue ObjectRef)
    : coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
          parentType fieldName arguments source
        = some resolved
      ↔ ∃ coercedArguments,
          coerceArgumentValues schema variableValues fieldDefinition.arguments arguments
            = .success coercedArguments
          ∧ resolveFieldValue resolvers parentType fieldName coercedArguments source
            = some resolved := by
  unfold coerceAndResolveFieldValue
  cases hcoerce
        : coerceArgumentValues schema variableValues fieldDefinition.arguments
            arguments with
  | error => simp
  | success coercedArguments =>
      refine ⟨fun hresolve => ⟨coercedArguments, rfl, hresolve⟩, ?_⟩
      rintro ⟨candidate, hcandidate, hresolve⟩
      injection hcandidate with hcandidate
      subst candidate
      exact hresolve

@[simp]
theorem match_coerceArgumentValues_resolveFieldValue
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fieldDefinition : FieldDefinition)
    (parentType fieldName : Name) (arguments : List Argument)
    (source : ResolverValue ObjectRef) (onFailure : α)
    (onSuccess : ResolverValue ObjectRef -> α)
    : (match coerceArgumentValues schema variableValues fieldDefinition.arguments
              arguments with
        | .error => onFailure
        | .success coercedArguments =>
            match resolveFieldValue resolvers parentType fieldName coercedArguments
                    source with
            | none => onFailure
            | some resolved => onSuccess resolved)
      = match coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
                parentType fieldName arguments source with
        | none => onFailure
        | some resolved => onSuccess resolved := by
  unfold coerceAndResolveFieldValue
  cases hcoerce
        : coerceArgumentValues schema variableValues
            fieldDefinition.arguments arguments with
  | error => rfl
  | success coercedArguments =>
      cases resolveFieldValue resolvers parentType fieldName coercedArguments source <;>
        rfl

@[simp]
theorem executeField_succ_eq_coerceAndResolveFieldValue
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef) (responseName : Name)
    (field : ExecutableField) (fields : List ExecutableField)
    (fieldDefinition : FieldDefinition)
    (hlookup : schema.lookupField field.parentType field.fieldName = some fieldDefinition)
    : executeField schema resolvers variableValues (fuel + 1) source responseName
        (field :: fields)
      = match coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
                field.parentType field.fieldName field.arguments source with
        | none =>
            singleFieldResult responseName (handleFieldError fieldDefinition.outputType)
        | some resolved =>
            singleFieldResult responseName
              (completeValue schema resolvers variableValues fuel
                fieldDefinition.outputType (field :: fields) resolved) := by
  simp only [executeField, hlookup]
  exact match_coerceArgumentValues_resolveFieldValue schema resolvers variableValues
    fieldDefinition field.parentType field.fieldName field.arguments source
    (singleFieldResult responseName (handleFieldError fieldDefinition.outputType))
    (fun resolved =>
      singleFieldResult responseName
        (completeValue schema resolvers variableValues fuel fieldDefinition.outputType
          (field :: fields) resolved))

-- Proof-facing name-based resolution for statements that intentionally quantify over
-- arbitrary field names without carrying a successful schema lookup witness. Runtime
-- executors coerce arguments after lookup and pass them to `resolveFieldValue`.
def resolveFieldValueByName (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (parentType fieldName : Name)
    (arguments : List Argument) (source : ResolverValue ObjectRef)
    : Option (ResolverValue ObjectRef) :=
  match schema.lookupField parentType fieldName with
  | none => none
  | some fieldDefinition =>
      coerceAndResolveFieldValue schema resolvers variableValues fieldDefinition
        parentType fieldName arguments source

-- Proof-facing field lookup wrapper used by resolver probes. Runtime execution calls
-- `coerceArgumentValues` directly after the same lookup.
def coercedArgumentsForField (schema : Schema) (variableValues : VariableValues)
    (parentType fieldName : Name) (arguments : List Argument)
    : CoercedArguments :=
  match schema.lookupField parentType fieldName with
  | none => []
  | some fieldDefinition =>
      match coerceArgumentValues schema variableValues fieldDefinition.arguments
              arguments with
      | .success coercedArguments => coercedArguments
      | .error => []

theorem coercedArgumentsForField_eq_of_success
    (schema : Schema) (variableValues : VariableValues)
    (parentType fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) (coercedArguments : CoercedArguments)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hcoercion
      : coerceArgumentValues schema variableValues fieldDefinition.arguments arguments
        = .success coercedArguments)
    : coercedArgumentsForField schema variableValues parentType fieldName arguments
      = coercedArguments := by
  simp [coercedArgumentsForField, hlookup, hcoercion]

theorem coerceArgumentValues_equivalent_success_of_coercedArgumentsForField
    (schema : Schema) (variableValues : VariableValues)
    (parentType fieldName : Name) (arguments : List Argument)
    (fieldDefinition : FieldDefinition) (targetArguments : CoercedArguments)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hsuccess
      : (coerceArgumentValues schema variableValues fieldDefinition.arguments
          arguments).isSuccess
        = true)
    (harguments
      : CoercedArgument.argumentsEquivalent
          (coercedArgumentsForField schema variableValues parentType fieldName arguments)
          targetArguments)
    : ArgumentCoercionResult.equivalent
        (coerceArgumentValues schema variableValues fieldDefinition.arguments arguments)
        (.success targetArguments) := by
  cases hcoercion
        : coerceArgumentValues schema variableValues fieldDefinition.arguments
            arguments with
  | error => simp [hcoercion] at hsuccess
  | success coercedArguments =>
      simpa [ArgumentCoercionResult.equivalent, hcoercion,
        coercedArgumentsForField, hlookup] using harguments

-- Two variable environments are indistinguishable at the resolver boundary when every
-- field-argument definition and syntax pair produces equivalent coercion results.
def argumentCoercionEquivalent (schema : Schema) (leftValues rightValues : VariableValues)
    : Prop :=
  ∀ definitions arguments,
    ArgumentCoercionResult.equivalent
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
    ArgumentCoercionResult.equivalent
      (coerceArgumentValues schema [] definitions leftArguments)
      (coerceArgumentValues schema [] definitions rightArguments)
    -> Argument.argumentsEquivalent leftArguments rightArguments

end Execution

end GraphQL
