import Proofs.GraphQL.Validation.FieldMerge

/-! Variable-collector facts used by validation-preservation proofs. -/

namespace GraphQL

namespace Validation

theorem inputObjectFieldsVariables_insertObjectFieldSorted_mem_iff
    (variableName : Name) (field : Name × InputValue)
    : ∀ fields,
        variableName
          ∈ inputObjectFieldsVariables (InputValue.insertObjectFieldSorted field fields)
        ↔ variableName ∈ inputValueVariables field.2
          ∨ variableName ∈ inputObjectFieldsVariables fields
    | [] => by
        simp [InputValue.insertObjectFieldSorted, inputObjectFieldsVariables]
    | candidate :: rest => by
      rw [InputValue.insertObjectFieldSorted]
      split
      · simp [inputObjectFieldsVariables]
      · simp only [inputObjectFieldsVariables, List.mem_append]
        rw [inputObjectFieldsVariables_insertObjectFieldSorted_mem_iff]
        constructor
        · rintro (hcandidate | hfield | hrest)
          · exact Or.inr (Or.inl hcandidate)
          · exact Or.inl hfield
          · exact Or.inr (Or.inr hrest)
        · rintro (hfield | hcandidate | hrest)
          · exact Or.inr (Or.inl hfield)
          · exact Or.inl hcandidate
          · exact Or.inr (Or.inr hrest)

theorem inputObjectFieldsVariables_sortObjectFieldsByName_mem_iff (variableName : Name)
    : ∀ fields,
        variableName
          ∈ inputObjectFieldsVariables (InputValue.sortObjectFieldsByName fields)
        ↔ variableName ∈ inputObjectFieldsVariables fields
    | [] => by
        simp [InputValue.sortObjectFieldsByName, inputObjectFieldsVariables]
    | field :: rest => by
      simp only [InputValue.sortObjectFieldsByName]
      rw [inputObjectFieldsVariables_insertObjectFieldSorted_mem_iff,
        inputObjectFieldsVariables_sortObjectFieldsByName_mem_iff]
      simp [inputObjectFieldsVariables]

mutual
  theorem inputValueVariables_canonical_mem_iff (variableName : Name)
      : ∀ value,
          variableName ∈ inputValueVariables value.canonical
          ↔ variableName ∈ inputValueVariables value
    | .null => by simp [InputValue.canonical, inputValueVariables]
    | .int value => by simp [InputValue.canonical, inputValueVariables]
    | .float value => by simp [InputValue.canonical, inputValueVariables]
    | .string value => by simp [InputValue.canonical, inputValueVariables]
    | .boolean value => by simp [InputValue.canonical, inputValueVariables]
    | .enum value => by simp [InputValue.canonical, inputValueVariables]
    | .variable name => by simp [InputValue.canonical, inputValueVariables]
    | .list values => by
        simp only [InputValue.canonical, inputValueVariables]
        exact inputValuesVariables_canonical_mem_iff variableName values
    | .object fields => by
        simp only [InputValue.canonical, inputValueVariables]
        rw [inputObjectFieldsVariables_sortObjectFieldsByName_mem_iff]
        exact inputObjectFieldsVariables_canonical_mem_iff variableName fields

  theorem inputValuesVariables_canonical_mem_iff (variableName : Name)
      : ∀ values,
          variableName ∈ inputValuesVariables (InputValue.canonicalValues values)
          ↔ variableName ∈ inputValuesVariables values
    | [] => by simp [InputValue.canonicalValues, inputValuesVariables]
    | value :: rest => by
        simp only [InputValue.canonicalValues, inputValuesVariables,
          List.mem_append]
        rw [inputValueVariables_canonical_mem_iff,
          inputValuesVariables_canonical_mem_iff]

  theorem inputObjectFieldsVariables_canonical_mem_iff (variableName : Name)
      : ∀ fields,
          variableName
            ∈ inputObjectFieldsVariables (InputValue.canonicalObjectFields fields)
          ↔ variableName ∈ inputObjectFieldsVariables fields
    | [] => by
        simp [InputValue.canonicalObjectFields, inputObjectFieldsVariables]
    | (name, value) :: rest => by
        simp only [InputValue.canonicalObjectFields,
          inputObjectFieldsVariables, List.mem_append]
        rw [inputValueVariables_canonical_mem_iff,
          inputObjectFieldsVariables_canonical_mem_iff]
end

mutual
  theorem inputValueVariables_mem_iff_of_structuralEquivalent (variableName : Name)
      : ∀ left right,
          InputValue.structuralEquivalent left right
          -> (variableName ∈ inputValueVariables left
              ↔ variableName ∈ inputValueVariables right)
    | .null, .null, _ => by simp [inputValueVariables]
    | .int left, .int right, _ => by simp [inputValueVariables]
    | .float left, .float right, _ => by simp [inputValueVariables]
    | .string left, .string right, _ => by simp [inputValueVariables]
    | .boolean left, .boolean right, _ => by simp [inputValueVariables]
    | .enum left, .enum right, _ => by simp [inputValueVariables]
    | .variable left, .variable right, hequivalent => by
        simp [InputValue.structuralEquivalent] at hequivalent
        simp [inputValueVariables, hequivalent]
    | .list left, .list right, hequivalent => by
        simp only [inputValueVariables]
        exact inputValuesVariables_mem_iff_of_structuralEquivalent
          variableName left right hequivalent
    | .object left, .object right, hequivalent => by
        simp only [inputValueVariables]
        exact inputObjectFieldsVariables_mem_iff_of_structuralEquivalent
          variableName left right hequivalent
    | .null, .int _, hequivalent
    | .null, .float _, hequivalent
    | .null, .string _, hequivalent
    | .null, .boolean _, hequivalent
    | .null, .enum _, hequivalent
    | .null, .list _, hequivalent
    | .null, .object _, hequivalent
    | .null, .variable _, hequivalent
    | .int _, .null, hequivalent
    | .int _, .float _, hequivalent
    | .int _, .string _, hequivalent
    | .int _, .boolean _, hequivalent
    | .int _, .enum _, hequivalent
    | .int _, .list _, hequivalent
    | .int _, .object _, hequivalent
    | .int _, .variable _, hequivalent
    | .float _, .null, hequivalent
    | .float _, .int _, hequivalent
    | .float _, .string _, hequivalent
    | .float _, .boolean _, hequivalent
    | .float _, .enum _, hequivalent
    | .float _, .list _, hequivalent
    | .float _, .object _, hequivalent
    | .float _, .variable _, hequivalent
    | .string _, .null, hequivalent
    | .string _, .int _, hequivalent
    | .string _, .float _, hequivalent
    | .string _, .boolean _, hequivalent
    | .string _, .enum _, hequivalent
    | .string _, .list _, hequivalent
    | .string _, .object _, hequivalent
    | .string _, .variable _, hequivalent
    | .boolean _, .null, hequivalent
    | .boolean _, .int _, hequivalent
    | .boolean _, .float _, hequivalent
    | .boolean _, .string _, hequivalent
    | .boolean _, .enum _, hequivalent
    | .boolean _, .list _, hequivalent
    | .boolean _, .object _, hequivalent
    | .boolean _, .variable _, hequivalent
    | .enum _, .null, hequivalent
    | .enum _, .int _, hequivalent
    | .enum _, .float _, hequivalent
    | .enum _, .string _, hequivalent
    | .enum _, .boolean _, hequivalent
    | .enum _, .list _, hequivalent
    | .enum _, .object _, hequivalent
    | .enum _, .variable _, hequivalent
    | .list _, .null, hequivalent
    | .list _, .int _, hequivalent
    | .list _, .float _, hequivalent
    | .list _, .string _, hequivalent
    | .list _, .boolean _, hequivalent
    | .list _, .enum _, hequivalent
    | .list _, .object _, hequivalent
    | .list _, .variable _, hequivalent
    | .object _, .null, hequivalent
    | .object _, .int _, hequivalent
    | .object _, .float _, hequivalent
    | .object _, .string _, hequivalent
    | .object _, .boolean _, hequivalent
    | .object _, .enum _, hequivalent
    | .object _, .list _, hequivalent
    | .object _, .variable _, hequivalent
    | .variable _, .null, hequivalent
    | .variable _, .int _, hequivalent
    | .variable _, .float _, hequivalent
    | .variable _, .string _, hequivalent
    | .variable _, .boolean _, hequivalent
    | .variable _, .enum _, hequivalent
    | .variable _, .list _, hequivalent
    | .variable _, .object _, hequivalent => by
        simp [InputValue.structuralEquivalent] at hequivalent

  theorem inputValuesVariables_mem_iff_of_structuralEquivalent (variableName : Name)
      : ∀ left right,
          InputValue.structuralValuesEquivalent left right
          -> (variableName ∈ inputValuesVariables left
              ↔ variableName ∈ inputValuesVariables right)
    | [], [], _ => by simp [inputValuesVariables]
    | left :: lefts, right :: rights, hequivalent => by
        simp [InputValue.structuralValuesEquivalent] at hequivalent
        simp only [inputValuesVariables, List.mem_append]
        rw [inputValueVariables_mem_iff_of_structuralEquivalent
            variableName left right hequivalent.1,
          inputValuesVariables_mem_iff_of_structuralEquivalent
            variableName lefts rights hequivalent.2]
    | [], _ :: _, hequivalent
    | _ :: _, [], hequivalent => by
        simp [InputValue.structuralValuesEquivalent] at hequivalent

  theorem inputObjectFieldsVariables_mem_iff_of_structuralEquivalent (variableName : Name)
      : ∀ left right,
          InputValue.structuralObjectFieldsEquivalent left right
          -> (variableName ∈ inputObjectFieldsVariables left
              ↔ variableName ∈ inputObjectFieldsVariables right)
    | [], [], _ => by simp [inputObjectFieldsVariables]
    | (leftName, leftValue) :: lefts,
      (rightName, rightValue) :: rights, hequivalent => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hequivalent
        simp only [inputObjectFieldsVariables, List.mem_append]
        rw [inputValueVariables_mem_iff_of_structuralEquivalent
            variableName leftValue rightValue hequivalent.2.1,
          inputObjectFieldsVariables_mem_iff_of_structuralEquivalent
            variableName lefts rights hequivalent.2.2]
    | [], _ :: _, hequivalent
    | _ :: _, [], hequivalent => by
        simp [InputValue.structuralObjectFieldsEquivalent] at hequivalent
end

theorem inputValueVariables_mem_iff_of_equivalent
    {left right : InputValue} (variableName : Name)
    (hequivalent : left.equivalent right)
    : variableName ∈ inputValueVariables left
      ↔ variableName ∈ inputValueVariables right := by
  rw [← inputValueVariables_canonical_mem_iff variableName left,
    ← inputValueVariables_canonical_mem_iff variableName right]
  exact inputValueVariables_mem_iff_of_structuralEquivalent
    variableName left.canonical right.canonical hequivalent

theorem argumentVariables_mem_iff_of_equivalent
    {left right : Argument} (variableName : Name)
    (hequivalent : left.equivalent right)
    : variableName ∈ argumentVariables left ↔ variableName ∈ argumentVariables right := by
  exact inputValueVariables_mem_iff_of_equivalent variableName hequivalent.2

theorem argumentsVariables_mem_iff (variableName : Name)
    : ∀ arguments,
        variableName ∈ argumentsVariables arguments
        ↔ ∃ argument, argument ∈ arguments ∧ variableName ∈ argumentVariables argument
  | [] => by
      simp [argumentsVariables]
  | argument :: rest => by
      simp only [argumentsVariables, List.mem_append,
        argumentsVariables_mem_iff]
      constructor
      · rintro (hargument | ⟨candidate, hcandidate, hvariable⟩)
        · exact ⟨argument, by simp, hargument⟩
        · exact ⟨candidate, by simp [hcandidate], hvariable⟩
      · rintro ⟨candidate, hcandidate, hvariable⟩
        rcases List.mem_cons.mp hcandidate with heq | hrest
        · subst candidate
          exact Or.inl hvariable
        · exact Or.inr ⟨candidate, hrest, hvariable⟩

theorem argumentsVariables_mem_iff_of_equivalent
    {left right : List Argument} (variableName : Name)
    (hequivalent : Argument.argumentsEquivalent left right)
    : variableName ∈ argumentsVariables left
      ↔ variableName ∈ argumentsVariables right := by
  constructor
  · intro hvariable
    rcases (argumentsVariables_mem_iff variableName left).1 hvariable with
      ⟨argument, hargument, hargumentVariable⟩
    rcases hequivalent.1 argument hargument with
      ⟨argument', hargument', hargumentEquivalent⟩
    exact (argumentsVariables_mem_iff variableName right).2
      ⟨argument', hargument',
        (argumentVariables_mem_iff_of_equivalent variableName
          hargumentEquivalent).1 hargumentVariable⟩
  · intro hvariable
    rcases (argumentsVariables_mem_iff variableName right).1 hvariable with
      ⟨argument, hargument, hargumentVariable⟩
    rcases hequivalent.2 argument hargument with
      ⟨argument', hargument', hargumentEquivalent⟩
    exact (argumentsVariables_mem_iff variableName left).2
      ⟨argument', hargument',
        (argumentVariables_mem_iff_of_equivalent variableName
          hargumentEquivalent).2 hargumentVariable⟩

end Validation

end GraphQL
