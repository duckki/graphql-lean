import GraphQL.Theories.ResponseShape.Footprint

/-! Basic inversion and environment facts for operation footprints. -/

namespace GraphQL

namespace ResponseShape

/-- A duplicate-free assignment maps each contained bit to its Boolean input value. -/
theorem lookupVariableValue?_boolCaseVariableValues_of_mem
    {assignment : NormalForm.BoolCase}
    {varName : NormalForm.BoolVar} {value : Bool}
    (hnodup : (assignment.map Prod.fst).Nodup)
    (hmem : (varName, value) ∈ assignment) :
    Execution.lookupVariableValue?
        (NormalForm.boolCaseVariableValues assignment) varName =
      some (.boolean value) := by
  induction assignment with
  | nil => simp at hmem
  | cons head rest ih =>
      rcases head with ⟨headVariable, headValue⟩
      have hparts := List.nodup_cons.mp hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | hrest
      · cases hhead
        simp [NormalForm.boolCaseVariableValues, Execution.lookupVariableValue?]
      · have hvariableMem : varName ∈ rest.map Prod.fst :=
          List.mem_map.mpr ⟨(varName, value), hrest, rfl⟩
        have hne : headVariable ≠ varName := by
          intro heq
          subst headVariable
          exact hparts.1 hvariableMem
        simpa [NormalForm.boolCaseVariableValues,
          Execution.lookupVariableValue?, hne]
          using ih hparts.2 hrest

/-- Boolean directive lookup reads the bit represented by an assignment pair. -/
theorem inputValueBoolean?_boolCaseVariableValues_of_mem
    {assignment : NormalForm.BoolCase}
    {varName : NormalForm.BoolVar} {value : Bool}
    (hnodup : (assignment.map Prod.fst).Nodup)
    (hmem : (varName, value) ∈ assignment) :
    Execution.inputValueBoolean?
        (NormalForm.boolCaseVariableValues assignment) (.variable varName) =
      some value := by
  simp [Execution.inputValueBoolean?,
    lookupVariableValue?_boolCaseVariableValues_of_mem hnodup hmem,
    InputValue.staticBoolean?]

/-- Empty paths are absent from every collected-field footprint. -/
@[simp] theorem collectedFieldsSelectPath_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (groupedFields : List (Name × List Execution.ExecutableField)) :
    collectedFieldsSelectPath
        schema variableValues groupedFields []
      ↔ False := by
  rfl

/-- Inversion for a one-step collected-field footprint. -/
theorem collectedFieldsSelectPath_singleton
    (schema : Schema) (variableValues : Execution.VariableValues)
    (groupedFields : List (Name × List Execution.ExecutableField))
    (step : PathStep) :
    collectedFieldsSelectPath
        schema variableValues groupedFields [step]
      ↔
      ∃ fields,
        (step.responseName, fields) ∈ groupedFields
        ∧ ∃ field,
          field ∈ fields
          ∧ executableFieldMatchesPathStep schema field step := by
  rfl

/-- Inversion for a path with a current step and a nonempty child path. -/
theorem collectedFieldsSelectPath_cons_cons
    (schema : Schema) (variableValues : Execution.VariableValues)
    (groupedFields : List (Name × List Execution.ExecutableField))
    (step next : PathStep) (rest : List PathStep) :
    collectedFieldsSelectPath
        schema variableValues groupedFields (step :: next :: rest)
      ↔
      ∃ fields,
        (step.responseName, fields) ∈ groupedFields
        ∧ (∃ field,
          field ∈ fields
          ∧ executableFieldMatchesPathStep schema field step)
        ∧ schema.typeIncludesObject
          step.field.outputType.namedType next.parentObject
        ∧ collectedFieldsSelectPath
          schema variableValues
          (Execution.collectSubfields
            schema variableValues next.parentObject
            (.object next.parentObject ()) fields)
          (next :: rest) := by
  rfl

/-- Empty paths are absent from every operation footprint. -/
@[simp] theorem operationSelectsPath_nil
    (schema : Schema) (operation : Operation)
    (assignment : NormalForm.BoolCase) :
    operationSelectsPath schema operation assignment [] ↔ False := by
  rfl

/-- Inversion of operation selection at the first concrete path step. -/
theorem operationSelectsPath_cons_iff
    (schema : Schema) (operation : Operation)
    (assignment : NormalForm.BoolCase)
    (step : PathStep) (rest : List PathStep) :
    operationSelectsPath schema operation assignment (step :: rest)
      ↔
      schema.typeIncludesObject
          (operation.rootType schema) step.parentObject
      ∧ collectedFieldsSelectPath
          schema (NormalForm.boolCaseVariableValues assignment)
          (Execution.collectFields
            schema (NormalForm.boolCaseVariableValues assignment)
              (operation.rootType schema)
            (.object step.parentObject ()) operation.selectionSet)
          (step :: rest) := by
  rfl

/-- Adding outer collected groups cannot remove an already selected path. -/
theorem collectedFieldsSelectPath_mono_outerGroups
    (schema : Schema) (variableValues : Execution.VariableValues)
    (groupedFields largerGroupedFields :
      List (Name × List Execution.ExecutableField))
    (path : List PathStep)
    (hgroups : ∀ group, group ∈ groupedFields -> group ∈ largerGroupedFields)
    (hpath : collectedFieldsSelectPath
      schema variableValues groupedFields path) :
    collectedFieldsSelectPath
      schema variableValues largerGroupedFields path := by
  cases path with
  | nil =>
      exact False.elim hpath
  | cons step rest =>
      cases rest with
      | nil =>
          rw [collectedFieldsSelectPath_singleton] at hpath ⊢
          rcases hpath with ⟨fields, hfields, hmatch⟩
          exact ⟨fields, hgroups _ hfields, hmatch⟩
      | cons next rest =>
          rw [collectedFieldsSelectPath_cons_cons] at hpath ⊢
          rcases hpath with ⟨fields, hfields, hmatch, hincludes, hrest⟩
          exact ⟨fields, hgroups _ hfields, hmatch, hincludes, hrest⟩

end ResponseShape

end GraphQL
