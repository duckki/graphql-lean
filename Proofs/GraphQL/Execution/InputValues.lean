import Proofs.GraphQL.SchemaWellFormedness.InputInhabited
import Proofs.GraphQL.Validation.InputCompatibility
import GraphQL.Theories.ExecutionReadiness

/-! Fully supplied, non-null variable environments for coercibility witnesses. -/

namespace GraphQL.Execution

-- A proof witness for satisfiability: explicitly supply every defined variable with
-- a non-null value, so operation defaults and nullable-variable exceptions cannot
-- introduce null at a required argument location.
def variablesHaveNonNullValues (schema : Schema)
    (definitions : List VariableDefinition) (values : VariableValues)
    : Prop :=
  ∀ definition,
    definition ∈ definitions
    -> ∃ value,
        lookupVariableValue? values definition.name = some value
        ∧ value ≠ .null
        ∧ Schema.ConstInputValueIsCorrectType schema value definition.typeRef

private theorem lookupVariableValue_map {definitions : List VariableDefinition}
    (values : VariableDefinition -> ConstInputValue)
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    {definition : VariableDefinition} (hmem : definition ∈ definitions)
    : lookupVariableValue? (definitions.map fun d => (d.name, values d)) definition.name
      = some (values definition) := by
  induction definitions with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [lookupVariableValue?]
      · have hne : head.name ≠ definition.name := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map.mpr ⟨definition, hmem, rfl⟩)
        simp [lookupVariableValue?, hne, ih hnodup.2 hmem]

theorem exists_variablesHaveNonNullValues
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {definitions : List VariableDefinition}
    (hvalid : Validation.variableDefinitionsValid schema definitions)
    : ∃ values, variablesHaveNonNullValues schema definitions values := by
  classical
  have hinhabited (definition : VariableDefinition) (hmem : definition ∈ definitions) :
      ∃ value : ConstInputValue, value ≠ .null
        ∧ Schema.ConstInputValueIsCorrectType schema value definition.typeRef := by
    obtain ⟨value, hnonnull, hcorrect⟩ :=
      SchemaWellFormedness.schemaWellFormed_inputTypeInhabited_nonNull
        hschema definition.typeRef (hvalid.2 definition hmem).1
    refine ⟨value, ?_, hcorrect⟩
    intro heq
    subst value
    exact hnonnull
  let values := fun definition =>
    if hmem : definition ∈ definitions then Classical.choose (hinhabited definition hmem)
    else .null
  refine ⟨definitions.map (fun d => (d.name, values d)), ?_⟩
  intro definition hmem
  refine ⟨values definition, lookupVariableValue_map values hvalid.1 hmem, ?_⟩
  simpa [values, hmem] using Classical.choose_spec (hinhabited definition hmem)

-- Repeated names are allowed when their declared types agree, so two operations'
-- definition lists can share one fully supplied environment.
theorem exists_variablesHaveNonNullValues_of_consistentTypes
    {schema : Schema} (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {definitions : List VariableDefinition}
    (hinput
      : ∀ definition, definition ∈ definitions -> definition.typeRef.isInputType schema)
    (hconsistent
      : ∀ first,
          first ∈ definitions
          -> ∀ second,
              second ∈ definitions
              -> first.name = second.name
              -> first.typeRef = second.typeRef)
    : ∃ values, variablesHaveNonNullValues schema definitions values := by
  induction definitions with
  | nil => exact ⟨[], by intro definition hmem; cases hmem⟩
  | cons head rest ih =>
      obtain ⟨values, hvalues⟩ := ih
        (fun definition hmem => hinput definition (List.mem_cons_of_mem _ hmem))
        (fun first hfirst second hsecond => hconsistent first (List.mem_cons_of_mem _ hfirst)
          second (List.mem_cons_of_mem _ hsecond))
      obtain ⟨value, hnonnull, htyped⟩ :=
        SchemaWellFormedness.schemaWellFormed_inputTypeInhabited_nonNull hschema head.typeRef
          (hinput head List.mem_cons_self)
      have hnotNull : value ≠ .null := by intro heq; subst value; exact hnonnull
      refine ⟨(head.name, value) :: values, ?_⟩
      intro definition hmem
      by_cases hname : head.name = definition.name
      · refine ⟨value, by simp [lookupVariableValue?, hname], hnotNull, ?_⟩
        exact (hconsistent head List.mem_cons_self definition hmem hname) ▸ htyped
      · have hrest : definition ∈ rest := by
          rcases List.mem_cons.mp hmem with rfl | hmem
          · exact False.elim (hname rfl)
          · exact hmem
        obtain ⟨value, hlookup, hnonnull, htyped⟩ := hvalues definition hrest
        exact ⟨
          value,
          by simpa [lookupVariableValue?, hname] using hlookup,
          hnonnull,
          htyped
        ⟩

theorem variablesHaveNonNullValues_of_equivalent
    {schema : Schema} {left right : List VariableDefinition} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema left values)
    (hequivalent : variableDefinitionsSyntacticallyEquivalent left right)
    : variablesHaveNonNullValues schema right values := by
  intro definition hmem
  obtain ⟨other, hother, heq⟩ := hequivalent.2 definition hmem
  obtain ⟨value, hlookup, hnonnull, hcorrect⟩ := hvalues other hother
  exact ⟨value, heq.1 ▸ hlookup, hnonnull, heq.2.1 ▸ hcorrect⟩

theorem variablesHaveNonNullValues_boolCase
    {schema : Schema} {definitions : List VariableDefinition} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema definitions values)
    (boolCase : BoolCase)
    (hboolean
      : ∀ name bit,
          (name, bit) ∈ boolCase
          -> ∀ definition,
              definition ∈ definitions
              -> definition.name = name
              -> definition.typeRef = .named "Boolean"
                  ∨ definition.typeRef = .nonNull (.named "Boolean"))
    : variablesHaveNonNullValues schema definitions
        (boolCaseVariableValues boolCase values) := by
  induction boolCase with
  | nil => exact hvalues
  | cons head rest ih =>
      have hrest :=
        ih (fun name bit hmem => hboolean name bit (List.mem_cons_of_mem _ hmem))
      intro definition hmem
      by_cases hname : definition.name = head.1
      · have htype := hboolean head.1 head.2 (by simp) definition hmem hname
        have hboolInput : (TypeRef.named "Boolean").isInputType schema :=
          ⟨.builtinScalar .boolean, by rfl, trivial⟩
        have hbool : Schema.ConstInputValueIsCorrectType schema (.boolean head.2)
            (.named "Boolean") :=
          .namedNonInputObject _ _ hboolInput (by simp) (by simp) (by rfl)
        refine ⟨.boolean head.2, ?_, by simp, ?_⟩
        · simp [boolCaseVariableValues, lookupVariableValue?, hname]
        · rcases htype with htype | htype
          · exact htype ▸ hbool
          · rw [htype]
            exact .nonNull _ _ hboolInput (by simp) hbool
      · obtain ⟨value, hlookup, hnonnull, hcorrect⟩ := hrest definition hmem
        refine ⟨value, ?_, hnonnull, hcorrect⟩
        simpa [boolCaseVariableValues, lookupVariableValue?, Ne.symm hname] using hlookup

theorem coerceVariableValues_eq_of_variablesHaveNonNullValues
    {schema : Schema} {operation : Operation} {values : VariableValues}
    (hvalues : variablesHaveNonNullValues schema operation.variableDefinitions values)
    : coerceVariableValues operation values = values := by
  unfold coerceVariableValues
  generalize hdefinitions : operation.variableDefinitions = definitions at hvalues ⊢
  clear hdefinitions
  induction definitions with
  | nil => rfl
  | cons head rest ih =>
      obtain ⟨value, hlookup, _⟩ := hvalues head (by simp)
      simp only [List.foldl_cons, hlookup]
      apply ih
      intro definition hmem
      exact hvalues definition (List.mem_cons_of_mem _ hmem)

end GraphQL.Execution
