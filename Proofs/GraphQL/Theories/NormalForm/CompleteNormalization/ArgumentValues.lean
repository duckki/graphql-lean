import Proofs.GraphQL.Execution.InputValues
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Directives
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases

/-! Shared typed variable witnesses for every complete Boolean case.

This establishes variable-value satisfiability. `ArgumentCoercibility.lean` combines it
with validity-to-coercion to discharge the joint Boolean-case readiness premise.
-/

namespace GraphQL.NormalForm.CompleteNormalization

private theorem variableUsageAllowed_boolean_type
    {schema : Schema} {definition : VariableDefinition}
    (husage
      : Validation.variableUsageAllowed schema definition
          Validation.booleanNonNullType none)
    : definition.typeRef = .named "Boolean"
      ∨ definition.typeRef = .nonNull (.named "Boolean") := by
  rcases husage with ⟨hinput, _, hcompatible⟩
  cases htype : definition.typeRef with
  | named name =>
      simp only [Validation.booleanNonNullType, htype,
        Validation.areInputTypesCompatible] at hcompatible
      exact Or.inl (hcompatible.2 ▸ rfl)
  | list inner =>
      simp only [Validation.booleanNonNullType, htype,
        Validation.areInputTypesCompatible] at hcompatible
      exact False.elim hcompatible.2
  | nonNull inner =>
      cases inner with
      | named name =>
          simp only [Validation.booleanNonNullType, htype,
            Validation.areInputTypesCompatible] at hcompatible
          exact Or.inr (hcompatible ▸ rfl)
      | list inner =>
          simp only [Validation.booleanNonNullType, htype,
            Validation.areInputTypesCompatible] at hcompatible
      | nonNull inner =>
          simp [htype, TypeRef.isInputType] at hinput

private theorem lookupVariableDefinition_of_mem {definitions : List VariableDefinition}
    (hnodup : (definitions.map VariableDefinition.name).Nodup)
    {definition : VariableDefinition} (hmem : definition ∈ definitions)
    : Validation.getVariableDefinition? definitions definition.name
      = some definition := by
  induction definitions with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [Validation.getVariableDefinition?]
      · have hne : head.name ≠ definition.name := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map.mpr ⟨definition, hmem, rfl⟩)
        simpa [Validation.getVariableDefinition?, hne] using ih hnodup.2 hmem

theorem operationBoolVars_haveBooleanTypes {schema : Schema} {operation : Operation}
    (hvalid : Validation.operationDefinitionValid schema operation) {name : Name}
    (hname : name ∈ operationBoolVars operation) {definition : VariableDefinition}
    (hdefinition : definition ∈ operation.variableDefinitions)
    (heq : definition.name = name)
    : definition.typeRef = .named "Boolean"
      ∨ definition.typeRef = .nonNull (.named "Boolean") := by
  have hsource : name ∈ selectionSetBooleanVariables operation.selectionSet :=
    (mem_dedupBoolVars_iff name _).1 hname
  obtain ⟨source, hlookup, husage⟩ :=
    directiveIfArgumentValid_of_selectionSetBooleanVariables schema
      operation.variableDefinitions name (operation.rootType schema)
      operation.selectionSet hsource
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hlookupDef := lookupVariableDefinition_of_mem
    (Validation.operationDefinitionValid_variableDefinitionsValid hvalid).1 hdefinition
  rw [heq] at hlookupDef
  rw [hlookupDef] at hlookup
  have heq : source = definition := Option.some.inj hlookup.symm
  subst source
  exact variableUsageAllowed_boolean_type husage

theorem exists_jointlyTypedBoolCaseValues
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleft : Validation.operationDefinitionValid schema left)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent
          left.variableDefinitions right.variableDefinitions)
    : ∃ baseValues,
        ∀ boolCase,
          completeNormalBoolCase (operationBoolVars left) boolCase
          -> Execution.variablesHaveNonNullValues schema left.variableDefinitions
                (boolCaseVariableValues boolCase baseValues)
              ∧ Execution.variablesHaveNonNullValues schema right.variableDefinitions
                  (boolCaseVariableValues boolCase baseValues) := by
  obtain ⟨baseValues, hvalues⟩ := Execution.exists_variablesHaveNonNullValues hschema
    (Validation.operationDefinitionValid_variableDefinitionsValid hleft)
  refine ⟨baseValues, ?_⟩
  intro boolCase hcomplete
  have hleftValues := Execution.variablesHaveNonNullValues_boolCase hvalues boolCase (by
    intro name bit hmem definition hdefinition heq
    have hname : name ∈ operationBoolVars left :=
      (hcomplete.2.2 name).1 (List.mem_map.mpr ⟨(name, bit), hmem, rfl⟩)
    exact operationBoolVars_haveBooleanTypes hleft hname hdefinition heq)
  exact ⟨hleftValues,
    Execution.variablesHaveNonNullValues_of_equivalent hleftValues hdefinitions⟩

end GraphQL.NormalForm.CompleteNormalization
