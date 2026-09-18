import Proofs.GraphQL.SchemaWellFormedness.FieldLookup

/-! Input-type inhabitants derived from schema well-formedness.

Nullable fields and lists break recursion. The non-null singular cycle check
bounds the remaining dependencies by the finite list of schema type names.
-/

namespace GraphQL.SchemaWellFormedness

theorem inputValueDefinitions_lookupArgument_of_mem
    {definitions : List InputValueDefinition}
    (hnodup : (definitions.map InputValueDefinition.name).Nodup)
    {definition : InputValueDefinition} (hmem : definition ∈ definitions)
    : Schema.lookupArgumentDefinition definitions definition.name = some definition := by
  induction definitions with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [Schema.lookupArgumentDefinition]
      · have hne : head.name ≠ definition.name := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map.mpr ⟨definition, hmem, rfl⟩)
        simpa [Schema.lookupArgumentDefinition, hne] using ih hnodup.2 hmem

private theorem lookupValue_map {definitions : List InputValueDefinition}
    (values : InputValueDefinition -> ConstInputValue)
    (hnodup : (definitions.map InputValueDefinition.name).Nodup)
    {definition : InputValueDefinition} (hmem : definition ∈ definitions)
    : Schema.getConstInputObjectField?
        (definitions.map fun d => (d.name, values d)) definition.name
      = some (values definition) := by
  induction definitions with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [Schema.getConstInputObjectField?]
      · have hne : head.name ≠ definition.name := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map.mpr ⟨definition, hmem, rfl⟩)
        simp [Schema.getConstInputObjectField?, hne, ih hnodup.2 hmem]

private theorem nonNull_of_correctType {schema : Schema} {value : ConstInputValue}
    {inner : TypeRef}
    (h : Schema.ConstInputValueIsCorrectType schema value (.nonNull inner))
    : value.nonNull := by
  cases h with
  | nonNull value _ _ hnotNull _ =>
      cases value <;> simp_all [ConstInputValue.nonNull]

private theorem fieldsInhabited {schema : Schema}
    {definitions : List InputValueDefinition}
    (hnodup : (definitions.map InputValueDefinition.name).Nodup)
    (hvalues
      : ∀ definition,
          definition ∈ definitions
          -> ∃ value,
              Schema.ConstInputValueIsCorrectType schema value definition.inputType)
    : ∃ fields, Schema.ConstInputObjectFieldsValid schema definitions fields := by
  classical
  let values := fun definition =>
    if hmem : definition ∈ definitions then Classical.choose (hvalues definition hmem)
    else .null
  have htyped (definition : InputValueDefinition) (hmem : definition ∈ definitions) :
      Schema.ConstInputValueIsCorrectType schema (values definition) definition.inputType := by
    simpa [values, hmem] using Classical.choose_spec (hvalues definition hmem)
  refine ⟨definitions.map (fun d => (d.name, values d)), .intro _ _ ?_ ?_ ?_ ?_ ?_⟩
  · simpa [List.map_map, Function.comp_def] using hnodup
  · intro name value hmem
    obtain ⟨definition, hdefinition, heq⟩ := List.mem_map.mp hmem
    cases heq
    rw [inputValueDefinitions_lookupArgument_of_mem hnodup hdefinition]
    rfl
  · intro name value definition hmem hlookup
    obtain ⟨source, hsource, heq⟩ := List.mem_map.mp hmem
    cases heq
    rw [inputValueDefinitions_lookupArgument_of_mem hnodup hsource] at hlookup
    have heq : definition = source := Option.some.inj hlookup.symm
    subst definition
    exact htyped source hsource
  · intro definition hmem _
    rw [lookupValue_map values hnodup hmem]
    rfl
  · intro definition value hmem hrequired hlookup
    rw [lookupValue_map values hnodup hmem] at hlookup
    cases Option.some.inj hlookup
    have htype := htyped definition hmem
    cases hinput : definition.inputType with
    | named name => simp [InputValueDefinition.isRequired, hinput] at hrequired
    | list inner => simp [InputValueDefinition.isRequired, hinput] at hrequired
    | nonNull inner =>
        rw [hinput] at htype
        exact nonNull_of_correctType htype

-- Nullable fields use null, and non-null lists use an empty list. Only a non-null
-- singular input-object field creates a dependency on another input-object witness.
private theorem inputTypeInhabited_of_requiredTargets {schema : Schema}
    (inputType : TypeRef) (hinput : inputType.isInputType schema)
    (htarget
      : ∀ target,
          nonNullSingularInputObjectTarget? inputType = some target
          -> ∀ inputObject,
              schema.lookupInputObject target = some inputObject
              -> ∃ fields,
                  Schema.ConstInputObjectFieldsValid schema inputObject.inputFields
                    fields)
    : ∃ value, Schema.ConstInputValueIsCorrectType schema value inputType := by
  cases inputType with
  | named name => exact ⟨.null, .nullNamed name hinput⟩
  | list inner => exact ⟨.null, .nullList inner hinput⟩
  | nonNull inner =>
      cases inner with
      | nonNull inner => exact False.elim hinput
      | list inner =>
          exact ⟨.list [], .nonNull _ _ hinput (by simp) (.list _ _ hinput (by simp))⟩
      | named name =>
          cases hlookup : schema.lookupInputObject name with
          | none =>
              exact ⟨
                .int 1,
                .nonNull _ _ hinput (by simp)
                  (.namedNonInputObject _ _ hinput (by simp) (by simp) hlookup)
              ⟩
          | some inputObject =>
              obtain ⟨fields, hfields⟩ := htarget name rfl inputObject hlookup
              exact ⟨
                .object fields,
                .nonNull _ _ hinput (by simp)
                  (.objectNamed _ _ inputObject hinput hlookup hfields)
              ⟩

theorem lookupInputObject_type {schema : Schema} {name : Name}
    {inputObject : InputObjectType}
    (hlookup : schema.lookupInputObject name = some inputObject)
    : schema.lookupType name = some (.inputObject inputObject) := by
  cases htype : schema.lookupType name with
  | none => simp [Schema.lookupInputObject, htype] at hlookup
  | some typeDefinition =>
      cases typeDefinition <;> simp [Schema.lookupInputObject, htype] at hlookup
      case inputObject candidate =>
        subst candidate
        rfl

theorem lookupInputObject_mem {schema : Schema} {name : Name}
    {inputObject : InputObjectType}
    (hlookup : schema.lookupInputObject name = some inputObject)
    : .inputObject inputObject ∈ schema.types := by
  have htype := lookupInputObject_type hlookup
  have hmem : .inputObject inputObject ∈ schema.allTypes := by
    exact List.mem_of_find?_eq_some htype
  have hmem' : .inputObject inputObject ∈ Schema.builtinScalarDefinitions
      ∨ .inputObject inputObject ∈ schema.types := List.mem_append.mp hmem
  simpa [Schema.builtinScalarDefinitions] using hmem'

theorem lookupInputObject_name {schema : Schema} {name : Name}
    {inputObject : InputObjectType}
    (hlookup : schema.lookupInputObject name = some inputObject)
    : inputObject.name = name := by
  have htype := lookupInputObject_type hlookup
  have hfound := List.find?_some htype
  simpa [TypeDefinition.name] using hfound

private theorem inputObjectFieldsInhabited_of_no_cycle
    (schema : Schema) (hschema : schemaWellFormed schema)
    : ∀ fuel visited name inputObject,
        inputObjectHasNonNullSingularCycleFrom schema fuel visited name = false
        -> visited.Nodup
        -> visited ⊆ schema.types.map TypeDefinition.name
        -> schema.types.length < visited.length + fuel
        -> schema.lookupInputObject name = some inputObject
        -> ∃ fields,
            Schema.ConstInputObjectFieldsValid schema inputObject.inputFields fields := by
  intro fuel
  induction fuel with
  | zero =>
      intro visited name inputObject _ hnodup hsubset hlength _
      have hle := hnodup.length_le_of_subset hsubset
      simp only [List.length_map] at hle
      omega
  | succ fuel ih =>
      intro visited name inputObject hcycle hnodup hsubset hlength hlookup
      have hnotmem : name ∉ visited := by
        intro hmem
        simp [inputObjectHasNonNullSingularCycleFrom, hmem] at hcycle
      have hmemSchema : name ∈ schema.types.map TypeDefinition.name := by
        exact List.mem_map.mpr ⟨.inputObject inputObject, lookupInputObject_mem hlookup,
          lookupInputObject_name hlookup⟩
      have hnextNodup : (name :: visited).Nodup := List.nodup_cons.mpr ⟨hnotmem, hnodup⟩
      have hnextSubset : name :: visited ⊆ schema.types.map TypeDefinition.name := by
        intro candidate hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hmemSchema
        · exact hsubset hmem
      have hobjectWell : inputObjectTypeWellFormed schema inputObject :=
        hschema.2.2.1 (.inputObject inputObject) (lookupInputObject_mem hlookup)
      apply fieldsInhabited hobjectWell.2.1
      intro definition hdefinition
      apply inputTypeInhabited_of_requiredTargets definition.inputType
        (hobjectWell.2.2 definition hdefinition).1
      intro target htarget targetObject htargetLookup
      have hchildCycle : inputObjectHasNonNullSingularCycleFrom schema fuel
          (name :: visited) target = false := by
        simp only [inputObjectHasNonNullSingularCycleFrom, List.contains_eq_mem,
          hnotmem, hlookup] at hcycle
        have hfield := (List.any_eq_false.mp hcycle) definition hdefinition
        simpa [htarget] using hfield
      exact ih (name :: visited) target targetObject hchildCycle hnextNodup hnextSubset
        (by simp only [List.length_cons]; omega) htargetLookup

theorem schemaWellFormed_inputObjectFieldsInhabited
    {schema : Schema} (hschema : schemaWellFormed schema)
    {name : Name} {inputObject : InputObjectType}
    (hlookup : schema.lookupInputObject name = some inputObject)
    : ∃ fields,
        Schema.ConstInputObjectFieldsValid schema inputObject.inputFields fields := by
  have hacyclic := hschema.2.2.2.1.1
  unfold inputObjectNonNullSingularCircularReferencesValid
    inputObjectNonNullSingularCircularReferencesValidBool at hacyclic
  have hname : name = inputObject.name := (lookupInputObject_name hlookup).symm
  subst name
  have hmem : inputObject.name ∈ schema.types.filterMap (fun definition =>
      match definition with
      | .inputObject object => some object.name
      | _ => none) := by
    exact List.mem_filterMap.mpr ⟨.inputObject inputObject, lookupInputObject_mem hlookup, rfl⟩
  have hcycle := List.all_eq_true.mp hacyclic inputObject.name hmem
  have hcycleFalse : inputObjectHasNonNullSingularCycleFrom schema
      (schema.types.length + 1) [] inputObject.name = false := by
    cases h : inputObjectHasNonNullSingularCycleFrom schema
        (schema.types.length + 1) [] inputObject.name <;> simp_all
  exact inputObjectFieldsInhabited_of_no_cycle schema hschema _ [] _ inputObject
    hcycleFalse (by simp) (by simp) (by simp) hlookup

theorem schemaWellFormed_inputTypeInhabited_nonNull
    {schema : Schema} (hschema : schemaWellFormed schema) (inputType : TypeRef)
    (hinput : inputType.isInputType schema)
    : ∃ value : ConstInputValue,
        value.nonNull ∧ Schema.ConstInputValueIsCorrectType schema value inputType := by
  induction inputType with
  | named name =>
      cases hlookup : schema.lookupInputObject name with
      | none =>
          exact ⟨
            .int 1,
            trivial,
            .namedNonInputObject _ _ hinput (by simp) (by simp) hlookup
          ⟩
      | some inputObject =>
          obtain ⟨fields, hfields⟩ :=
            schemaWellFormed_inputObjectFieldsInhabited hschema hlookup
          exact ⟨
            .object fields,
            trivial,
            .objectNamed _ _ inputObject hinput hlookup hfields
          ⟩
  | list inner _ =>
      exact ⟨.list [], trivial, .list [] inner hinput (by simp)⟩
  | nonNull inner ih =>
      have hinner : inner.isInputType schema := by
        cases inner with
        | named _ => exact hinput
        | list _ => exact hinput
        | nonNull _ => exact False.elim hinput
      obtain ⟨value, hnonnull, hcorrect⟩ := ih hinner
      have hnotNull : value ≠ .null := by
        intro heq
        subst value
        exact hnonnull
      exact ⟨value, hnonnull, .nonNull _ _ hinput hnotNull hcorrect⟩

end GraphQL.SchemaWellFormedness
