import Proofs.GraphQL.Theories.ExecutionReadiness.SemanticSoundness

/-! The proposed schema constraints discharge operation execution readiness. -/

namespace GraphQL
namespace ExecutionReadiness

open SchemaWellFormedness NormalForm

private theorem lookupType_mem_of_fields {schema : Schema} {parent : Name}
    {definition : TypeDefinition} {fields : List FieldDefinition}
    (hlookup : schema.lookupType parent = some definition)
    (hfields : definition.fields? = some fields)
    : definition ∈ schema.types := by
  have hmem : definition ∈ schema.allTypes := List.mem_of_find?_eq_some hlookup
  rcases List.mem_append.mp hmem with hbuiltin | hmem
  · simp [Schema.builtinScalarDefinitions] at hbuiltin
    rcases hbuiltin with rfl | rfl | rfl | rfl | rfl <;> cases hfields
  · exact hmem

theorem schemaCompositeFieldTypesInhabited_lookupField {schema : Schema}
    (houtputs : schemaCompositeFieldTypesInhabited schema)
    {parent fieldName : Name} {field : FieldDefinition}
    (hlookup : schema.lookupField parent fieldName = some field)
    (hcomposite : field.outputType.isCompositeBool schema = true)
    : nonNullNonListOutputTypeInhabited schema field.outputType := by
  have hname := Schema.lookupField_ne_typename_of_composite hlookup hcomposite
  have hdeclared : schema.lookupDeclaredField parent fieldName = some field := by
    simpa [Schema.lookupField, hname] using hlookup
  cases htype : schema.lookupType parent with
  | none => simp [Schema.lookupDeclaredField, htype] at hdeclared
  | some definition =>
      cases hfields : definition.fields? with
      | none => simp [Schema.lookupDeclaredField, htype, hfields] at hdeclared
      | some fields =>
          have hfield : Schema.lookupFieldDefinition fields fieldName = some field := by
            simpa [Schema.lookupDeclaredField, htype, hfields,
              Schema.lookupFieldDefinition]
              using hdeclared
          exact houtputs definition (lookupType_mem_of_fields htype hfields) fields
            hfields field (List.mem_of_find?_eq_some hfield) hcomposite

mutual
  theorem selectionCompositeFieldTypesInhabited_of_schema {schema : Schema}
      (houtputs : schemaCompositeFieldTypesInhabited schema)
      (values : Execution.VariableValues) (parent : Name) (selection : Selection)
      : selectionCompositeFieldTypesInhabited schema values parent selection := by
    unfold selectionCompositeFieldTypesInhabited
    cases selection with
    | field responseName fieldName arguments directives children =>
        intro _ field hlookup hcomposite
        exact ⟨schemaCompositeFieldTypesInhabited_lookupField houtputs hlookup hcomposite,
          fun runtime _ => selectionSetCompositeFieldTypesInhabited_of_schema houtputs
            values runtime children⟩
    | inlineFragment condition directives children =>
        cases condition with
        | none =>
            intro _
            exact selectionSetCompositeFieldTypesInhabited_of_schema houtputs values parent children
        | some condition =>
            intro _ _
            exact selectionSetCompositeFieldTypesInhabited_of_schema houtputs values parent children

  theorem selectionSetCompositeFieldTypesInhabited_of_schema {schema : Schema}
      (houtputs : schemaCompositeFieldTypesInhabited schema)
      (values : Execution.VariableValues) (parent : Name) (selections : List Selection)
      : selectionSetCompositeFieldTypesInhabited schema values parent selections := by
    unfold selectionSetCompositeFieldTypesInhabited
    cases selections with
    | nil => simp
    | cons head rest =>
        intro selection hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst selection
          exact selectionCompositeFieldTypesInhabited_of_schema houtputs values parent head
        · have hrest := selectionSetCompositeFieldTypesInhabited_of_schema houtputs values parent rest
          unfold selectionSetCompositeFieldTypesInhabited at hrest
          exact hrest selection hmem
end

theorem operationCompositeFieldTypesInhabited_of_schema {schema : Schema}
    (houtputs : schemaCompositeFieldTypesInhabited schema) (operation : Operation)
    : operationCompositeFieldTypesInhabited schema operation := by
  intro values
  exact selectionSetCompositeFieldTypesInhabited_of_schema houtputs values
    (operation.rootType schema) operation.selectionSet

private theorem findType_of_mem {types : List TypeDefinition}
    (hnodup : (types.map TypeDefinition.name).Nodup) {definition : TypeDefinition}
    (hmem : definition ∈ types)
    : types.find? (fun candidate => candidate.name == definition.name)
      = some definition := by
  induction types with
  | nil => cases hmem
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp
      · have hne : head.name ≠ definition.name := by
          intro heq
          exact hnodup.1 (heq ▸ List.mem_map.mpr ⟨definition, hmem, rfl⟩)
        simp [hne, ih hnodup.2 hmem]

private theorem objectType_mem_types {schema : Schema} {objectType : ObjectType}
    (hmem : objectType ∈ schema.objectTypes)
    : TypeDefinition.object objectType ∈ schema.types := by
  obtain ⟨definition, hmem, heq⟩ := List.mem_filterMap.mp hmem
  cases definition <;> simp at heq
  case object candidate =>
    subst candidate
    exact hmem

private theorem argumentDefaultsPreserved_refl {definitions : List InputValueDefinition}
    (hnodup : (definitions.map InputValueDefinition.name).Nodup)
    : argumentDefaultsPreserved definitions definitions := by
  intro definition hmem hdefault
  exact ⟨definition, inputValueDefinitions_lookupArgument_of_mem hnodup hmem, hdefault⟩

-- Transfer the declared interface defaults to the field selected on a concrete object.
-- Explicit ancestor declarations in a well-formed schema cover transitive inheritance.
theorem schemaInterfaceArgumentDefaultsPreserved_lookupField {schema : Schema}
    (hschema : schemaWellFormed schema)
    (hdefaults : schemaInterfaceArgumentDefaultsPreserved schema)
    {parent runtime fieldName : Name} {expected implementation : FieldDefinition}
    (hpossible : runtime ∈ schema.getPossibleTypes parent)
    (hexpected : schema.lookupField parent fieldName = some expected)
    (himplementation : schema.lookupField runtime fieldName = some implementation)
    : argumentDefaultsPreserved implementation.arguments expected.arguments := by
  rcases Schema.lookupField_eq_some_cases hexpected with
    ⟨rfl, rfl, _⟩ | ⟨hne, hdeclared⟩
  · rcases Schema.lookupField_eq_some_cases himplementation with
      ⟨_, rfl, _⟩ | ⟨hne, _⟩
    · simp [Schema.typenameFieldDefinition, argumentDefaultsPreserved]
    · exact False.elim (hne rfl)
  cases hparent : schema.lookupType parent with
  | none => simp [Schema.lookupDeclaredField, hparent] at hdeclared
  | some definition =>
      cases definition <;>
        try (simp [Schema.lookupDeclaredField, hparent, TypeDefinition.fields?] at hdeclared)
      case object objectType =>
        have heq : runtime = parent := object_typeIncludesObjectBool_eq_self schema
          ⟨objectType, hparent⟩ (by simpa [Schema.typeIncludesObjectBool] using hpossible)
        subst runtime
        have heq : implementation = expected := Option.some.inj
          (himplementation.symm.trans hexpected)
        subst implementation
        exact argumentDefaultsPreserved_refl
          (schemaWellFormed_lookupField_wellFormed hschema hexpected).2.1
      case interface interfaceType =>
        have hparentName : interfaceType.name = parent := by
          simpa [TypeDefinition.name] using List.find?_some hparent
        simp only [Schema.getPossibleTypes, hparent, Schema.objectTypesImplementingInterface,
          List.mem_map, List.mem_filter] at hpossible
        obtain ⟨objectType, ⟨hobject, himplements⟩, hname⟩ := hpossible
        have hmem := objectType_mem_types hobject
        have hobjectWell : objectTypeWellFormed schema objectType :=
          hschema.2.2.1 (.object objectType) hmem
        obtain ⟨declared, hdeclaredInterface, hreach⟩ :=
          (objectTypeImplementsInterfaceBool_iff schema objectType interfaceType.name).mp himplements
        have hinterface : parent ∈ objectType.interfaces := by
          rw [← hparentName]
          exact objectTypeWellFormed_reachableInterface_declared hobjectWell hdeclaredInterface hreach
        have hlookupObject : schema.lookupType runtime = some (.object objectType) := by
          rw [← hname]
          exact findType_of_mem hschema.1 (List.mem_append_right _ hmem)
        have hfield : Schema.lookupFieldDefinition interfaceType.fields fieldName = some expected := by
          simpa [Schema.lookupDeclaredField, hparent, TypeDefinition.fields?,
            Schema.lookupFieldDefinition]
            using hdeclared
        have hfieldName : expected.name = fieldName := by
          simpa using List.find?_some hfield
        obtain ⟨actual, hactual, hpreserved⟩ :=
          hdefaults (.object objectType) hmem parent hinterface interfaceType
            (by simp [Schema.lookupInterface, hparent]) expected (List.mem_of_find?_eq_some hfield)
        rw [hfieldName] at hactual
        have hactualLookup : schema.lookupField runtime fieldName = some actual := by
          simpa [Schema.lookupField, hne, Schema.lookupDeclaredField, hlookupObject,
            TypeDefinition.fields?, Schema.lookupFieldDefinition]
            using hactual
        rw [himplementation] at hactualLookup
        cases Option.some.inj hactualLookup
        exact hpreserved

private theorem omittedNonNullArgumentsHaveDefaults_of_preserved
    {schema : Schema} {variables : List VariableDefinition}
    {expected implementation : List InputValueDefinition} {arguments : List Argument}
    (hdefinitions : inputValueDefinitionsWellFormed schema implementation)
    (himplements : argumentDefinitionsImplement implementation expected)
    (hdefaults : argumentDefaultsPreserved implementation expected)
    (hvalid : Validation.argumentsValid schema expected variables arguments)
    : omittedNonNullArgumentsHaveDefaults implementation arguments := by
  intro definition hmem hnonNull hmissing
  have hlookup := inputValueDefinitions_lookupArgument_of_mem hdefinitions.1 hmem
  cases hexpected : Schema.lookupArgumentDefinition expected definition.name with
  | none =>
      have hoptional := himplements.2 definition hmem hexpected
      cases hdefault : definition.defaultValue with
      | some value => rfl
      | none =>
          apply False.elim
          apply hoptional
          cases htype : definition.inputType <;>
            simp_all [InputValueDefinition.isRequired, TypeRef.isNonNull]
  | some source =>
      have hsource : source ∈ expected := List.mem_of_find?_eq_some hexpected
      have hname : source.name = definition.name := by
        simpa using List.find?_some hexpected
      obtain ⟨target, htarget, htype⟩ := himplements.1 source hsource
      rw [hname, hlookup] at htarget
      cases Option.some.inj htarget
      have hsourceDefault := Execution.omittedNonNullArgumentsHaveDefaults_of_valid hvalid
        source hsource (by simpa [htype] using hnonNull) (by simpa [hname] using hmissing)
      obtain ⟨target, htarget, hdefault⟩ := hdefaults source hsource hsourceDefault
      rw [hname, hlookup] at htarget
      cases Option.some.inj htarget
      exact hdefault

mutual
  theorem selectionCoercibleInPossibleTypes_of_schema {schema : Schema}
      {variables : List VariableDefinition} (hschema : schemaWellFormed schema)
      (hdefaults : schemaInterfaceArgumentDefaultsPreserved schema)
      (values : Execution.VariableValues) {sourceType runtimeType : Name}
      (hpossible : runtimeType ∈ schema.getPossibleTypes sourceType)
      (selection : Selection)
      (hvalid : Validation.selectionValid schema variables sourceType selection)
      : selectionCoercibleInPossibleTypes schema values runtimeType selection := by
    unfold selectionCoercibleInPossibleTypes
    cases selection with
    | field responseName fieldName arguments directives children =>
        intro _
        cases hlookup : schema.lookupField runtimeType fieldName with
        | none => trivial
        | some definition =>
            obtain ⟨source, hsource, harguments, hchildren⟩ :=
              Validation.selectionValid_field_lookup hvalid
            constructor
            · exact omittedNonNullArgumentsHaveDefaults_of_preserved
                (schemaWellFormed_lookupField_wellFormed hschema hlookup).2
                (schemaWellFormed_possibleObject_lookupField_argumentsImplement hschema
                  hpossible hsource hlookup)
                (schemaInterfaceArgumentDefaultsPreserved_lookupField hschema hdefaults
                  hpossible hsource hlookup) harguments
            · intro childType hmember
              have hsourcePossible := typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
                (schemaWellFormed_possibleObject_lookupField_outputTypeSubtype hschema
                  hpossible hsource hlookup)
                (by simpa [Schema.typeIncludesObjectBool] using hmember)
              have hsourceMember : childType ∈ schema.getPossibleTypes source.outputType.namedType := by
                simpa [Schema.typeIncludesObjectBool] using hsourcePossible
              exact selectionSetCoercibleInPossibleTypes_of_schema hschema hdefaults
                values hsourceMember children
                (fieldSelectionSetValid_child_of_possibleType hchildren hsourceMember)
    | inlineFragment condition directives children =>
        cases condition with
        | none =>
            intro _
            exact selectionSetCoercibleInPossibleTypes_of_schema hschema hdefaults values
              hpossible children (Validation.selectionValid_inlineFragment_none_selectionSetValid hvalid)
        | some condition =>
            intro _ hcondition
            have hmember : runtimeType ∈ schema.getPossibleTypes condition := by
              simpa [Schema.typeIncludesObjectBool] using hcondition
            exact selectionSetCoercibleInPossibleTypes_of_schema hschema hdefaults values
              hmember children
              (Validation.selectionValid_inlineFragment_some_selectionSetValid hvalid)

  theorem selectionSetCoercibleInPossibleTypes_of_schema {schema : Schema}
      {variables : List VariableDefinition} (hschema : schemaWellFormed schema)
      (hdefaults : schemaInterfaceArgumentDefaultsPreserved schema)
      (values : Execution.VariableValues) {sourceType runtimeType : Name}
      (hpossible : runtimeType ∈ schema.getPossibleTypes sourceType)
      (selections : List Selection)
      (hvalid : Validation.selectionSetValid schema variables sourceType selections)
      : selectionSetCoercibleInPossibleTypes schema values runtimeType selections := by
    cases selections with
    | nil => trivial
    | cons head rest =>
        unfold Validation.selectionSetValid at hvalid
        exact ⟨
          selectionCoercibleInPossibleTypes_of_schema hschema hdefaults values hpossible
            head (hvalid head (by simp)),
          selectionSetCoercibleInPossibleTypes_of_schema hschema hdefaults values
            hpossible rest
            (by
              unfold Validation.selectionSetValid
              exact fun selection hmem => hvalid selection (List.mem_cons_of_mem _ hmem))
        ⟩
end

theorem operationCoercibleInPossibleTypes_of_schema {schema : Schema}
    (hschema : schemaWellFormed schema)
    (hdefaults : schemaInterfaceArgumentDefaultsPreserved schema) {operation : Operation}
    (hvalid : Validation.operationDefinitionValid schema operation)
    : operationCoercibleInPossibleTypes schema operation := by
  intro values
  have hroot : schema.objectType (operation.rootType schema) := by
    cases operation.operationType
    exact hschema.2.1
  apply selectionSetCoercibleInPossibleTypes_of_schema hschema hdefaults values
    (sourceType := operation.rootType schema) ?_ operation.selectionSet
    (Validation.operationDefinitionValid_selectionSetValid hvalid)
  simpa [Schema.typeIncludesObjectBool]
    using object_typeIncludesObjectBool_self schema hroot

end ExecutionReadiness

theorem schemaExecution_sound {schema : Schema} : SchemaExecutionSound schema := by
  intro hschema hdefaults houtputs operation hvalid
  exact executionReadiness_sound hschema hvalid
    (ExecutionReadiness.operationCompositeFieldTypesInhabited_of_schema houtputs operation)
    (ExecutionReadiness.operationCoercibleInPossibleTypes_of_schema hschema hdefaults hvalid)

end GraphQL
