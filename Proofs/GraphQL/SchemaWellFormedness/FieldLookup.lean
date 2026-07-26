import GraphQL.SchemaWellFormedness

/-!
Field lookup facts derived from schema well-formedness predicates.
-/

namespace GraphQL

namespace SchemaWellFormedness

theorem fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
    {schema : Schema} {fields : List FieldDefinition}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : fieldDefinitionsWellFormed schema fields
      -> Schema.lookupFieldDefinition fields fieldName = some fieldDefinition
      -> fieldDefinitionWellFormed schema fieldDefinition := by
  intro hfields hlookup
  have hmem : fieldDefinition ∈ fields := by
    simpa [Schema.lookupFieldDefinition] using
      List.mem_of_find?_eq_some hlookup
  exact hfields.2.2 fieldDefinition hmem

theorem fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {fields : List FieldDefinition}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : fieldDefinitionsWellFormed schema fields
      -> Schema.lookupFieldDefinition fields fieldName = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hfields hlookup
  exact
    (fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
      hfields hlookup).1

theorem objectTypeWellFormed_lookupFieldDefinition_wellFormed
    {schema : Schema} {objectType : ObjectType}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : objectTypeWellFormed schema objectType
      -> Schema.lookupFieldDefinition objectType.fields fieldName = some fieldDefinition
      -> fieldDefinitionWellFormed schema fieldDefinition := by
  intro hobject hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
    hobject.1 hlookup

theorem objectTypeWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {objectType : ObjectType}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : objectTypeWellFormed schema objectType
      -> Schema.lookupFieldDefinition objectType.fields fieldName = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hobject hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    hobject.1 hlookup

theorem interfaceTypeWellFormed_lookupFieldDefinition_wellFormed
    {schema : Schema} {interfaceType : InterfaceType}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : interfaceTypeWellFormed schema interfaceType
      -> Schema.lookupFieldDefinition interfaceType.fields fieldName
          = some fieldDefinition
      -> fieldDefinitionWellFormed schema fieldDefinition := by
  intro hinterface hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed
    hinterface.1 hlookup

theorem interfaceTypeWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {interfaceType : InterfaceType}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : interfaceTypeWellFormed schema interfaceType
      -> Schema.lookupFieldDefinition interfaceType.fields fieldName
          = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hinterface hlookup
  exact fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    hinterface.1 hlookup

theorem typeDefinitionWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {typeDefinition : TypeDefinition}
    {fields : List FieldDefinition} {fieldName : Name}
    {fieldDefinition : FieldDefinition}
    : typeDefinitionWellFormed schema typeDefinition
      -> typeDefinition.fields? = some fields
      -> Schema.lookupFieldDefinition fields fieldName = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro htype hfields hlookup
  cases typeDefinition with
  | object objectType =>
      simp [TypeDefinition.fields?] at hfields
      subst fields
      exact objectTypeWellFormed_lookupFieldDefinition_outputType
        htype hlookup
  | interface interfaceType =>
      simp [TypeDefinition.fields?] at hfields
      subst fields
      exact interfaceTypeWellFormed_lookupFieldDefinition_outputType
        htype hlookup
  | builtinScalar scalar =>
      simp [TypeDefinition.fields?] at hfields
  | customScalar scalar =>
      simp [TypeDefinition.fields?] at hfields
  | union unionType =>
      simp [TypeDefinition.fields?] at hfields
  | enum enumType =>
      simp [TypeDefinition.fields?] at hfields
  | inputObject inputObjectType =>
      simp [TypeDefinition.fields?] at hfields

theorem schemaWellFormed_lookupType_typeDefinitionWellFormed
    {schema : Schema} {typeName : Name} {typeDefinition : TypeDefinition}
    : schemaWellFormed schema
      -> schema.lookupType typeName = some typeDefinition
      -> typeDefinitionWellFormed schema typeDefinition := by
  intro hschema hlookup
  have hmemAll : typeDefinition ∈ schema.allTypes := by
    simpa [Schema.lookupType] using List.mem_of_find?_eq_some hlookup
  rcases List.mem_append.mp (by simpa [Schema.allTypes] using hmemAll) with
    hbuiltin | hschemaType
  · simp [Schema.builtinScalarDefinitions] at hbuiltin
    rcases hbuiltin with htype | htype | htype | htype | htype
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
    · subst typeDefinition
      simp [typeDefinitionWellFormed]
  · exact hschema.2.2.1 typeDefinition hschemaType

theorem schemaWellFormed_lookupField_outputType
    {schema : Schema} {parentType fieldName : Name}
    {fieldDefinition : FieldDefinition}
    : schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hschema hlookup
  cases htype : schema.lookupType parentType with
  | none =>
      simp [Schema.lookupField, htype] at hlookup
  | some typeDefinition =>
      have htypeWell :
          typeDefinitionWellFormed schema typeDefinition :=
        schemaWellFormed_lookupType_typeDefinitionWellFormed hschema htype
      cases hfields : typeDefinition.fields? with
      | none =>
          simp [Schema.lookupField, htype, hfields] at hlookup
      | some fields =>
          have hfield :
              Schema.lookupFieldDefinition fields fieldName =
                some fieldDefinition := by
            simpa [Schema.lookupField, htype, hfields,
              Schema.lookupFieldDefinition] using hlookup
          exact typeDefinitionWellFormed_lookupFieldDefinition_outputType
            htypeWell hfields hfield

end SchemaWellFormedness

end GraphQL
