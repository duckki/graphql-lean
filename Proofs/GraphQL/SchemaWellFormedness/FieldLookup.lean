import GraphQL.SchemaWellFormedness
import Proofs.GraphQL.Schema.Typename

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
    simpa [Schema.lookupFieldDefinition] using List.mem_of_find?_eq_some hlookup
  exact hfields.2.2 fieldDefinition hmem

theorem fieldDefinitionsWellFormed_lookupFieldDefinition_outputType
    {schema : Schema} {fields : List FieldDefinition}
    {fieldName : Name} {fieldDefinition : FieldDefinition}
    : fieldDefinitionsWellFormed schema fields
      -> Schema.lookupFieldDefinition fields fieldName = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hfields hlookup
  exact (fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed hfields hlookup).1

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

theorem typenameFieldDefinition_wellFormed (schema : Schema)
    : fieldDefinitionWellFormed schema Schema.typenameFieldDefinition := by
  constructor
  · exact ⟨.builtinScalar .string, rfl, trivial⟩
  · simp [Schema.typenameFieldDefinition, inputValueDefinitionsWellFormed, namesAreUnique]

theorem typenameFieldDefinition_implements (schema : Schema)
    : fieldDefinitionImplements schema Schema.typenameFieldDefinition
        Schema.typenameFieldDefinition := by
  refine ⟨?_, ?_⟩
  · exact ⟨⟨.builtinScalar .string, rfl, trivial⟩,
      ⟨.builtinScalar .string, rfl, trivial⟩, Or.inl rfl⟩
  · simp [argumentDefinitionsImplement, Schema.typenameFieldDefinition]

theorem lookupField_typename_implements {schema : Schema} {parentType objectType : Name}
    {expected : FieldDefinition}
    (hlookup : schema.lookupField parentType "__typename" = some expected)
    (hobject : schema.objectType objectType)
    : ∃ implementation,
        schema.lookupField objectType "__typename" = some implementation
        ∧ fieldDefinitionImplements schema implementation expected := by
  rcases Schema.lookupField_eq_some_cases hlookup with ⟨_, rfl, _⟩ | ⟨hne, _⟩
  · obtain ⟨definition, hobject⟩ := hobject
    exact ⟨_, Schema.lookupField_typename ⟨.object definition, hobject, trivial⟩,
      typenameFieldDefinition_implements schema⟩
  · exact False.elim (hne rfl)

theorem schemaWellFormed_lookupField_wellFormed
    {schema : Schema} {parentType fieldName : Name}
    {fieldDefinition : FieldDefinition}
    : schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinitionWellFormed schema fieldDefinition := by
  intro hschema hlookup
  rcases Schema.lookupField_eq_some_cases hlookup with ⟨_, rfl, _⟩ | ⟨_, hlookup⟩
  · exact typenameFieldDefinition_wellFormed schema
  cases htype : schema.lookupType parentType with
  | none =>
      simp [Schema.lookupDeclaredField, htype] at hlookup
  | some typeDefinition =>
      have htypeWell :
          typeDefinitionWellFormed schema typeDefinition :=
        schemaWellFormed_lookupType_typeDefinitionWellFormed hschema htype
      cases hfields : typeDefinition.fields? with
      | none =>
          simp [Schema.lookupDeclaredField, htype, hfields] at hlookup
      | some fields =>
          have hfield :
              Schema.lookupFieldDefinition fields fieldName =
                some fieldDefinition := by
            simpa [Schema.lookupDeclaredField, htype, hfields,
              Schema.lookupFieldDefinition]
              using hlookup
          cases typeDefinition <;> simp [TypeDefinition.fields?] at hfields
          all_goals
            subst fields
            exact fieldDefinitionsWellFormed_lookupFieldDefinition_wellFormed htypeWell.1 hfield

theorem schemaWellFormed_lookupField_outputType
    {schema : Schema} {parentType fieldName : Name}
    {fieldDefinition : FieldDefinition}
    : schemaWellFormed schema
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.isOutputType schema := by
  intro hschema hlookup
  exact (schemaWellFormed_lookupField_wellFormed hschema hlookup).1

end SchemaWellFormedness

end GraphQL
