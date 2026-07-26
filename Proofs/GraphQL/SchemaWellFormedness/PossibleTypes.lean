import Proofs.GraphQL.SchemaWellFormedness.FieldLookup

/-!
Possible-type and object implementation facts derived from schema well-formedness.
-/

namespace GraphQL

namespace SchemaWellFormedness

theorem schemaWellFormed_possibleTypesAreObjects {schema : Schema}
    : schemaWellFormed schema
      -> ∀ typeName objectTypeName,
          objectTypeName ∈ schema.getPossibleTypes typeName
          -> schema.objectType objectTypeName := by
  intro hschema
  exact hschema.2.2.2.1

theorem schemaWellFormed_possibleTypesNodup {schema : Schema}
    : schemaWellFormed schema
      -> ∀ typeName, (schema.getPossibleTypes typeName).Nodup := by
  intro hschema
  exact hschema.2.2.2.2.1

theorem schemaWellFormed_possibleObjectFieldDefinitionsImplement {schema : Schema}
    : schemaWellFormed schema -> possibleObjectFieldDefinitionsImplement schema := by
  intro hschema
  exact hschema.2.2.2.2.2

theorem schemaWellFormed_possibleObject_lookupField_implements
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition}
    : schemaWellFormed schema
      -> objectTypeName ∈ schema.getPossibleTypes parentType
      -> schema.lookupField parentType fieldName = some expected
      -> schema.lookupField objectTypeName fieldName = some implementation
      -> fieldDefinitionImplements schema implementation expected := by
  intro hschema hpossible hexpected himplementation
  rcases schemaWellFormed_possibleObjectFieldDefinitionsImplement hschema
      parentType objectTypeName fieldName expected hpossible hexpected with
    ⟨actual, hactual, himplements, _hshape⟩
  rw [hactual] at himplementation
  cases himplementation
  exact himplements

theorem schemaWellFormed_possibleObject_lookupField_sameResponseShape
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition}
    : schemaWellFormed schema
      -> objectTypeName ∈ schema.getPossibleTypes parentType
      -> schema.lookupField parentType fieldName = some expected
      -> schema.lookupField objectTypeName fieldName = some implementation
      -> FieldMerge.sameResponseShape schema
          implementation.outputType expected.outputType := by
  intro hschema hpossible hexpected himplementation
  rcases schemaWellFormed_possibleObjectFieldDefinitionsImplement hschema
      parentType objectTypeName fieldName expected hpossible hexpected with
    ⟨actual, hactual, _himplements, hshape⟩
  rw [hactual] at himplementation
  cases himplementation
  exact hshape

theorem schemaWellFormed_possibleObject_lookupField_exists
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected : FieldDefinition}
    : schemaWellFormed schema
      -> objectTypeName ∈ schema.getPossibleTypes parentType
      -> schema.lookupField parentType fieldName = some expected
      -> ∃ implementation,
          schema.lookupField objectTypeName fieldName = some implementation := by
  intro hschema hpossible hexpected
  rcases schemaWellFormed_possibleObjectFieldDefinitionsImplement hschema
      parentType objectTypeName fieldName expected hpossible hexpected with
    ⟨implementation, himplementation, _himplements, _hshape⟩
  exact ⟨implementation, himplementation⟩

theorem schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition}
    : schemaWellFormed schema
      -> objectTypeName ∈ schema.getPossibleTypes parentType
      -> schema.lookupField parentType fieldName = some expected
      -> schema.lookupField objectTypeName fieldName = some implementation
      -> schema.outputTypeSubtype implementation.outputType expected.outputType := by
  intro hschema hpossible hexpected himplementation
  exact (schemaWellFormed_possibleObject_lookupField_implements hschema
    hpossible hexpected himplementation).1

theorem schemaWellFormed_possibleObject_lookupField_argumentsImplement
    {schema : Schema} {parentType objectTypeName fieldName : Name}
    {expected implementation : FieldDefinition}
    : schemaWellFormed schema
      -> objectTypeName ∈ schema.getPossibleTypes parentType
      -> schema.lookupField parentType fieldName = some expected
      -> schema.lookupField objectTypeName fieldName = some implementation
      -> argumentDefinitionsImplement implementation.arguments expected.arguments := by
  intro hschema hpossible hexpected himplementation
  exact (schemaWellFormed_possibleObject_lookupField_implements hschema
    hpossible hexpected himplementation).2

end SchemaWellFormedness

theorem object_typeIncludesObjectBool_eq_self
    (schema : Schema) {typeName objectName : Name}
    : schema.objectType typeName
      -> schema.typeIncludesObjectBool typeName objectName = true
      -> objectName = typeName := by
  intro hobject hinclude
  rcases hobject with ⟨objectType, hlookup⟩
  have hname : objectType.name = typeName := by
    have hmatch := List.find?_some hlookup
    simpa [Schema.lookupType, TypeDefinition.name] using hmatch
  simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hlookup,
    hname] at hinclude
  exact hinclude

theorem typeIncludesObjectBool_of_outputTypeSubtype_namedType (schema : Schema)
    : ∀ {implementation expected : TypeRef} {objectType : Name},
        schema.outputTypeSubtype implementation expected
        -> schema.typeIncludesObjectBool implementation.namedType objectType = true
        -> schema.typeIncludesObjectBool expected.namedType objectType = true := by
  intro implementation
  induction implementation with
  | named implementationName =>
      intro expected objectType hsubtype hinclude
      cases expected with
      | named expectedName =>
          simp [Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype]
            at hsubtype
          rcases hsubtype with hleaf | hcomposite
          · rcases hleaf with
              ⟨_hleafImplementation, _hleafExpected, heq⟩
            subst expectedName
            exact hinclude
          · rcases hcomposite with
              ⟨_himplementationComposite, _hexpectedComposite, hcontains⟩
            exact List.contains_iff_mem.mpr
              (hcontains objectType (List.contains_iff_mem.mp hinclude))
      | list expectedInner =>
          simp [Schema.outputTypeSubtype] at hsubtype
      | nonNull expectedInner =>
          simp [Schema.outputTypeSubtype] at hsubtype
  | list implementationInner ih =>
      intro expected objectType hsubtype hinclude
      cases expected with
      | named expectedName =>
          simp [Schema.outputTypeSubtype] at hsubtype
      | list expectedInner =>
          simp [Schema.outputTypeSubtype] at hsubtype
          exact ih (expected := expectedInner) hsubtype hinclude
      | nonNull expectedInner =>
          simp [Schema.outputTypeSubtype] at hsubtype
  | nonNull implementationInner ih =>
      intro expected objectType hsubtype hinclude
      cases expected with
      | named expectedName =>
          exact ih hsubtype hinclude
      | list expectedInner =>
          simp [Schema.outputTypeSubtype] at hsubtype
          exact ih hsubtype hinclude
      | nonNull expectedInner =>
          simp [Schema.outputTypeSubtype] at hsubtype
          exact ih (expected := expectedInner) hsubtype hinclude

end GraphQL
