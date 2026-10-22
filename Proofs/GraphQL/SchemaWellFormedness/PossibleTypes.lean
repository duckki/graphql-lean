import Proofs.GraphQL.SchemaWellFormedness.FieldLookup
import Proofs.GraphQL.SchemaWellFormedness.InterfaceInheritance

/-!
Possible-type and object implementation facts derived from schema well-formedness.
-/

namespace GraphQL

namespace SchemaWellFormedness

-- Schema well-formedness includes the spec 3.10 default-expansion-cycle check.
theorem schemaWellFormed_inputDefaultExpansionAcyclic {schema : Schema}
    : schemaWellFormed schema -> inputDefaultExpansionAcyclic schema := by
  intro hschema
  exact hschema.2.2.2.1.2

theorem schemaWellFormed_possibleTypesAreObjects {schema : Schema}
    : schemaWellFormed schema
      -> ∀ typeName objectTypeName,
          objectTypeName ∈ schema.getPossibleTypes typeName
          -> schema.objectType objectTypeName := by
  intro hschema
  exact hschema.2.2.2.2.1

theorem schemaWellFormed_possibleTypesNodup {schema : Schema}
    : schemaWellFormed schema
      -> ∀ typeName, (schema.getPossibleTypes typeName).Nodup := by
  intro hschema
  exact hschema.2.2.2.2.2.1

theorem schemaWellFormed_possibleObjectFieldDefinitionsImplement {schema : Schema}
    : schemaWellFormed schema -> possibleObjectFieldDefinitionsImplement schema := by
  intro hschema
  exact hschema.2.2.2.2.2.2

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
    ⟨actual, hactual, himplements⟩
  rw [hactual] at himplementation
  cases himplementation
  exact himplements

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
    ⟨implementation, himplementation, _himplements⟩
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

private theorem objectType_mem_of_lookup {schema : Schema} {name : Name}
    {objectType : ObjectType}
    (hlookup : schema.lookupType name = some (.object objectType))
    : objectType ∈ schema.objectTypes := by
  have hmem : .object objectType ∈ schema.allTypes :=
    List.mem_of_find?_eq_some hlookup
  have hmem' : .object objectType ∈ schema.types := by
    simpa [Schema.builtinScalarDefinitions] using List.mem_append.mp hmem
  exact List.mem_filterMap.mpr ⟨.object objectType, hmem', rfl⟩

theorem typeIncludesObjectBool_of_isSubType (schema : Schema)
    {implementation expected objectName : Name}
    (hsubtype : schema.isSubType implementation expected)
    (hinclude : schema.typeIncludesObjectBool implementation objectName = true)
    : schema.typeIncludesObjectBool expected objectName = true := by
  rcases hsubtype with rfl | hsubtype
  · exact hinclude
  split at hsubtype
  · rename_i objectType unionType hobject hunion
    have heq := object_typeIncludesObjectBool_eq_self schema ⟨objectType, hobject⟩ hinclude
    subst objectName
    simpa [Schema.typeIncludesObjectBool, Schema.getPossibleTypes, hunion]
      using List.contains_iff_mem.mpr hsubtype
  · rename_i objectType interfaceType hobject hinterface
    have hname : interfaceType.name = expected := by
      simpa [TypeDefinition.name] using List.find?_some hinterface
    have hobjectName : objectType.name = implementation := by
      simpa [TypeDefinition.name] using List.find?_some hobject
    have heq := object_typeIncludesObjectBool_eq_self schema ⟨objectType, hobject⟩ hinclude
    subst objectName
    apply List.contains_iff_mem.mpr
    simp only [Schema.getPossibleTypes, hinterface, hname,
      Schema.objectTypesImplementingInterface, List.mem_map, List.mem_filter]
    refine ⟨objectType, ⟨objectType_mem_of_lookup hobject, ?_⟩, hobjectName⟩
    apply List.any_eq_true.mpr
    refine ⟨expected, hsubtype, ?_⟩
    exact (interfaceTypeImplementsInterfaceBool_iff schema expected expected).mpr
      (.refl _)
  · rename_i implementationInterface expectedInterface himplementation hexpected
    have himplementationName : implementationInterface.name = implementation := by
      simpa [TypeDefinition.name] using List.find?_some himplementation
    have hexpectedName : expectedInterface.name = expected := by
      simpa [TypeDefinition.name] using List.find?_some hexpected
    have hparent : schema.interfaceTypeImplementsInterface implementation expected :=
      .trans implementation expected implementationInterface expected
        (by simp [Schema.lookupInterface, himplementation]) hsubtype (.refl _)
    have hmem := List.contains_iff_mem.mp hinclude
    simp only [Schema.getPossibleTypes, himplementation, himplementationName,
      Schema.objectTypesImplementingInterface, List.mem_map, List.mem_filter] at hmem
    rcases hmem with ⟨objectType, ⟨hobject, himplements⟩, hname⟩
    apply List.contains_iff_mem.mpr
    simp only [Schema.getPossibleTypes, hexpected, hexpectedName,
      Schema.objectTypesImplementingInterface, List.mem_map, List.mem_filter]
    refine ⟨objectType, ⟨hobject, ?_⟩, hname⟩
    rcases List.any_eq_true.mp himplements with ⟨declared, hdeclared, hreach⟩
    apply List.any_eq_true.mpr
    refine ⟨declared, hdeclared, ?_⟩
    apply (interfaceTypeImplementsInterfaceBool_iff schema declared expected).mpr
    exact interfaceTypeImplementsInterface_trans
      ((interfaceTypeImplementsInterfaceBool_iff schema declared implementation).mp
        hreach)
      hparent
  · contradiction

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
          exact typeIncludesObjectBool_of_isSubType schema hsubtype.2.2 hinclude
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
