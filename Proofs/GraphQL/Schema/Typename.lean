import GraphQL.Schema

/-! Implicit type-name lookup and its separation from declared fields. -/

namespace GraphQL.Schema

theorem lookupField_typename {schema : Schema} {parentType : Name}
    (hparent : schema.isCompositeType parentType)
    : schema.lookupField parentType "__typename" = some typenameFieldDefinition := by
  obtain ⟨definition, hlookup, hcomposite⟩ := hparent
  cases definition <;>
    simp_all [lookupField, TypeDefinition.isCompositeType]

theorem lookupField_eq_some_cases {schema : Schema} {parentType fieldName : Name}
    {field : FieldDefinition}
    (hlookup : schema.lookupField parentType fieldName = some field)
    : (fieldName = "__typename"
        ∧ field = typenameFieldDefinition
        ∧ schema.isCompositeType parentType)
      ∨ (fieldName ≠ "__typename"
          ∧ schema.lookupDeclaredField parentType fieldName = some field) := by
  by_cases hname : fieldName = "__typename"
  · subst fieldName
    cases htype : schema.lookupType parentType with
    | none => simp [lookupField, htype] at hlookup
    | some definition =>
        cases definition <;> simp [lookupField, htype] at hlookup
        all_goals
          subst field
          exact Or.inl ⟨rfl, rfl, ⟨_, htype, trivial⟩⟩
  · exact Or.inr ⟨hname, by simpa [lookupField, hname] using hlookup⟩

theorem lookupField_ne_typename_of_composite {schema : Schema}
    {parentType fieldName : Name} {field : FieldDefinition}
    (hlookup : schema.lookupField parentType fieldName = some field)
    (hcomposite : field.outputType.isCompositeBool schema = true)
    : fieldName ≠ "__typename" := by
  intro hmeta
  subst fieldName
  rcases lookupField_eq_some_cases hlookup with ⟨_, rfl, _⟩ | ⟨hne, _⟩
  · simp [typenameFieldDefinition, TypeRef.isCompositeBool, TypeRef.namedType,
      lookupType, allTypes, builtinScalarDefinitions, TypeDefinition.name,
      BuiltinScalar.name, List.find?] at hcomposite
  · exact hne rfl

theorem lookupField_ne_typename_of_includesObject {schema : Schema}
    {parentType fieldName runtimeType : Name} {field : FieldDefinition}
    (hlookup : schema.lookupField parentType fieldName = some field)
    (hincludes
      : schema.typeIncludesObjectBool field.outputType.namedType runtimeType = true)
    : fieldName ≠ "__typename" := by
  intro hmeta
  subst fieldName
  rcases lookupField_eq_some_cases hlookup with ⟨_, rfl, _⟩ | ⟨hne, _⟩
  · simp [typenameFieldDefinition, TypeRef.namedType, typeIncludesObjectBool, getPossibleTypes,
      lookupType, allTypes, builtinScalarDefinitions, TypeDefinition.name,
      BuiltinScalar.name, List.find?] at hincludes
  · exact hne rfl

end GraphQL.Schema
