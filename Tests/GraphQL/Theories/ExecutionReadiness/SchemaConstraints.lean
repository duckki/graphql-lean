import Proofs.GraphQL.Theories.ExecutionReadiness.SchemaConstraints

namespace GraphQL.Tests.ExecutionReadiness.SchemaConstraints

private def argument (defaultValue : Option ConstInputValue) : InputValueDefinition :=
  { name := "a", inputType := .nonNull (.named "Int"), defaultValue := defaultValue }

private def field (defaultValue : Option ConstInputValue) : FieldDefinition :=
  { name := "f", outputType := .named "String", arguments := [argument defaultValue] }

private def defaultsSchema (implementationDefault : Option ConstInputValue)
    (interfaceImplementation : Bool := false)
    : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .interface { name := "I", fields := [field (some (.int 1))] },
        if interfaceImplementation then
          .interface
            { name := "J", interfaces := ["I"], fields := [field implementationDefault] }
        else
          .object
            {
              name := "Query",
              interfaces := ["I"],
              fields := [field implementationDefault]
            }
      ]
  }

attribute [local simp] argument field defaultsSchema
  schemaInterfaceArgumentDefaultsPreserved fieldsPreserveInterfaceArgumentDefaults
  argumentDefaultsPreserved Schema.lookupInterface Schema.lookupType Schema.allTypes
  Schema.builtinScalarDefinitions TypeDefinition.name BuiltinScalar.name
  Schema.lookupFieldDefinition Schema.lookupArgumentDefinition List.find?_cons

-- Presence is preserved; matching default values are optional.
example : schemaInterfaceArgumentDefaultsPreserved (defaultsSchema (some (.int 1))) := by
  simp

example : schemaInterfaceArgumentDefaultsPreserved (defaultsSchema (some (.int 2))) := by
  simp

example : ¬ schemaInterfaceArgumentDefaultsPreserved (defaultsSchema none) := by simp

-- No default is required when the interface does not promise one.
example : argumentDefaultsPreserved [argument none] [argument none] := by simp

-- An interface implementing another interface must preserve defaults too.
example
    : schemaInterfaceArgumentDefaultsPreserved (defaultsSchema (some (.int 2)) true) := by
  simp

example : ¬ schemaInterfaceArgumentDefaultsPreserved (defaultsSchema none true) := by simp

-- The proposed rule also preserves nullable defaults, including an explicit null.
example
    : argumentDefaultsPreserved
        [{ name := "a", inputType := .named "Int", defaultValue := some .null }]
        [{ name := "a", inputType := .named "Int", defaultValue := some (.int 1) }] := by
  simp

example
    : ¬ argumentDefaultsPreserved
          [{ name := "a", inputType := .named "Int" }]
          [{ name := "a", inputType := .named "Int", defaultValue := some .null }] := by
  simp

private def outputsSchema (outputType : TypeRef) : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .interface
          {
            name := "Empty", fields := [{ name := "name", outputType := .named "String" }]
          },
        .object
          { name := "Query", fields := [{ name := "empty", outputType := outputType }] }
      ]
  }

attribute [local simp] outputsSchema schemaCompositeFieldTypesInhabited
  nonNullNonListOutputTypeInhabited TypeDefinition.fields? TypeRef.isCompositeBool
  TypeRef.namedType Schema.getPossibleTypes Schema.objectTypesImplementingInterface
  Schema.objectTypes Schema.objectTypeImplementsInterfaceBool
  List.filterMap_cons List.filter_cons

-- An interface without implementations is allowed, but a singular non-null use is not.
example : schemaCompositeFieldTypesInhabited (outputsSchema (.named "Empty")) := by simp

example
    : ¬ schemaCompositeFieldTypesInhabited
          (outputsSchema (.nonNull (.named "Empty"))) := by simp

-- Every list form admits an empty list, including lists with non-null elements.
example
    : schemaCompositeFieldTypesInhabited (outputsSchema (.list (.named "Empty"))) := by
  simp

example
    : schemaCompositeFieldTypesInhabited
        (outputsSchema (.list (.nonNull (.named "Empty")))) := by simp

example
    : schemaCompositeFieldTypesInhabited
        (outputsSchema (.nonNull (.list (.named "Empty")))) := by simp

example
    : schemaCompositeFieldTypesInhabited
        (outputsSchema (.nonNull (.list (.nonNull (.named "Empty"))))) := by simp

-- The composite guard permits non-null scalar fields.
example
    : schemaCompositeFieldTypesInhabited
        (outputsSchema (.nonNull (.named "String"))) := by simp

-- Inhabited composite types may still be singular and non-null.
example
    : schemaCompositeFieldTypesInhabited (outputsSchema (.nonNull (.named "Query"))) := by
  simp

private def inhabitedSchema : Schema :=
  {
    outputsSchema (.nonNull (.named "Empty")) with
      types :=
        (outputsSchema (.nonNull (.named "Empty"))).types
        ++ [.object
              {
                name := "Value",
                interfaces := ["Empty"],
                fields := [{ name := "name", outputType := .named "String" }]
              }]
  }

example : schemaCompositeFieldTypesInhabited inhabitedSchema := by
  simp [inhabitedSchema, Schema.interfaceTypeImplementsInterfaceBool,
    Schema.interfaceTypeImplementsInterfaceBoundedBool]

#print axioms GraphQL.schemaExecution_sound
#print axioms GraphQL.ExecutionReadiness.operationCoercibleInPossibleTypes_of_schema
#print axioms GraphQL.ExecutionReadiness.operationCompositeFieldTypesInhabited_of_schema

end GraphQL.Tests.ExecutionReadiness.SchemaConstraints
