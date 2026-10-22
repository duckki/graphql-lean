import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes

namespace GraphQL.Tests.SchemaWellFormedness.OutputCovariance

open GraphQL.SchemaWellFormedness

def valueField (output : TypeRef) : FieldDefinition :=
  { name := "value", outputType := output }

def interfaceType (expected : TypeRef) : InterfaceType :=
  { name := "I", fields := [valueField expected] }

def queryType (implementation : TypeRef) : ObjectType :=
  {
    name := "Query"
    interfaces := ["I"]
    fields :=
      [
        valueField implementation,
        { name := "node", outputType := .named "I" },
        { name := "safe", outputType := .named "String" }
      ]
  }

def plainType (expected : TypeRef) : ObjectType :=
  { name := "Plain", interfaces := ["I"], fields := [valueField expected] }

def schema (expected implementation : TypeRef) : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .interface (interfaceType expected),
        .object (queryType implementation),
        .object (plainType expected)
      ]
  }

attribute [local simp]
  schema valueField interfaceType queryType plainType
  Schema.lookupType Schema.allTypes Schema.builtinScalarDefinitions
  TypeDefinition.name TypeDefinition.fields? BuiltinScalar.name

private theorem outputSubtype_refl {schema : Schema} (type : TypeRef)
    (houtput : type.isOutputType schema)
    : schema.outputTypeSubtype type type := by
  induction type with
  | named name => exact ⟨houtput, houtput, Or.inl rfl⟩
  | list inner ih => exact ih houtput
  | nonNull inner ih =>
      exact ih (by cases inner <;> simp_all [TypeRef.isOutputType])

theorem possibleTypes (expected implementation : TypeRef) (parent : Name)
    : (schema expected implementation).getPossibleTypes parent
      = if parent = "I" then
          ["Query", "Plain"]
        else if parent = "Query" then
          ["Query"]
        else if parent = "Plain" then
          ["Plain"]
        else
          [] := by
  by_cases hI : parent = "I"
  · subst parent; rfl
  by_cases hQ : parent = "Query"
  · subst parent; rfl
  by_cases hP : parent = "Plain"
  · subst parent; rfl
  simp [Schema.getPossibleTypes, hI, hQ, hP, beq_iff_eq, Ne.symm hI,
    Ne.symm hQ, Ne.symm hP]

private theorem wellFormed (expected implementation : TypeRef)
    (hexpected : expected.isOutputType (schema expected implementation))
    (himplementation : implementation.isOutputType (schema expected implementation))
    (hsubtype
      : (schema expected implementation).outputTypeSubtype implementation expected)
    : schemaWellFormed (schema expected implementation) := by
  have hidentity := outputSubtype_refl expected hexpected
  have hi : (TypeRef.named "I").isOutputType (schema expected implementation) :=
    ⟨.interface (interfaceType expected), rfl, trivial⟩
  have hs : (TypeRef.named "String").isOutputType (schema expected implementation) :=
    ⟨.builtinScalar .string, rfl, trivial⟩
  have htypes : ∀ definition ∈ (schema expected implementation).types,
      typeDefinitionWellFormed (schema expected implementation) definition := by
    intro definition hdefinition
    simp only [schema, List.mem_cons, List.not_mem_nil, or_false] at hdefinition
    rcases hdefinition with rfl | rfl | rfl <;>
      simp_all [typeDefinitionWellFormed, interfaceTypeWellFormed, objectTypeWellFormed,
        interfacesIncludeInherited,
        fieldDefinitionsWellFormed, fieldDefinitionWellFormed, inputValueDefinitionsWellFormed,
        fieldsImplementInterface, fieldDefinitionImplements, argumentDefinitionsImplement,
        Schema.lookupInterface, Schema.lookupFieldDefinition, namesAreUnique, listNonempty]
  refine ⟨
    by simp [namesAreUnique],
    ⟨queryType implementation, rfl⟩,
    htypes,
    ⟨by rfl, by rfl⟩,
    ?_,
    ?_,
    ?_
  ⟩
  · intro parent object hobject
    rw [possibleTypes] at hobject
    split at hobject
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hobject
      rcases hobject with rfl | rfl
      · exact ⟨queryType implementation, rfl⟩
      · exact ⟨plainType expected, rfl⟩
    · split at hobject
      · have : object = "Query" := by simpa using hobject
        subst object
        exact ⟨queryType implementation, rfl⟩
      · split at hobject
        · have : object = "Plain" := by simpa using hobject
          subst object
          exact ⟨plainType expected, rfl⟩
        · cases hobject
  · intro parent
    rw [possibleTypes]
    split <;> (try split) <;> (try split) <;> decide
  · intro parent object field expectedField hpossible hlookup
    rw [possibleTypes] at hpossible
    by_cases hI : parent = "I"
    · subst parent
      simp only [ite_eq_left, List.mem_cons, List.not_mem_nil, or_false] at hpossible
      have hfield : "value" = field ∧ valueField expected = expectedField := by
        simpa [Schema.lookupField] using hlookup
      rcases hfield with ⟨rfl, rfl⟩
      rcases hpossible with rfl | rfl
      · exact ⟨valueField implementation, rfl, hsubtype,
          by simp [argumentDefinitionsImplement]⟩
      · exact ⟨valueField expected, rfl, hidentity, by simp [argumentDefinitionsImplement]⟩
    by_cases hQ : parent = "Query"
    · subst parent
      have hobject : object = "Query" := by simpa using hpossible
      subst object
      by_cases hv : field = "value"
      · subst field
        have hfield : valueField implementation = expectedField := by
          simpa [Schema.lookupField] using hlookup
        subst expectedField
        exact ⟨
          valueField implementation,
          rfl,
          outputSubtype_refl _ himplementation,
          by simp [argumentDefinitionsImplement]
        ⟩
      by_cases hn : field = "node"
      · subst field
        have hfield : ({ name := "node", outputType := .named "I" } : FieldDefinition)
            = expectedField := by simpa [Schema.lookupField] using hlookup
        subst expectedField
        exact ⟨_, rfl, outputSubtype_refl _ hi, by simp [argumentDefinitionsImplement]⟩
      by_cases hf : field = "safe"
      · subst field
        have hfield : ({ name := "safe", outputType := .named "String" } : FieldDefinition)
            = expectedField := by simpa [Schema.lookupField] using hlookup
        subst expectedField
        exact ⟨_, rfl, outputSubtype_refl _ hs, by simp [argumentDefinitionsImplement]⟩
      simp [Schema.lookupField, beq_iff_eq, Ne.symm hv, Ne.symm hn, Ne.symm hf] at hlookup
    by_cases hP : parent = "Plain"
    · subst parent
      have hobject : object = "Plain" := by simpa using hpossible
      subst object
      have hfield : "value" = field ∧ valueField expected = expectedField := by
        simpa [Schema.lookupField] using hlookup
      rcases hfield with ⟨rfl, rfl⟩
      exact ⟨valueField expected, rfl, hidentity, by simp [argumentDefinitionsImplement]⟩
    simp [hI, hQ, hP] at hpossible

theorem nonNullStrengthening_accepted
    : schemaWellFormed (schema (.named "String") (.nonNull (.named "String"))) := by
  apply wellFormed <;>
    simp [TypeRef.isOutputType, Schema.isOutputType, TypeDefinition.isOutputType,
      Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isSubType]

theorem listItemStrengthening_accepted
    : schemaWellFormed
        (schema (.list (.named "String")) (.list (.nonNull (.named "String")))) := by
  apply wellFormed <;>
    simp [TypeRef.isOutputType, Schema.isOutputType, TypeDefinition.isOutputType,
      Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isSubType]

theorem listAndItemStrengthening_accepted
    : schemaWellFormed
        (schema (.list (.named "String"))
          (.nonNull (.list (.nonNull (.named "String"))))) := by
  apply wellFormed <;>
    simp [TypeRef.isOutputType, Schema.isOutputType, TypeDefinition.isOutputType,
      Schema.outputTypeSubtype, Schema.namedOutputTypeSubtype, Schema.isSubType]

theorem nonNullWeakening_rejected
    : ¬ schemaWellFormed (schema (.nonNull (.named "String")) (.named "String")) := by
  intro hschema
  have hsubtype := schemaWellFormed_possibleObject_lookupField_outputTypeSubtype hschema
    (parentType := "I") (objectTypeName := "Query") (fieldName := "value")
    (by decide) (by rfl) (by rfl)
  exact hsubtype

theorem listShapeMismatch_rejected
    : ¬ schemaWellFormed (schema (.list (.named "String")) (.named "String")) := by
  intro hschema
  have hsubtype := schemaWellFormed_possibleObject_lookupField_outputTypeSubtype hschema
    (parentType := "I") (objectTypeName := "Query") (fieldName := "value")
    (by decide) (by rfl) (by rfl)
  exact hsubtype

end GraphQL.Tests.SchemaWellFormedness.OutputCovariance
