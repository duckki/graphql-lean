import GraphQL.Validation

/-! Well-formedness of GraphQL schemas
Spec reference: GraphQL September 2025.
- 3.3 Schema and 3.4-3.12 Type System validation: this file separates raw schema syntax
  from schema well-formedness predicates. The spec describes these as validation rules;
  this module names the resulting schema invariants `WellFormed`.
- 3.6-3.10 Object, Interface, Union, Enum, and Input Object validation: modeled partially,
  covering uniqueness, non-empty member/field lists, default-value validity, and
  object/interface field implementation compatibility.
-- Fidelity note: several normative rules are omitted, including reserved `__` names,
  interface cycles, directive validation, extensions,
  OneOf, mutation/subscription roots, and introspection.
-/

namespace GraphQL

namespace SchemaWellFormedness

-- Spec 3.6-3.10 type validation repeatedly requires non-empty definition/member lists.
def listNonempty {α : Type} (values : List α) : Prop :=
  values ≠ []

-- Spec type-system uniqueness clauses: faithful as a generic list-level no-duplicates
-- predicate.
def namesAreUnique (names : List Name) : Prop :=
  names.Nodup

-- Spec 3.6.1 / 3.10 input value definition rules: partial; checks `IsInputType` and
-- constant default validity, omitting directive/name rules and full scalar coercion.
def inputValueDefinitionWellFormed (schema : Schema) (definition : InputValueDefinition)
    : Prop :=
  definition.inputType.isInputType schema
  ∧ match definition.defaultValue with
    | none => True
    | some defaultValue => defaultValue.isCorrectType schema definition.inputType

-- Spec 3.6.1 / 3.10 input value definition lists: names are unique and every definition
-- has an input type and valid default when present. Empty field argument lists are valid.
def inputValueDefinitionsWellFormed (schema : Schema)
    (definitions : List InputValueDefinition)
    : Prop :=
  namesAreUnique (definitions.map InputValueDefinition.name)
  ∧ ∀ definition,
      definition ∈ definitions -> inputValueDefinitionWellFormed schema definition

-- Spec 3.6 field definition rules: partial; checks output type and argument definitions,
-- omitting reserved names, descriptions, directives, and deprecation-specific rules.
def fieldDefinitionWellFormed (schema : Schema) (field : FieldDefinition) : Prop :=
  field.outputType.isOutputType schema
  ∧ inputValueDefinitionsWellFormed schema field.arguments

-- Spec 3.6 / 3.7 output field lists must be non-empty, uniquely named, and individually
-- well-formed. Field argument lists themselves may be empty.
def fieldDefinitionsWellFormed (schema : Schema) (fields : List FieldDefinition) : Prop :=
  listNonempty fields
  ∧ namesAreUnique (fields.map FieldDefinition.name)
  ∧ ∀ field, field ∈ fields -> fieldDefinitionWellFormed schema field

-- Spec 3.6 / 3.7 field implementation argument rules: inherited arguments must exist
-- with the same input type; additional implementation arguments must not be required.
def argumentDefinitionsImplement (implementation expected : List InputValueDefinition)
    : Prop :=
  (∀ expectedDefinition,
    expectedDefinition ∈ expected
    -> ∃ implementationDefinition,
        Schema.lookupArgumentDefinition implementation expectedDefinition.name
          = some implementationDefinition
        ∧ implementationDefinition.inputType = expectedDefinition.inputType)
  ∧ (∀ implementationDefinition,
      implementationDefinition ∈ implementation
      -> Schema.lookupArgumentDefinition expected implementationDefinition.name = none
      -> ¬ implementationDefinition.isRequired)

-- Spec 3.6 / 3.7 field implementation rules: return type is covariant and arguments
-- are compatible.
def fieldDefinitionImplements (schema : Schema)
    (implementation expected : FieldDefinition)
    : Prop :=
  schema.outputTypeSubtype implementation.outputType expected.outputType
  ∧ argumentDefinitionsImplement implementation.arguments expected.arguments

-- Spec 3.6 / 3.7 object/interface implementation rules: every interface field must be
-- implemented by name with compatible type and arguments.
def fieldsImplementInterface (schema : Schema)
    (implementationFields : List FieldDefinition) (interfaceName : Name)
    : Prop :=
  ∃ interfaceType,
    schema.lookupInterface interfaceName = some interfaceType
    ∧ ∀ interfaceField,
        interfaceField ∈ interfaceType.fields
        -> ∃ implementationField,
            Schema.lookupFieldDefinition implementationFields interfaceField.name
              = some implementationField
            ∧ fieldDefinitionImplements schema implementationField interfaceField

-- Spec 3.6 object type rules: checks non-empty fields, declared interface existence,
-- and interface field implementation compatibility.
def objectTypeWellFormed (schema : Schema) (objectType : ObjectType) : Prop :=
  fieldDefinitionsWellFormed schema objectType.fields
  ∧ namesAreUnique objectType.interfaces
  ∧ ∀ interfaceName,
      interfaceName ∈ objectType.interfaces
      -> fieldsImplementInterface schema objectType.fields interfaceName

-- Spec 3.7 interface type rules: checks non-empty fields, declared interface existence,
-- and interface field implementation compatibility, but not cycles.
def interfaceTypeWellFormed (schema : Schema) (interfaceType : InterfaceType) : Prop :=
  fieldDefinitionsWellFormed schema interfaceType.fields
  ∧ namesAreUnique interfaceType.interfaces
  ∧ ∀ implementedInterfaceName,
      implementedInterfaceName ∈ interfaceType.interfaces
      -> fieldsImplementInterface schema interfaceType.fields implementedInterfaceName

-- Spec 3.8 union type rules: checks non-empty unique object members; directives and
-- extensions are out of scope.
def unionTypeWellFormed (schema : Schema) (unionType : UnionType) : Prop :=
  listNonempty unionType.members
  ∧ namesAreUnique unionType.members
  ∧ ∀ objectName, objectName ∈ unionType.members -> schema.objectType objectName

-- Spec 3.9 enum type rules: checks non-empty unique values but omits reserved names,
-- directives, and deprecation rules.
def enumTypeWellFormed (enumType : EnumType) : Prop :=
  listNonempty enumType.values ∧ namesAreUnique enumType.values

-- Spec 3.10 input object type rules: checks non-empty input field definitions but omits
-- OneOf rules.
def inputObjectTypeWellFormed (schema : Schema) (inputObjectType : InputObjectType)
    : Prop :=
  listNonempty inputObjectType.inputFields
  ∧ inputValueDefinitionsWellFormed schema inputObjectType.inputFields

-- Spec 3.10 circular-reference rule: only an unbroken chain of singular non-null input
-- object fields is forbidden. Nullable and list fields deliberately break the chain, so
-- schemas may still represent finite recursive input values.
private def nonNullSingularInputObjectTarget? (inputType : TypeRef) : Option Name :=
  match inputType with
  | .nonNull (.named target) => some target
  | _ => none

private def inputObjectHasNonNullSingularCycleFrom (schema : Schema)
    : Nat -> List Name -> Name -> Bool
  | 0, _visited, _current => false
  | fuel + 1, visited, current =>
      if visited.contains current then
        true
      else
        match schema.lookupInputObject current with
        | none => false
        | some inputObject =>
            inputObject.inputFields.any
              fun field =>
                match nonNullSingularInputObjectTarget? field.inputType with
                | none => false
                | some target =>
                    inputObjectHasNonNullSingularCycleFrom schema fuel
                      (current :: visited) target

def inputObjectNonNullSingularCircularReferencesValidBool (schema : Schema) : Bool :=
  (schema.types.filterMap
    fun typeDefinition =>
      match typeDefinition with
      | .inputObject inputObject => some inputObject.name
      | _ => none).all
    fun inputObjectName =>
      !(inputObjectHasNonNullSingularCycleFrom schema (schema.types.length + 1) []
          inputObjectName)

def inputObjectNonNullSingularCircularReferencesValid (schema : Schema) : Prop :=
  inputObjectNonNullSingularCircularReferencesValidBool schema = true

mutual
  private def constInputValueSize : ConstInputValue -> Nat
    | .null | .int _ | .float _ | .string _ | .boolean _ | .enum _ => 1
    | .list values => 1 + constInputValueListSize values
    | .object fields => 1 + constInputValueFieldSize fields

  private def constInputValueListSize : List ConstInputValue -> Nat
    | [] => 0
    | value :: values => constInputValueSize value + constInputValueListSize values

  private def constInputValueFieldSize : List (Name × ConstInputValue) -> Nat
    | [] => 0
    | (_, value) :: fields => constInputValueSize value + constInputValueFieldSize fields
end

-- The bound covers every schema default's finite syntax tree plus every input-object
-- field. It bounds traversal of defaults, not the depth of supplied runtime input.
private def inputObjectDefaultExpansionFuel (schema : Schema) : Nat :=
  schema.types.foldr
    (fun typeDefinition fuel =>
      match typeDefinition with
      | .inputObject inputObject =>
          inputObject.inputFields.foldr
            (fun field fuel =>
              1
              + (match field.defaultValue with
                  | none => 0
                  | some value => constInputValueSize value)
              + fuel)
            fuel
      | _ => fuel)
    1

-- Spec 3.10 `InputObjectDefaultValueHasCycle`: supplied object entries take precedence;
-- absent entries follow their field default. Re-visiting a defaulted input field is the
-- cycle witness. The fuel makes this executable on arbitrary raw schemas.
private def inputObjectDefaultValueHasCycleWithFuel (schema : Schema)
    : Nat -> InputObjectType -> ConstInputValue -> List (Name × Name) -> Bool
  | 0, _inputObject, _value, _visited => false
  | fuel + 1, inputObject, value, visited =>
      match value with
      | .list values =>
          values.any
            fun value =>
              inputObjectDefaultValueHasCycleWithFuel schema fuel inputObject value
                visited
      | .object fields =>
          inputObject.inputFields.any
            fun field =>
              match schema.lookupInputObject field.inputType.namedType with
              | none => false
              | some fieldInputObject =>
                  match Schema.getConstInputObjectField? fields field.name,
                        field.defaultValue with
                  | some fieldValue, _ =>
                      inputObjectDefaultValueHasCycleWithFuel schema fuel fieldInputObject
                        fieldValue visited
                  | none, some defaultValue =>
                      let coordinate := (inputObject.name, field.name)
                      if visited.contains coordinate then
                        true
                      else
                        inputObjectDefaultValueHasCycleWithFuel schema fuel
                          fieldInputObject defaultValue (coordinate :: visited)
                  | none, none => false
      | _ => false

def inputObjectDefaultValueHasCycle (schema : Schema) (inputObject : InputObjectType)
    : Bool :=
  inputObjectDefaultValueHasCycleWithFuel schema (inputObjectDefaultExpansionFuel schema)
    inputObject (.object []) []

-- Spec 3.10 requires every input object to be free of default-expansion cycles. This
-- establishes `inputDefaultExpansionAcyclic`; it does not bound finite user values that
-- use nullable or list recursive fields.
def inputDefaultExpansionAcyclicBool (schema : Schema) : Bool :=
  (schema.types.filterMap
    fun typeDefinition =>
      match typeDefinition with
      | .inputObject inputObject => some inputObject
      | _ => none).all
    fun inputObject =>
      !(inputObjectDefaultValueHasCycle schema inputObject)

def inputDefaultExpansionAcyclic (schema : Schema) : Prop :=
  inputDefaultExpansionAcyclicBool schema = true

-- Spec 3.10 input-object circular-reference validation.
def inputObjectCircularReferencesValid (schema : Schema) : Prop :=
  inputObjectNonNullSingularCircularReferencesValid schema
  ∧ inputDefaultExpansionAcyclic schema

-- Spec 3.4-3.10 type well-formedness dispatcher: partial in the same ways as the
-- per-type predicates.
def typeDefinitionWellFormed (schema : Schema) : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .object objectType => objectTypeWellFormed schema objectType
  | .interface interfaceType => interfaceTypeWellFormed schema interfaceType
  | .union unionType => unionTypeWellFormed schema unionType
  | .enum enumType => enumTypeWellFormed enumType
  | .inputObject inputObjectType => inputObjectTypeWellFormed schema inputObjectType

-- Proof-facing schema invariant: possible runtime object fields are compatible with
-- fields selected through their static parent type. This is the field-level bridge
-- needed when execution grounds abstract parents to concrete object sources.
def possibleObjectFieldDefinitionsImplement (schema : Schema) : Prop :=
  ∀ parentType objectTypeName fieldName expected,
    objectTypeName ∈ schema.getPossibleTypes parentType
    -> schema.lookupField parentType fieldName = some expected
    -> ∃ implementation,
        schema.lookupField objectTypeName fieldName = some implementation
        ∧ fieldDefinitionImplements schema implementation expected
        ∧ FieldMerge.sameResponseShape schema
            implementation.outputType expected.outputType

-- Spec 3.3 schema rules: partial; checks unique type names and a query object root,
-- omitting operation-type uniqueness/existence for mutation/subscription and directive
-- validation.
def schemaWellFormed (schema : Schema) : Prop :=
  namesAreUnique (schema.allTypes.map TypeDefinition.name)
  ∧ schema.objectType schema.queryType
  ∧ (∀ typeDefinition,
      typeDefinition ∈ schema.types -> typeDefinitionWellFormed schema typeDefinition)
  ∧ inputObjectCircularReferencesValid schema
  ∧ (∀ typeName objectTypeName,
      objectTypeName ∈ schema.getPossibleTypes typeName
      -> schema.objectType objectTypeName)
  ∧ (∀ typeName, (schema.getPossibleTypes typeName).Nodup)
  ∧ possibleObjectFieldDefinitionsImplement schema

-- Spec-conformance pattern, not a GraphQL spec definition: bundles a schema with this
-- file's partial well-formedness proof.
structure WellFormedSchema where
  schema : Schema
  wellFormed : schemaWellFormed schema

end SchemaWellFormedness

end GraphQL
