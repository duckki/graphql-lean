/-! GraphQL schema representation
Spec reference: GraphQL September 2025.
- 2.1.8 Names: names identify schema and executable elements; this model stores raw
  strings and leaves grammar/reserved-name checks to well-formedness/validation work.
- 2.10 Input Values and 2.12 Type References: value and type-reference syntax are
  represented directly, constant values are separated for defaults, and coercion/source
  parsing are out of scope.
- 2.14 Schema Coordinates are not modeled; this formalization has no source-level
  coordinate syntax or introspection surface.
- 3.3-3.13 Type System: schema and type definitions cover core GraphQL types, wrapping
  types, built-in scalars, and the `@skip`/`@include` scalar dependencies, but omit
  descriptions, arbitrary directives, extensions, introspection, mutation/subscription
  roots, and OneOf metadata.
- 5.5.2.3 Fragment Spread Is Possible: possible-object helpers model the spec's
  `GetPossibleTypes` basis for overlap checks.
-/

namespace GraphQL

-- Type-directed notation for syntactic equivalence. Modules add instances for syntax
-- relations they own; the underlying declarations retain descriptive, searchable names.
class SyntacticEquivalence (α : Type u) where
  equivalent : α -> α -> Prop

namespace SyntacticEquivalence

scoped infix:50 " ≡ " => SyntacticEquivalence.equivalent

end SyntacticEquivalence

-- Type-directed notation for semantic equivalence. Unlike `=`, instances may identify
-- observably identical values with different structural representations.
class SemanticEquivalence (α : Type u) where
  equivalent : α -> α -> Prop

namespace SemanticEquivalence

scoped infix:50 " ≈ " => SemanticEquivalence.equivalent

end SemanticEquivalence

-- Spec 2.1.8 `Name`: partial; raw `String` does not enforce the GraphQL name grammar or
-- reserved `__` rules.
abbrev Name := String

-- Spec 2.10 `Value`: partial; literals and variables are represented, but
-- constant-vs-variable contexts and input coercion are handled elsewhere or omitted.
inductive InputValue where
  | null
  | int (value : Int)
  | float (value : String)
  | string (value : String)
  | boolean (value : Bool)
  | enum (value : Name)
  | list (values : List InputValue)
  | object (fields : List (Name × InputValue))
  | variable (name : Name)
deriving Repr

namespace InputValue

def insertObjectFieldSorted (field : Name × InputValue)
    : List (Name × InputValue) -> List (Name × InputValue)
  | [] => [field]
  | candidate :: rest =>
      if field.1 <= candidate.1 then
        field :: candidate :: rest
      else
        candidate :: insertObjectFieldSorted field rest

def sortObjectFieldsByName : List (Name × InputValue) -> List (Name × InputValue)
  | [] => []
  | field :: rest =>
      insertObjectFieldSorted field (sortObjectFieldsByName rest)

mutual
  def canonical : InputValue -> InputValue
    | .null => .null
    | .int value => .int value
    | .float value => .float value
    | .string value => .string value
    | .boolean value => .boolean value
    | .enum value => .enum value
    | .variable name => .variable name
    | .list values => .list (canonicalValues values)
    | .object fields =>
        .object (sortObjectFieldsByName (canonicalObjectFields fields))

  def canonicalValues : List InputValue -> List InputValue
    | [] => []
    | value :: rest =>
        canonical value :: canonicalValues rest

  def canonicalObjectFields : List (Name × InputValue) -> List (Name × InputValue)
    | [] => []
    | (name, value) :: rest =>
        (name, canonical value) :: canonicalObjectFields rest
end

mutual
  -- Spec 2.10 input value equality for semantic analysis: list order matters, object field
  -- order does not. Validation is responsible for rejecting duplicate input object fields.
  def structuralEquivalent : InputValue -> InputValue -> Prop
    | .null, .null => True
    | .int left, .int right => left = right
    | .float left, .float right => left = right
    | .string left, .string right => left = right
    | .boolean left, .boolean right => left = right
    | .enum left, .enum right => left = right
    | .variable left, .variable right => left = right
    | .list left, .list right => structuralValuesEquivalent left right
    | .object left, .object right => structuralObjectFieldsEquivalent left right
    | _left, _right => False

  def structuralValuesEquivalent : List InputValue -> List InputValue -> Prop
    | [], [] => True
    | left :: lefts, right :: rights =>
        structuralEquivalent left right ∧ structuralValuesEquivalent lefts rights
    | _left, _right => False

  def structuralObjectFieldsEquivalent
      : List (Name × InputValue) -> List (Name × InputValue) -> Prop
    | [], [] => True
    | (leftName, leftValue) :: lefts,
      (rightName, rightValue) :: rights =>
        leftName = rightName
        ∧ structuralEquivalent leftValue rightValue
        ∧ structuralObjectFieldsEquivalent lefts rights
    | _left, _right => False
end

mutual
  def decideStructuralEquivalent (left right : InputValue)
      : Decidable (structuralEquivalent left right) := by
    cases left <;> cases right <;> simp only [structuralEquivalent]
    all_goals
      first
      | exact decideStructuralValuesEquivalent _ _
      | exact decideStructuralObjectFieldsEquivalent _ _
      | infer_instance

  def decideStructuralValuesEquivalent
      : (left right : List InputValue)
        -> Decidable (structuralValuesEquivalent left right)
    | [], [] => isTrue trivial
    | left :: lefts, right :: rights =>
        match decideStructuralEquivalent left right,
              decideStructuralValuesEquivalent lefts rights with
        | isTrue hleft, isTrue hrest => isTrue ⟨hleft, hrest⟩
        | isFalse hleft, _ => isFalse fun h => hleft h.1
        | _, isFalse hrest => isFalse fun h => hrest h.2
    | [], _right :: _rights => isFalse id
    | _left :: _lefts, [] => isFalse id

  def decideStructuralObjectFieldsEquivalent
      : (left right : List (Name × InputValue))
        -> Decidable (structuralObjectFieldsEquivalent left right)
    | [], [] => isTrue trivial
    | (leftName, leftValue) :: lefts, (rightName, rightValue) :: rights =>
        match inferInstanceAs (Decidable (leftName = rightName)),
              decideStructuralEquivalent leftValue rightValue,
              decideStructuralObjectFieldsEquivalent lefts rights with
        | isTrue hname, isTrue hvalue, isTrue hrest =>
            isTrue ⟨hname, hvalue, hrest⟩
        | isFalse hname, _, _ => isFalse fun h => hname h.1
        | _, isFalse hvalue, _ => isFalse fun h => hvalue h.2.1
        | _, _, isFalse hrest => isFalse fun h => hrest h.2.2
    | [], _right :: _rights => isFalse id
    | _left :: _lefts, [] => isFalse id
end

instance structuralEquivalentDecidable : DecidableRel structuralEquivalent :=
  decideStructuralEquivalent

instance structuralValuesEquivalentDecidable : DecidableRel structuralValuesEquivalent :=
  decideStructuralValuesEquivalent

instance structuralObjectFieldsEquivalentDecidable
    : DecidableRel structuralObjectFieldsEquivalent :=
  decideStructuralObjectFieldsEquivalent

-- Computable views of the corresponding propositions. Their implementations are
-- supplied by the reusable decision procedures above.
def structuralEquivalentBool (left right : InputValue) : Bool :=
  decide (structuralEquivalent left right)

def structuralValuesEquivalentBool (left right : List InputValue) : Bool :=
  decide (structuralValuesEquivalent left right)

def structuralObjectFieldsEquivalentBool (left right : List (Name × InputValue)) : Bool :=
  decide (structuralObjectFieldsEquivalent left right)

def equivalent (left right : InputValue) : Prop :=
  structuralEquivalent left.canonical right.canonical

instance syntacticallyEquivalentDecidable : DecidableRel equivalent :=
  fun left right =>
    inferInstanceAs (Decidable (structuralEquivalent left.canonical right.canonical))

instance syntacticEquivalence : SyntacticEquivalence InputValue where
  equivalent := equivalent

instance syntacticEquivalenceNotationDecidable (left right : InputValue)
    : Decidable (SyntacticEquivalence.equivalent left right) := by
  change Decidable (equivalent left right)
  infer_instance

-- Computable syntactic input-value equivalence. List order matters; input object field
-- order does not. Duplicate input object fields remain a validation concern.
def syntacticallyEquivalentBool (left right : InputValue) : Bool :=
  decide (equivalent left right)

-- Spec 2.10 input object field equality for semantic argument comparison; object field
-- order is ignored, with duplicate rejection delegated to validation.
def objectFieldsEquivalent (left right : List (Name × InputValue)) : Prop :=
  structuralObjectFieldsEquivalent
    (sortObjectFieldsByName (canonicalObjectFields left))
    (sortObjectFieldsByName (canonicalObjectFields right))

-- Spec 3.13.1 `@skip` / 3.13.2 `@include` `if` argument: partial; this only recognizes
-- statically provided Boolean literals.
def staticBoolean? : InputValue -> Option Bool
  | .boolean value => some value
  | _ => none

-- Spec 2.10 input value helper: recognizes an explicit `null` literal after variable
-- substitution.
def isNull : InputValue -> Bool
  | .null => true
  | _ => false

end InputValue

-- Spec 2.10 `Value Const`: default values must be constant and therefore exclude
-- variables. Coercion and literal scalar semantics remain out of scope; structural
-- default conformance is checked by schema well-formedness.
inductive ConstInputValue where
  | null
  | int (value : Int)
  | float (value : String)
  | string (value : String)
  | boolean (value : Bool)
  | enum (value : Name)
  | list (values : List ConstInputValue)
  | object (fields : List (Name × ConstInputValue))
deriving Repr

namespace ConstInputValue

-- Spec 5.4.3 / 5.6.4 helper: null does not satisfy a required input entry.
def nonNull : ConstInputValue -> Prop
  | .null => False
  | _ => True

mutual
  -- Non-spec embedding from constant values into the general input-value syntax.
  def toInputValue : ConstInputValue -> InputValue
    | .null => .null
    | .int value => .int value
    | .float value => .float value
    | .string value => .string value
    | .boolean value => .boolean value
    | .enum value => .enum value
    | .list values => .list (valuesToInputValues values)
    | .object fields => .object (objectFieldsToInputFields fields)

  def valuesToInputValues : List ConstInputValue -> List InputValue
    | [] => []
    | value :: rest => value.toInputValue :: valuesToInputValues rest

  def objectFieldsToInputFields
      : List (Name × ConstInputValue) -> List (Name × InputValue)
    | [] => []
    | (name, value) :: rest =>
        (name, value.toInputValue) :: objectFieldsToInputFields rest
end

mutual
  -- Runtime input values use the constant-value grammar because executable variable
  -- references have already been resolved. This partial inverse rejects any residual
  -- variable reference, including one nested in a list or input object.
  def ofInputValue? : InputValue -> Option ConstInputValue
    | .null => some .null
    | .int value => some (.int value)
    | .float value => some (.float value)
    | .string value => some (.string value)
    | .boolean value => some (.boolean value)
    | .enum value => some (.enum value)
    | .variable _name => none
    | .list values => do
        return .list (← inputValuesToConstInputValues? values)
    | .object fields => do
        return .object (← inputFieldsToConstInputFields? fields)

  def inputValuesToConstInputValues? : List InputValue -> Option (List ConstInputValue)
    | [] => some []
    | value :: rest => do
        return (← ofInputValue? value) :: (← inputValuesToConstInputValues? rest)

  def inputFieldsToConstInputFields?
      : List (Name × InputValue) -> Option (List (Name × ConstInputValue))
    | [] => some []
    | (name, value) :: rest => do
        return (name, ← ofInputValue? value) :: (← inputFieldsToConstInputFields? rest)
end

end ConstInputValue

-- Spec 2.12 `Type`, `NamedType`, `ListType`, `NonNullType`: partial; syntax is
-- represented, and invalid nested non-null is rejected by `TypeRef.wellFormed` and
-- input/output type predicates rather than by construction.
inductive TypeRef where
  | named : Name -> TypeRef
  | list : TypeRef -> TypeRef
  | nonNull : TypeRef -> TypeRef
deriving Repr, DecidableEq

namespace TypeRef

-- Spec 2.12 Type reference semantics: faithful for retrieving the underlying named type
-- of modeled wrapping references.
def namedType : TypeRef -> Name
  | .named name => name
  | .list inner => inner.namedType
  | .nonNull inner => inner.namedType

-- Spec 2.12 type reference helper: only the outer wrapper is relevant for required
-- argument checks.
def isNonNull : TypeRef -> Bool
  | .nonNull _inner => true
  | _ => false

end TypeRef

-- Spec 3.5.1-3.5.5 built-in scalars: faithful for the five required scalar names, without
-- modeling coercion behavior.
inductive BuiltinScalar where
  | int
  | float
  | string
  | boolean
  | id
deriving Repr, DecidableEq

namespace BuiltinScalar

-- Spec 3.5.1-3.5.5 built-in scalar names: faithful.
def name : BuiltinScalar -> Name
  | .int => "Int"
  | .float => "Float"
  | .string => "String"
  | .boolean => "Boolean"
  | .id => "ID"

end BuiltinScalar

-- Spec 3.5 `ScalarTypeDefinition`: partial; custom scalar identity only, no description,
-- directives, specifiedBy URL, or coercion hooks.
structure CustomScalarType where
  name : Name
deriving Repr, DecidableEq

-- Spec 3.6.1 `InputValueDefinition` and 3.10 input fields: partial; name/type/default are
-- represented, but descriptions, directives, OneOf constraints, and value coercion are
-- omitted.
structure InputValueDefinition where
  name : Name
  inputType : TypeRef
  defaultValue : Option ConstInputValue := none
deriving Repr

namespace InputValueDefinition

-- Spec 5.4.3 / 5.6.4 required input entries: non-null type with no default.
def isRequired (definition : InputValueDefinition) : Prop :=
  match definition.inputType with
  | .nonNull _ => definition.defaultValue = none
  | _ => False

end InputValueDefinition

-- Spec 3.6 `FieldDefinition`: partial; name, return type, and arguments are represented,
-- but descriptions, directives, and deprecation are omitted.
structure FieldDefinition where
  name : Name
  outputType : TypeRef
  arguments : List InputValueDefinition := []
deriving Repr

-- Spec 3.6 `ObjectTypeDefinition`: partial; object fields and implemented interfaces are
-- represented, while descriptions, directives, extensions, and introspection fields are
-- omitted.
structure ObjectType where
  name : Name
  fields : List FieldDefinition
  interfaces : List Name := []
deriving Repr

-- Spec 3.7 `InterfaceTypeDefinition`: partial; fields and declared implemented interfaces
-- are represented, while descriptions, directives, extensions, and validation details are
-- omitted.
structure InterfaceType where
  name : Name
  fields : List FieldDefinition
  interfaces : List Name := []
deriving Repr

-- Spec 3.8 `UnionTypeDefinition`: partial; member object names are represented, but
-- descriptions, directives, extensions, and reserved-name validation are omitted.
structure UnionType where
  name : Name
  members : List Name
deriving Repr, DecidableEq

-- Spec 3.9 `EnumTypeDefinition`: partial; enum values are named but descriptions,
-- directives, deprecation, and reserved-name validation are omitted.
structure EnumType where
  name : Name
  values : List Name
deriving Repr, DecidableEq

-- Spec 3.10 `InputObjectTypeDefinition`: partial; input fields are represented, but
-- descriptions, directives, OneOf status, and extensions are omitted. Circular-reference
-- validation is expressed by `SchemaWellFormedness`.
structure InputObjectType where
  name : Name
  inputFields : List InputValueDefinition
deriving Repr

-- Spec 3.4 `TypeDefinition`: partial; core type categories are represented, but
-- type-system extensions, directive definitions, and introspection definitions are
-- outside this syntax.
inductive TypeDefinition where
  | builtinScalar : BuiltinScalar -> TypeDefinition
  | customScalar : CustomScalarType -> TypeDefinition
  | object : ObjectType -> TypeDefinition
  | interface : InterfaceType -> TypeDefinition
  | union : UnionType -> TypeDefinition
  | enum : EnumType -> TypeDefinition
  | inputObject : InputObjectType -> TypeDefinition
deriving Repr

namespace TypeDefinition

-- Spec 3.4 named type definitions: faithful for the modeled type categories.
def name : TypeDefinition -> Name
  | .builtinScalar scalar => scalar.name
  | .customScalar scalar => scalar.name
  | .object objectType => objectType.name
  | .interface interfaceType => interfaceType.name
  | .union unionType => unionType.name
  | .enum enumType => enumType.name
  | .inputObject inputObjectType => inputObjectType.name

-- Spec 5.3 field selection lookup applies only to object and interface definitions.
def fields? : TypeDefinition -> Option (List FieldDefinition)
  | .object objectType => some objectType.fields
  | .interface interfaceType => some interfaceType.fields
  | _ => none

-- Spec 5.3 field selection and 5.3.2 response-shape rules use the leaf type category;
-- faithful for scalar and enum definitions in the modeled type universe.
def isLeafType : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .enum _ => True
  | _ => False

-- Spec note in 5.3.2 and type-system usage of composite types: faithful for
-- object/interface/union in the modeled type universe.
def isCompositeType : TypeDefinition -> Prop
  | .object _ => True
  | .interface _ => True
  | .union _ => True
  | _ => False

-- Spec 3.4.2 `IsInputType`: faithful for the modeled named type categories.
def isInputType : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .enum _ => True
  | .inputObject _ => True
  | _ => False

-- Spec 3.4.2 `IsOutputType`: faithful for the modeled named type categories.
def isOutputType : TypeDefinition -> Prop
  | .builtinScalar _ => True
  | .customScalar _ => True
  | .object _ => True
  | .interface _ => True
  | .union _ => True
  | .enum _ => True
  | _ => False

end TypeDefinition

-- Spec 3.3 `Schema`: partial; only the query root and type list are modeled, omitting
-- mutation/subscription roots, directives, descriptions, extensions, and introspection.
structure Schema where
  queryType : Name
  types : List TypeDefinition
deriving Repr

namespace Schema

-- Spec 3.5 built-in scalar availability: faithful for adding the five required scalar
-- definitions to every modeled schema.
def builtinScalarDefinitions : List TypeDefinition :=
  [
    .builtinScalar .int,
    .builtinScalar .float,
    .builtinScalar .string,
    .builtinScalar .boolean,
    .builtinScalar .id
  ]

-- Spec 3.5 built-in scalar availability plus user-provided schema types.
def allTypes (schema : Schema) : List TypeDefinition :=
  builtinScalarDefinitions ++ schema.types

-- Spec type-system named type lookup over built-ins and explicit schema definitions.
def lookupType (schema : Schema) (typeName : Name) : Option TypeDefinition :=
  schema.allTypes.find? (fun typeDefinition => typeDefinition.name == typeName)

-- Spec object type lookup helper for schema validation and execution predicates.
def lookupObject (schema : Schema) (typeName : Name) : Option ObjectType := do
  match schema.lookupType typeName with
  | some (.object object) => some object
  | _ => none

-- Spec 3.10 input-object lookup helper for input/default validation.
def lookupInputObject (schema : Schema) (typeName : Name) : Option InputObjectType := do
  match schema.lookupType typeName with
  | some (.inputObject inputObject) => some inputObject
  | _ => none

-- Spec 3.7 interface lookup helper for implementation checks and possible types.
def lookupInterface (schema : Schema) (typeName : Name) : Option InterfaceType := do
  match schema.lookupType typeName with
  | some (.interface interfaceType) => some interfaceType
  | _ => none

-- Spec 3.6 / 3.7 interface implementation transitivity as proof-facing
-- reachability over declared interface inheritance.
inductive InterfaceTypeImplementsInterface (schema : Schema) : Name -> Name -> Prop where
  | refl (interfaceName : Name)
    : InterfaceTypeImplementsInterface schema interfaceName interfaceName
  | trans (interfaceName targetName : Name) (interfaceType : InterfaceType)
    (parentName : Name)
    (hlookup : schema.lookupInterface interfaceName = some interfaceType)
    (hparent : parentName ∈ interfaceType.interfaces)
    (himplements : InterfaceTypeImplementsInterface schema parentName targetName)
    : InterfaceTypeImplementsInterface schema interfaceName targetName

def interfaceTypeImplementsInterface (schema : Schema) (interfaceName targetName : Name)
    : Prop :=
  InterfaceTypeImplementsInterface schema interfaceName targetName

-- Boolean counterpart bounded for cyclic raw schema declarations.
def interfaceTypeImplementsInterfaceBoundedBool (schema : Schema)
    : Nat -> Name -> Name -> Bool
  | 0, _interfaceName, _targetName => false
  | bound + 1, interfaceName, targetName =>
      (interfaceName == targetName)
      || match schema.lookupInterface interfaceName with
          | some interfaceType =>
              interfaceType.interfaces.any
                (fun parentName =>
                  interfaceTypeImplementsInterfaceBoundedBool
                    schema bound parentName targetName)
          | none => false

def interfaceTypeImplementsInterfaceBool (schema : Schema)
    (interfaceName targetName : Name)
    : Bool :=
  interfaceTypeImplementsInterfaceBoundedBool
    schema (schema.types.length + 1) interfaceName targetName

-- Spec 3.6 object/interface relationship, including transitive interface inheritance.
def objectTypeImplementsInterface (schema : Schema)
    (objectType : ObjectType) (interfaceName : Name)
    : Prop :=
  ∃ declaredInterfaceName,
    declaredInterfaceName ∈ objectType.interfaces
    ∧ schema.interfaceTypeImplementsInterface declaredInterfaceName interfaceName

def objectTypeImplementsInterfaceBool (schema : Schema)
    (objectType : ObjectType) (interfaceName : Name)
    : Bool :=
  objectType.interfaces.any
    (fun declaredInterfaceName =>
      schema.interfaceTypeImplementsInterfaceBool declaredInterfaceName interfaceName)

-- Spec 5.5.2.3 `GetPossibleTypes` object universe: user-defined object types only.
def objectTypes (schema : Schema) : List ObjectType :=
  schema.types.filterMap
    (fun typeDefinition =>
      match typeDefinition with
      | .object objectType => some objectType
      | _ => none)

-- Spec 5.5.2.3 `GetPossibleTypes` interface case: objects implementing an interface.
def objectTypesImplementingInterface (schema : Schema) (interfaceName : Name)
    : List Name :=
  (schema.objectTypes.filter
    (fun objectType =>
      schema.objectTypeImplementsInterfaceBool objectType interfaceName)).map
    ObjectType.name

def lookupField (schema : Schema) (parentType fieldName : Name)
    : Option FieldDefinition := do
  let typeDefinition <- schema.lookupType parentType
  let fields <- typeDefinition.fields?
  fields.find? (fun field => field.name == fieldName)

-- Spec 5.4.1 argument definition lookup by name.
def lookupArgumentDefinition (definitions : List InputValueDefinition)
    (argumentName : Name)
    : Option InputValueDefinition :=
  definitions.find? (fun definition => definition.name == argumentName)

-- Spec 3.6 / 3.7 field implementation checks use field lookup by name.
def lookupFieldDefinition (definitions : List FieldDefinition) (fieldName : Name)
    : Option FieldDefinition :=
  definitions.find? (fun definition => definition.name == fieldName)

def fieldReturnType? (schema : Schema) (parentType fieldName : Name) : Option Name := do
  let field <- schema.lookupField parentType fieldName
  pure field.outputType.namedType

-- Spec 5.5.2.3 `GetPossibleTypes`: object and union cases are direct; interface cases are
-- derived from object type declarations in the schema.
def getPossibleTypes (schema : Schema) (typeName : Name) : List Name :=
  match schema.lookupType typeName with
  | some (.object objectType) => [objectType.name]
  | some (.interface interfaceType) =>
      schema.objectTypesImplementingInterface interfaceType.name
  | some (.union unionType) => unionType.members
  | _ => []

def typeIncludesObject (schema : Schema) (typeName objectName : Name) : Prop :=
  objectName ∈ schema.getPossibleTypes typeName

-- Boolean counterpart to `typeIncludesObject`.
def typeIncludesObjectBool (schema : Schema) (typeName objectName : Name) : Bool :=
  (schema.getPossibleTypes typeName).contains objectName

-- Spec 5.5.2.3 Fragment Spread Is Possible: faithful at the set-overlap level for modeled
-- possible-object lists.
def typesOverlap (schema : Schema) (left right : Name) : Prop :=
  ∃ objectName,
    schema.typeIncludesObject left objectName ∧ schema.typeIncludesObject right objectName

-- Boolean counterpart to `typesOverlap`.
def typesOverlapBool (schema : Schema) (left right : Name) : Bool :=
  (schema.getPossibleTypes left).any
    (fun objectName => schema.typeIncludesObjectBool right objectName)

-- Spec type-system named type existence helper.
def typeExists (schema : Schema) (typeName : Name) : Prop :=
  schema.lookupType typeName ≠ none

-- Spec object type category helper.
def objectType (schema : Schema) (typeName : Name) : Prop :=
  ∃ objectType, schema.lookupType typeName = some (.object objectType)

-- Spec interface type category helper.
def interfaceType (schema : Schema) (typeName : Name) : Prop :=
  ∃ interfaceType, schema.lookupType typeName = some (.interface interfaceType)

-- Spec 3.4.2 `IsInputType`: schema-level lookup wrapper for named types.
def isInputType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition ∧ typeDefinition.isInputType

-- Spec 3.4.2 `IsOutputType`: schema-level lookup wrapper for named types.
def isOutputType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition ∧ typeDefinition.isOutputType

-- Spec composite type category: schema-level lookup wrapper for object/interface/union.
def isCompositeType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition ∧ typeDefinition.isCompositeType

-- Spec leaf type category used by field validation and `SameResponseShape`: schema-level
-- lookup wrapper for scalar/enum types.
def isLeafType (schema : Schema) (typeName : Name) : Prop :=
  ∃ typeDefinition,
    schema.lookupType typeName = some typeDefinition ∧ typeDefinition.isLeafType

end Schema

namespace TypeRef

-- Local syntax invariant, not a named spec function: rejects a non-null wrapper around
-- another non-null wrapper as required by Spec 2.12 and 3.12 `NonNullType`.
def wellFormed : TypeRef -> Prop
  | .named _ => True
  | .list inner => inner.wellFormed
  | .nonNull (.nonNull _) => False
  | .nonNull inner => inner.wellFormed

-- Spec 3.4.2 `IsInputType`: faithful for the modeled type categories and wrapping-type
-- recursion.
def isInputType : TypeRef -> Schema -> Prop
  | .named name, schema => schema.isInputType name
  | .list inner, schema => inner.isInputType schema
  | .nonNull (.nonNull _), _schema => False
  | .nonNull inner, schema => inner.isInputType schema

-- Spec 3.4.2 `IsOutputType`: faithful for the modeled type categories and wrapping-type
-- recursion.
def isOutputType : TypeRef -> Schema -> Prop
  | .named name, schema => schema.isOutputType name
  | .list inner, schema => inner.isOutputType schema
  | .nonNull (.nonNull _), _schema => False
  | .nonNull inner, schema => inner.isOutputType schema

end TypeRef

namespace Schema

-- Spec 5.6.2 input object field lookup helper for constant/default validation.
def getConstInputObjectField? (fields : List (Name × ConstInputValue)) (name : Name)
    : Option ConstInputValue :=
  match fields with
  | [] => none
  | (fieldName, value) :: rest =>
      if fieldName = name then some value else getConstInputObjectField? rest name

mutual
  -- Spec 3.6.1 / 3.10 default-value validity: constants are checked against input
  -- object definitions recursively, while scalar coercion details remain out of scope.
  inductive ConstInputValueIsCorrectType (schema : Schema)
      : ConstInputValue -> TypeRef -> Prop where
    | nullNamed (typeName : Name) (hinput : (TypeRef.named typeName).isInputType schema)
      : ConstInputValueIsCorrectType schema ConstInputValue.null (TypeRef.named typeName)
    | nullList (inner : TypeRef) (hinput : (TypeRef.list inner).isInputType schema)
      : ConstInputValueIsCorrectType schema ConstInputValue.null (TypeRef.list inner)
    | nonNull (value : ConstInputValue) (inner : TypeRef)
      (hinput : (TypeRef.nonNull inner).isInputType schema)
      (hnotNull : value ≠ ConstInputValue.null)
      (hinner : ConstInputValueIsCorrectType schema value inner)
      : ConstInputValueIsCorrectType schema value (TypeRef.nonNull inner)
    | list (values : List ConstInputValue) (inner : TypeRef)
      (hinput : (TypeRef.list inner).isInputType schema)
      (hitems : ∀ item, item ∈ values -> ConstInputValueIsCorrectType schema item inner)
      : ConstInputValueIsCorrectType schema
          (ConstInputValue.list values) (TypeRef.list inner)
    | objectNamed (fields : List (Name × ConstInputValue)) (typeName : Name)
      (inputObject : InputObjectType)
      (hinput : (TypeRef.named typeName).isInputType schema)
      (hlookup : schema.lookupInputObject typeName = some inputObject)
      (hfields : ConstInputObjectFieldsValid schema inputObject.inputFields fields)
      : ConstInputValueIsCorrectType schema
          (ConstInputValue.object fields) (TypeRef.named typeName)
    | objectAsListItem (fields : List (Name × ConstInputValue)) (inner : TypeRef)
      (hinput : (TypeRef.list inner).isInputType schema)
      (hitem : ConstInputObjectAsListItemValid schema fields inner)
      : ConstInputValueIsCorrectType schema
          (ConstInputValue.object fields) (TypeRef.list inner)
    | singletonListItem (value : ConstInputValue) (inner : TypeRef)
      (hinput : (TypeRef.list inner).isInputType schema)
      (hnotList : ∀ values, value ≠ ConstInputValue.list values)
      (hnotObject : ∀ fields, value ≠ ConstInputValue.object fields)
      (hnotNull : value ≠ ConstInputValue.null)
      (hitem : ConstInputValueIsCorrectType schema value inner)
      : ConstInputValueIsCorrectType schema value (TypeRef.list inner)
    | namedNonInputObject (value : ConstInputValue) (typeName : Name)
      (hinput : (TypeRef.named typeName).isInputType schema)
      (hnotObject : ∀ fields, value ≠ ConstInputValue.object fields)
      (hnotNull : value ≠ ConstInputValue.null)
      (hlookup : schema.lookupInputObject typeName = none)
      : ConstInputValueIsCorrectType schema value (TypeRef.named typeName)

  -- Spec 3.6.1 / 3.10 default-value validity through 5.6.2-5.6.4 input object rules:
  -- object fields must be unique, known, correctly typed, and include required fields.
  inductive ConstInputObjectFieldsValid (schema : Schema)
      : List InputValueDefinition -> List (Name × ConstInputValue) -> Prop where
    | intro (definitions : List InputValueDefinition)
      (fields : List (Name × ConstInputValue))
      (hnodup : (fields.map Prod.fst).Nodup)
      (hknown
        : ∀ name value,
            (name, value) ∈ fields
            -> (Schema.lookupArgumentDefinition definitions name).isSome = true)
      (htyped
        : ∀ name value definition,
            (name, value) ∈ fields
            -> Schema.lookupArgumentDefinition definitions name = some definition
            -> ConstInputValueIsCorrectType schema value definition.inputType)
      (hrequiredPresent
        : ∀ definition,
            definition ∈ definitions
            -> definition.isRequired
            -> (getConstInputObjectField? fields definition.name).isSome = true)
      (hrequiredNonNull
        : ∀ definition value,
            definition ∈ definitions
            -> definition.isRequired
            -> getConstInputObjectField? fields definition.name = some value
            -> value.nonNull)
      : ConstInputObjectFieldsValid schema definitions fields

  -- Spec 5.6.1 list input rule analogue for constants: a non-list value can be checked
  -- as a single list item at a list location.
  inductive ConstInputObjectAsListItemValid (schema : Schema)
      : List (Name × ConstInputValue) -> TypeRef -> Prop where
    | intro (fields : List (Name × ConstInputValue)) (inner : TypeRef)
      (hvalue : ConstInputValueIsCorrectType schema (ConstInputValue.object fields) inner)
      : ConstInputObjectAsListItemValid schema fields inner
end

-- Spec 3.6.1 / 3.10 default-value validity wrapper.
def constInputValueIsCorrectType (schema : Schema)
    (value : ConstInputValue) (expectedType : TypeRef)
    : Prop :=
  ConstInputValueIsCorrectType schema value expectedType

-- Spec 3.6 / 3.7 field return covariance for object/interface implementation:
-- wrappers are structural, leaf named types are invariant, and composite named types
-- compare by possible runtime object subset.
def namedOutputTypeSubtype (schema : Schema) (implementation expected : Name) : Prop :=
  (schema.isLeafType implementation
    ∧ schema.isLeafType expected
    ∧ implementation = expected)
  ∨ (schema.isCompositeType implementation
      ∧ schema.isCompositeType expected
      ∧ ∀ objectName,
          schema.typeIncludesObject implementation objectName
          -> schema.typeIncludesObject expected objectName)

-- Spec 3.6 / 3.7 field return covariance with GraphQL wrapper rules: implementation
-- non-null may refine nullable, expected non-null requires implementation non-null, and
-- list wrappers must match recursively.
def outputTypeSubtype (schema : Schema) : TypeRef -> TypeRef -> Prop
  | .nonNull implementationInner, .nonNull expectedInner =>
      outputTypeSubtype schema implementationInner expectedInner
  | .nonNull implementationInner, expected =>
      outputTypeSubtype schema implementationInner expected
  | _implementation, .nonNull _expectedInner => False
  | .list implementationInner, .list expectedInner =>
      outputTypeSubtype schema implementationInner expectedInner
  | .list _implementationInner, _expected => False
  | _implementation, .list _expectedInner => False
  | .named implementationName, .named expectedName =>
      namedOutputTypeSubtype schema implementationName expectedName

end Schema

namespace ConstInputValue

-- Spec 3.6.1 / 3.10 default-value validity exposed from the constant-value namespace.
def isCorrectType (value : ConstInputValue) (schema : Schema) (expectedType : TypeRef)
    : Prop :=
  schema.constInputValueIsCorrectType value expectedType

end ConstInputValue

namespace TypeRef

-- Boolean counterpart to `Schema.isCompositeType` for a type reference's underlying
-- named type.
def isCompositeBool (typeRef : TypeRef) (schema : Schema) : Bool :=
  match schema.lookupType typeRef.namedType with
  | some (.object _objectType) => true
  | some (.interface _interfaceType) => true
  | some (.union _unionType) => true
  | _ => false

end TypeRef

end GraphQL
