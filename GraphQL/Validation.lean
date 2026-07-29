import GraphQL.Operation

/-! GraphQL operation validation
Spec reference: GraphQL September 2025.
- 5.2 Operations, 5.3 Fields, 5.4 Arguments, 5.5 Fragments, 5.6 Values, 5.7 Directives,
  and 5.8 Variables: this file states operation validity as a proposition over the modeled
  schema and operation syntax.
- Fidelity note: the model is intentionally partial. It omits document-level
  multi-operation rules, mutation/subscription rules, custom directive definitions, full
  input coercion and literal type checking, fragment-must-be-used, and meta-field rules.
-/

namespace GraphQL

namespace Validation

-- Spec 5.8.3 All Variable Uses Defined: partial helper for operation-level variable
-- lookup.
def getVariableDefinition? (variableDefinitions : List VariableDefinition) (name : Name)
    : Option VariableDefinition :=
  variableDefinitions.find? (fun variableDefinition => variableDefinition.name == name)

-- Spec 5.8.5 helper for non-null variable defaults.
def constInputValueNonNull : ConstInputValue -> Prop
  | value => value.nonNull

-- Spec 5.4.3 / 5.6.4 helper: null does not satisfy a required input entry.
def inputValueNonNull : InputValue -> Prop
  | .null => False
  | _ => True

-- Spec 5.6.2 input object field lookup helper for required-field validation.
def getInputObjectField? (fields : List (Name × InputValue)) (name : Name)
    : Option InputValue :=
  match fields with
  | [] => none
  | (fieldName, value) :: rest =>
      if fieldName = name then some value else getInputObjectField? rest name

-- Spec 5.4.3 / 5.6.4 required input entries: non-null type with no default.
def isRequiredInputValueDefinition (definition : InputValueDefinition) : Prop :=
  definition.isRequired

-- Spec 5.8.5 nullable-variable exception: a default exists and is not null.
def defaultValueNonNull (defaultValue : Option ConstInputValue) : Prop :=
  ∃ value, defaultValue = some value ∧ value.nonNull

-- Spec 5.8.5 `AreTypesCompatible`: faithful wrapper-aware variable/location input type
-- compatibility for the modeled type references.
def areInputTypesCompatible : TypeRef -> TypeRef -> Prop
  | .nonNull variableInner, .nonNull locationInner =>
      areInputTypesCompatible variableInner locationInner
  | .nonNull variableInner, location =>
      areInputTypesCompatible variableInner location
  | _variable, .nonNull _locationInner => False
  | .list variableInner, .list locationInner =>
      areInputTypesCompatible variableInner locationInner
  | .list _variableInner, _location => False
  | _variable, .list _locationInner => False
  | .named variableName, .named locationName => variableName = locationName

-- Spec 5.8.5 All Variable Usages Are Allowed: nullable variables can flow to a non-null
-- location only when the variable definition or the input location has a non-null default.
def variableUsageAllowed (schema : Schema)
    (variableDefinition : VariableDefinition)
    (locationType : TypeRef) (locationDefault : Option ConstInputValue)
    : Prop :=
  variableDefinition.typeRef.isInputType schema
  ∧ locationType.isInputType schema
  ∧ match locationType, variableDefinition.typeRef with
    | .nonNull _locationInner, .nonNull _variableInner =>
        areInputTypesCompatible variableDefinition.typeRef locationType
    | .nonNull locationInner, _variableType =>
        (defaultValueNonNull variableDefinition.defaultValue
          ∨ defaultValueNonNull locationDefault)
        ∧ areInputTypesCompatible variableDefinition.typeRef locationInner
    | _locationType, _variableType =>
        areInputTypesCompatible variableDefinition.typeRef locationType

mutual
  -- Spec 5.6.1 Values of Correct Type, 5.6.2-5.6.4 input object rules, 5.8.3
  -- variable definition lookup, and 5.8.5 variable usage compatibility. Literal coercion
  -- remains deliberately shallow, but input-object structure is checked recursively.
  inductive ValueIsCorrectTypeAtLocation (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      : InputValue -> TypeRef -> Option ConstInputValue -> Prop where
    | variable (variableName : Name) (expectedType : TypeRef)
      (locationDefault : Option ConstInputValue)
      (variableDefinition : VariableDefinition)
      (hinput : expectedType.isInputType schema)
      (hlookup
        : getVariableDefinition? variableDefinitions variableName
          = some variableDefinition)
      (husage
        : variableUsageAllowed schema variableDefinition expectedType locationDefault)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          (InputValue.variable variableName) expectedType locationDefault
    | nullNamed (typeName : Name)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.named typeName).isInputType schema)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          InputValue.null (TypeRef.named typeName) locationDefault
    | nullList (inner : TypeRef)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.list inner).isInputType schema)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          InputValue.null (TypeRef.list inner) locationDefault
    | nonNull (value : InputValue) (inner : TypeRef)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.nonNull inner).isInputType schema)
      (hnotNull : value ≠ InputValue.null)
      (hnotVariable : ∀ variableName, value ≠ InputValue.variable variableName)
      (hinner : ValueIsCorrectTypeAtLocation schema variableDefinitions value inner none)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          value (TypeRef.nonNull inner) locationDefault
    | list (values : List InputValue) (inner : TypeRef)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.list inner).isInputType schema)
      (hitems
        : ∀ item,
            item ∈ values
            -> ValueIsCorrectTypeAtLocation schema variableDefinitions item inner none)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          (InputValue.list values) (TypeRef.list inner) locationDefault
    | objectNamed (fields : List (Name × InputValue)) (typeName : Name)
      (locationDefault : Option ConstInputValue)
      (inputObject : InputObjectType)
      (hinput : (TypeRef.named typeName).isInputType schema)
      (hlookup : schema.lookupInputObject typeName = some inputObject)
      (hfields
        : InputObjectFieldsValid schema variableDefinitions
            inputObject.inputFields fields)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          (InputValue.object fields) (TypeRef.named typeName) locationDefault
    | objectAsListItem (fields : List (Name × InputValue)) (inner : TypeRef)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.list inner).isInputType schema)
      (hitem : InputObjectAsListItemValid schema variableDefinitions fields inner)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          (InputValue.object fields) (TypeRef.list inner) locationDefault
    | singletonListItem (value : InputValue) (inner : TypeRef)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.list inner).isInputType schema)
      (hnotList : ∀ values, value ≠ InputValue.list values)
      (hnotObject : ∀ fields, value ≠ InputValue.object fields)
      (hnotNull : value ≠ InputValue.null)
      (hnotVariable : ∀ variableName, value ≠ InputValue.variable variableName)
      (hitem : ValueIsCorrectTypeAtLocation schema variableDefinitions value inner none)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          value (TypeRef.list inner) locationDefault
    | namedNonInputObject (value : InputValue) (typeName : Name)
      (locationDefault : Option ConstInputValue)
      (hinput : (TypeRef.named typeName).isInputType schema)
      (hnotObject : ∀ fields, value ≠ InputValue.object fields)
      (hnotNull : value ≠ InputValue.null)
      (hnotVariable : ∀ variableName, value ≠ InputValue.variable variableName)
      (hlookup : schema.lookupInputObject typeName = none)
      : ValueIsCorrectTypeAtLocation schema variableDefinitions
          value (TypeRef.named typeName) locationDefault

  -- Spec 5.6.2-5.6.4 input object validation: supplied fields are unique, known,
  -- recursively well-typed, and all required fields are supplied as non-null values.
  inductive InputObjectFieldsValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      : List InputValueDefinition -> List (Name × InputValue) -> Prop where
    | intro (definitions : List InputValueDefinition)
      (fields : List (Name × InputValue))
      (hnodup : (fields.map Prod.fst).Nodup)
      (hknown
        : ∀ name value,
            (name, value) ∈ fields
            -> (Schema.lookupArgumentDefinition definitions name).isSome = true)
      (htyped
        : ∀ name value definition,
            (name, value) ∈ fields
            -> Schema.lookupArgumentDefinition definitions name = some definition
            -> ValueIsCorrectTypeAtLocation schema variableDefinitions
                value definition.inputType definition.defaultValue)
      (hrequiredPresent
        : ∀ definition,
            definition ∈ definitions
            -> isRequiredInputValueDefinition definition
            -> (getInputObjectField? fields definition.name).isSome = true)
      (hrequiredNonNull
        : ∀ definition value,
            definition ∈ definitions
            -> isRequiredInputValueDefinition definition
            -> getInputObjectField? fields definition.name = some value
            -> inputValueNonNull value)
      : InputObjectFieldsValid schema variableDefinitions definitions fields

  -- Spec 5.6.1 list input rule: an object value can be checked as one list item at a
  -- list location.
  inductive InputObjectAsListItemValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      : List (Name × InputValue) -> TypeRef -> Prop where
    | intro (fields : List (Name × InputValue)) (inner : TypeRef)
      (hvalue
        : ValueIsCorrectTypeAtLocation schema variableDefinitions
            (InputValue.object fields) inner none)
      : InputObjectAsListItemValid schema variableDefinitions fields inner
end

-- Spec 5.6.1 / 5.8.5 value validity at a specific input location, including that
-- location's default value for the nullable-variable exception.
def valueIsCorrectTypeAtLocation (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (value : InputValue) (expectedType : TypeRef)
    (locationDefault : Option ConstInputValue)
    : Prop :=
  ValueIsCorrectTypeAtLocation schema variableDefinitions
    value expectedType locationDefault

def valueIsCorrectType (schema : Schema) (variableDefinitions : List VariableDefinition)
    (value : InputValue) (expectedType : TypeRef)
    : Prop :=
  valueIsCorrectTypeAtLocation schema variableDefinitions value expectedType none

-- Spec 2.10 `Value Const` / 5.6.1 defaults: defaults are structurally constant and use
-- the same scoped validation as runtime input values.
def constValueIsCorrectType (schema : Schema)
    (value : ConstInputValue) (expectedType : TypeRef)
    : Prop :=
  value.isCorrectType schema expectedType

-- Spec 3.13.1 `@skip` / 3.13.2 `@include`: both modeled directives define `if:
-- Boolean!`.
def booleanNonNullType : TypeRef :=
  .nonNull (.named "Boolean")

-- Spec 3.13.1 / 3.13.2 directive `if` argument validation for the modeled executable
-- directives, using the same variable-usage rule as field/input-object arguments.
def directiveIfArgumentValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    : InputValue -> Prop
  | .boolean _ => True
  | .variable variableName =>
      ∃ variableDefinition,
        getVariableDefinition? variableDefinitions variableName = some variableDefinition
        ∧ variableUsageAllowed schema variableDefinition booleanNonNullType none
  | _ => False

-- Non-spec helper exposing the modeled directive name for non-repeatability checks.
def directiveName : DirectiveApplication -> Name
  | .skip _ => "skip"
  | .include _ => "include"

-- Spec 3.13.1 / 3.13.2 directive validation for the modeled built-ins.
def directiveValid (schema : Schema) (variableDefinitions : List VariableDefinition)
    : DirectiveApplication -> Prop
  | .skip ifArgument =>
      directiveIfArgumentValid schema variableDefinitions ifArgument
  | .include ifArgument =>
      directiveIfArgumentValid schema variableDefinitions ifArgument

-- Spec 5.7 Directives for the modeled executable subset: `@skip` and `@include` are
-- defined at selection locations, are non-repeatable, and require `if: Boolean!`.
def directivesValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (directives : List DirectiveApplication)
    : Prop :=
  (directives.map directiveName).Nodup
  ∧ ∀ directive,
      directive ∈ directives -> directiveValid schema variableDefinitions directive

-- Spec 5.8.2 Variables Are Input Types: partial; also validates default values using the
-- scoped constant default-value predicate.
def variableDefinitionValid (schema : Schema) (variableDefinition : VariableDefinition)
    : Prop :=
  variableDefinition.typeRef.isInputType schema
  ∧ match variableDefinition.defaultValue with
    | none => True
    | some defaultValue =>
        constValueIsCorrectType schema defaultValue variableDefinition.typeRef

-- Spec 5.8.1 Variable Uniqueness and 5.8.2 Variables Are Input Types. Usage
-- compatibility is checked separately at each value location.
def variableDefinitionsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    : Prop :=
  (variableDefinitions.map VariableDefinition.name).Nodup
  ∧ ∀ variableDefinition,
      variableDefinition ∈ variableDefinitions
      -> variableDefinitionValid schema variableDefinition

mutual
  -- Spec 5.8.4 variable uses nested within an input value.
  def inputValueVariables : InputValue -> List Name
    | .variable name => [name]
    | .list values => inputValuesVariables values
    | .object fields => inputObjectFieldsVariables fields
    | _ => []

  def inputValuesVariables : List InputValue -> List Name
    | [] => []
    | value :: rest =>
        inputValueVariables value ++ inputValuesVariables rest

  def inputObjectFieldsVariables : List (Name × InputValue) -> List Name
    | [] => []
    | (_name, value) :: rest =>
        inputValueVariables value ++ inputObjectFieldsVariables rest
end

def argumentVariables (argument : Argument) : List Name :=
  inputValueVariables argument.value

def argumentsVariables : List Argument -> List Name
  | [] => []
  | argument :: rest =>
      argumentVariables argument ++ argumentsVariables rest

def directiveVariables : DirectiveApplication -> List Name
  | .skip ifArgument => inputValueVariables ifArgument
  | .include ifArgument => inputValueVariables ifArgument

def directivesVariables : List DirectiveApplication -> List Name
  | [] => []
  | directive :: rest =>
      directiveVariables directive ++ directivesVariables rest

mutual
  -- Spec 5.8.4 variable uses in field arguments, directives, and nested selections.
  def selectionVariables : Selection -> List Name
    | .field _responseName _fieldName arguments directives selectionSet =>
        argumentsVariables arguments
        ++ directivesVariables directives
        ++ selectionSetVariables selectionSet
    | .inlineFragment _typeCondition directives selectionSet =>
        directivesVariables directives ++ selectionSetVariables selectionSet

  def selectionSetVariables : List Selection -> List Name
    | [] => []
    | selection :: rest =>
        selectionVariables selection ++ selectionSetVariables rest
end

-- Spec 5.8.4 All Variables Used for the fragment-free operation syntax.
def operationVariablesUsed (operation : Operation) : Prop :=
  ∀ variableDefinition,
    variableDefinition ∈ operation.variableDefinitions
    -> variableDefinition.name ∈ selectionSetVariables operation.selectionSet

-- Spec 5.4.1 Argument Names, 5.6.1 Values of Correct Type, and 5.8.5 variable usage:
-- validates defined argument names and value compatibility at the argument location.
def argumentValid (schema : Schema) (definitions : List InputValueDefinition)
    (variableDefinitions : List VariableDefinition) (argument : Argument)
    : Prop :=
  ∃ definition,
    Schema.lookupArgumentDefinition definitions argument.name = some definition
    ∧ valueIsCorrectTypeAtLocation schema variableDefinitions
        argument.value definition.inputType definition.defaultValue

-- Spec 5.4.3 required argument lookup by name.
def getArgument? (arguments : List Argument) (name : Name) : Option Argument :=
  arguments.find? (fun argument => argument.name == name)

-- Spec 5.4.3 Required Arguments: faithful for identifying non-null arguments without
-- defaults.
def isRequiredArgument (definition : InputValueDefinition) : Prop :=
  isRequiredInputValueDefinition definition

-- Spec 5.4.1-5.4.3 Argument validation: partial; handles names, uniqueness, required
-- arguments, value validity, and variable usage compatibility at argument locations.
def argumentsValid (schema : Schema) (definitions : List InputValueDefinition)
    (variableDefinitions : List VariableDefinition) (arguments : List Argument)
    : Prop :=
  (arguments.map Argument.name).Nodup
  ∧ (∀ argument,
      argument ∈ arguments
      -> argumentValid schema definitions variableDefinitions argument)
  ∧ (∀ definition,
      definition ∈ definitions
      -> isRequiredArgument definition
      -> ∃ argument,
          getArgument? arguments definition.name = some argument
          ∧ inputValueNonNull argument.value)

-- Spec 5.3 Field validation and 5.7 Directive validation:
-- partial; combines modeled field lookup, arguments, leaf/composite subselection checks,
-- and inline-fragment applicability.
mutual
  def selectionValid (schema : Schema)
      (variableDefinitions : List VariableDefinition) (parentType : Name)
      : Selection -> Prop
    | .field _responseName fieldName arguments directives selectionSet =>
        directivesValid schema variableDefinitions directives
        ∧ ∃ fieldDefinition,
            schema.lookupField parentType fieldName = some fieldDefinition
            ∧ argumentsValid schema fieldDefinition.arguments variableDefinitions
                arguments
            ∧ fieldSelectionSetValid schema variableDefinitions
                fieldDefinition selectionSet
    | .inlineFragment none directives selectionSet =>
        directivesValid schema variableDefinitions directives
        ∧ selectionSet ≠ []
        ∧ selectionSetValid schema variableDefinitions parentType selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        directivesValid schema variableDefinitions directives
        ∧ schema.isCompositeType typeCondition
        ∧ schema.typesOverlap parentType typeCondition
        ∧ selectionSet ≠ []
        ∧ selectionSetValid schema variableDefinitions typeCondition selectionSet

  def selectionSetValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> selectionValid schema variableDefinitions parentType selection

  def fieldSelectionSetValid (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (fieldDefinition : FieldDefinition) (selectionSet : List Selection)
      : Prop :=
    let returnType := fieldDefinition.outputType.namedType
    fieldDefinition.outputType.isOutputType schema
    ∧ ((schema.isLeafType returnType ∧ selectionSet = [])
        ∨ (schema.isCompositeType returnType
            ∧ selectionSet ≠ []
            ∧ selectionSetValid schema variableDefinitions returnType selectionSet))
end

end Validation

namespace FieldMerge

-- Spec 5.3.2 `FieldsInSetCanMerge` field-pair context: non-spec helper carrying the
-- parent type and field data needed by merge checks.
structure ScopedField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  outputType : TypeRef
  selectionSet : List Selection
deriving Repr

-- Spec 5.3.2 `SameResponseShape`: mostly faithful for wrapping structure and leaf
-- named-type equality, using the modeled schema's leaf/output predicates.
def sameResponseShape (schema : Schema) : TypeRef -> TypeRef -> Prop
  | .nonNull left, .nonNull right => sameResponseShape schema left right
  | .nonNull _, _ => False
  | _, .nonNull _ => False
  | .list left, .list right => sameResponseShape schema left right
  | .list _, _ => False
  | _, .list _ => False
  | .named left, .named right =>
      schema.isOutputType left
      ∧ schema.isOutputType right
      ∧ ((schema.isLeafType left ∨ schema.isLeafType right) -> left = right)

-- Spec 5.3.2 `CollectFieldsAndFragmentNames` / 6.3.2 `CollectFields`: partial validation
-- helper; it does not apply directives or runtime type-condition filtering.
def collectFields (schema : Schema) : Name -> List Selection -> List ScopedField
  | _parentType, [] => []
  | parentType, selection :: rest =>
      let current :=
        match selection with
        | .field responseName fieldName arguments _directives selectionSet =>
            match schema.lookupField parentType fieldName with
            | none => []
            | some fieldDefinition =>
                [{
                  parentType := parentType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  outputType := fieldDefinition.outputType,
                  selectionSet := selectionSet
                }]
        | .inlineFragment none _directives selectionSet =>
            collectFields schema parentType selectionSet
        | .inlineFragment (some typeCondition) _directives selectionSet =>
            collectFields schema typeCondition selectionSet
      current ++ collectFields schema parentType rest

-- Spec 5.3.2 `FieldsInSetCanMerge`: captures pairwise response-shape,
-- same-field/argument checks on overlapping parent types, and recursive merged
-- subselection checks. It is a proposition rather than a recursive executable
-- function, so it does not need a synthetic fuel counter.
mutual
  inductive FieldsInSetCanMerge (schema : Schema) : Name -> List Selection -> Prop where
    | intro (parentType : Name) (selectionSet : List Selection)
      (hfields
        : let fields := collectFields schema parentType selectionSet
          ∀ left,
            left ∈ fields
            -> ∀ right,
                right ∈ fields
                -> left.responseName = right.responseName
                -> FieldsForNameCanMerge schema left right)
      : FieldsInSetCanMerge schema parentType selectionSet

  inductive FieldsForNameCanMerge (schema : Schema)
      : ScopedField -> ScopedField -> Prop where
    | intro (left right : ScopedField)
      (hshape : sameResponseShape schema left.outputType right.outputType)
      (hidentity
        : (left.parentType = right.parentType
            ∨ ¬ schema.objectType left.parentType
            ∨ ¬ schema.objectType right.parentType)
          -> left.fieldName = right.fieldName
              ∧ Argument.argumentsEquivalent left.arguments right.arguments)
      (hsubfields
        : (left.parentType = right.parentType
            ∨ ¬ schema.objectType left.parentType
            ∨ ¬ schema.objectType right.parentType)
          -> ∀ objectType,
              FieldsInSetCanMerge schema objectType
                (left.selectionSet ++ right.selectionSet))
      : FieldsForNameCanMerge schema left right
end

def fieldsInSetCanMerge (schema : Schema)
    (parentType : Name) (selectionSet : List Selection)
    : Prop :=
  FieldsInSetCanMerge schema parentType selectionSet

def fieldsForNameCanMerge (schema : Schema) (left right : ScopedField) : Prop :=
  FieldsForNameCanMerge schema left right

end FieldMerge

namespace Validation

-- Spec 5.2 Operation validation plus referenced executable validation rules: partial
-- aggregate predicate over the modeled single-operation representation.
def operationDefinitionValid (schema : Schema) (operation : Operation) : Prop :=
  operation.operationType = .query
  ∧ schema.isCompositeType (operation.rootType schema)
  ∧ variableDefinitionsValid schema operation.variableDefinitions
  ∧ operation.selectionSet ≠ []
  ∧ selectionSetValid schema operation.variableDefinitions
      (operation.rootType schema) operation.selectionSet
  ∧ FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
      operation.selectionSet
  ∧ operationVariablesUsed operation

end Validation

end GraphQL
