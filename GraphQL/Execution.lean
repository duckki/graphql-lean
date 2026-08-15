import GraphQL.Operation

/-! GraphQL query execution semantics
Spec reference: GraphQL September 2025.
- 6.1-6.2 Executing Requests and Operations: this module executes the modeled single
  query-like operation, not full request validation/coercion or mutation/subscription
  modes.
- 6.3 Executing Selection Sets: field collection, grouped field execution, and subfield
  merging are represented over selections.
- 6.4 Executing Fields: resolver invocation, argument default materialization, value
  completion, and execution-error null bubbling are modeled for a synchronous query
  fragment. Argument coercion failure is handled as a field error before resolver
  invocation. Scalar parsing, result coercion details, asynchronous behavior, and error
  metadata are omitted. Resolver failure is modeled as `none`, handled as a field error,
  counted in the response envelope, and propagated through non-null wrappers for the
  response path.
- 7 Response: response data is modeled recursively; the query response envelope carries
  response data plus a `Nat` execution-error count, omitting error details, paths,
  locations, extensions, and request error results.
-/

namespace GraphQL

namespace Execution

-- Spec 6.4.2 internal value domain used to stand in for host-language resolver results.
inductive ResolverValue (ObjectRef : Type := PUnit) where
  | null
  | scalar (value : String)
  | object (typeName : Name) (ref : ObjectRef)
  | list (values : List (ResolverValue ObjectRef))
deriving Repr

namespace Option

protected def null {ObjectRef : Type} : Option (ResolverValue ObjectRef) :=
  some .null

protected def scalar {ObjectRef : Type} (value : String)
    : Option (ResolverValue ObjectRef) :=
  some (.scalar value)

protected def object {ObjectRef : Type} (typeName : Name) (ref : ObjectRef)
    : Option (ResolverValue ObjectRef) :=
  some (.object typeName ref)

protected def list {ObjectRef : Type} (values : List (ResolverValue ObjectRef))
    : Option (ResolverValue ObjectRef) :=
  some (.list values)

end Option

-- Spec 7.1.1 response data: partial; models response data recursively, omitting execution
-- errors, extensions, response positions, and serialization details.
inductive ResponseValue where
  | null
  | scalar (value : String)
  | object (fields : List (Name × ResponseValue))
  | list (values : List ResponseValue)
deriving Repr

instance instInhabitedResponseValue : Inhabited ResponseValue where
  default := .null

-- Spec 7.1 response envelope: `errors` is an execution-error count rather than the
-- spec's list of detailed error maps.
structure Response where
  data : ResponseValue
  errors : Nat := 0
deriving Repr

-- Internal result for spec 6.4.4 null propagation. `Except.error errors` means
-- that a null/error reached a non-null wrapper and must be handled by the nearest
-- nullable parent. `Except.ok (value, errors)` carries the completed value plus
-- any execution errors accumulated below it.
abbrev Result (α : Type) : Type :=
  Except Nat (α × Nat)

namespace Result

def getD (default : α) : Result α -> α
  | .error _errors => default
  | .ok (value, _errors) => value

def combine {α β γ : Type} (combine : α -> β -> γ) : Result α -> Result β -> Result γ
  | .ok (left, leftErrors), .ok (right, rightErrors) =>
      .ok (combine left right, leftErrors + rightErrors)
  | .error leftErrors, .ok (_right, rightErrors) =>
      .error (leftErrors + rightErrors)
  | .ok (_left, leftErrors), .error rightErrors =>
      .error (leftErrors + rightErrors)
  | .error leftErrors, .error rightErrors =>
      .error (leftErrors + rightErrors)

end Result

instance instCoeResult {α : Type} [Inhabited α] : Coe (Result α) α where
  coe := Result.getD default

-- Runtime input values use the variable-free grammar. This is the same shape as a
-- constant syntax value, but the name records that it has crossed the execution
-- boundary and may have come from request variables rather than source text.
abbrev CoercedInputValue := ConstInputValue

-- Spec 6.1.2 `CoerceVariableValues`: supplied values and the resulting variable map are
-- runtime values, so executable `.variable` references are unrepresentable. Explicit
-- supplied values are assumed already coerced and type-conformant where scalar
-- semantics would matter.
abbrev VariableValues := List (Name × CoercedInputValue)

mutual
  -- Variable names that the input syntax can resolve. Runtime values are ground, so
  -- argument coercion never needs unrelated entries from the operation environment.
  def inputValueReferencedVariables : InputValue -> List Name
    | .variable name => [name]
    | .list values => inputValueListReferencedVariables values
    | .object fields => inputValueObjectFieldsReferencedVariables fields
    | _ => []

  def inputValueListReferencedVariables : List InputValue -> List Name
    | [] => []
    | value :: rest =>
        inputValueReferencedVariables value ++ inputValueListReferencedVariables rest

  def inputValueObjectFieldsReferencedVariables : List (Name × InputValue) -> List Name
    | [] => []
    | (_, value) :: rest =>
        inputValueReferencedVariables value
        ++ inputValueObjectFieldsReferencedVariables rest
end

-- Spec 6.4.2 resolver argument entry. Both the argument map and runtime variable map use
-- the variable-free input grammar, so executable syntax cannot cross the resolver
-- boundary.
structure CoercedArgument where
  name : Name
  value : CoercedInputValue
deriving Repr

namespace CoercedArgument

def toArgument (argument : CoercedArgument) : Argument :=
  { name := argument.name, value := argument.value.toInputValue }

def equivalent (left right : CoercedArgument) : Prop :=
  Argument.equivalent left.toArgument right.toArgument

def argumentsEquivalent (left right : List CoercedArgument) : Prop :=
  (∀ leftArgument,
    leftArgument ∈ left
    -> ∃ rightArgument, rightArgument ∈ right ∧ equivalent leftArgument rightArgument)
  ∧ ∀ rightArgument,
      rightArgument ∈ right
      -> ∃ leftArgument, leftArgument ∈ left ∧ equivalent leftArgument rightArgument

end CoercedArgument

abbrev CoercedArguments := List CoercedArgument

-- Spec 6.4.2 semantic resolver API. Resolvers receive only the schema-derived argument
-- map; executable argument syntax never crosses this boundary.
structure Resolvers (ObjectRef : Type := PUnit) where
  resolve
    : Name -> Name -> CoercedArguments -> ResolverValue ObjectRef
      -> Option (ResolverValue ObjectRef)
  resolve_argumentsEquivalent
    : ∀ parentType fieldName firstArguments laterArguments source,
        CoercedArgument.argumentsEquivalent firstArguments laterArguments
        -> resolve parentType fieldName firstArguments source
            = resolve parentType fieldName laterArguments source

variable {ObjectRef : Type}

instance instCoeNameToTypeRef : Coe Name TypeRef where
  coe := TypeRef.named

-- Spec 6.1.2 variable value lookup helper for already-coerced modeled variables.
def lookupVariableValue? (variableValues : VariableValues) (name : Name)
    : Option CoercedInputValue :=
  match variableValues with
  | [] => none
  | (variableName, value) :: rest =>
      if variableName = name then some value else lookupVariableValue? rest name

def lookupInputObjectFieldValue? : List (Name × InputValue) -> Name -> Option InputValue
  | [], _name => none
  | (fieldName, value) :: rest, name =>
      if fieldName = name then some value else lookupInputObjectFieldValue? rest name

mutual
  def inputValueCoercionFuel : InputValue -> Nat
    | .list values => inputValuesCoercionFuel values + 1
    | .object fields => inputObjectFieldsCoercionFuel fields + 1
    | _ => 1

  def inputValuesCoercionFuel : List InputValue -> Nat
    | [] => 0
    | value :: rest => inputValueCoercionFuel value + inputValuesCoercionFuel rest

  def inputObjectFieldsCoercionFuel : List (Name × InputValue) -> Nat
    | [] => 0
    | (_, value) :: rest =>
        inputValueCoercionFuel value + inputObjectFieldsCoercionFuel rest
end

def variableValuesCoercionFuel : VariableValues -> Nat
  | [] => 0
  | (_, value) :: rest =>
      inputValueCoercionFuel value.toInputValue + variableValuesCoercionFuel rest

def inputValueDefinitionCoercionFuel (definition : InputValueDefinition) : Nat :=
  match definition.defaultValue with
  | none => 0
  | some value => inputValueCoercionFuel value.toInputValue

def inputValueDefinitionsCoercionFuel : List InputValueDefinition -> Nat
  | [] => 0
  | definition :: rest =>
      inputValueDefinitionCoercionFuel definition + inputValueDefinitionsCoercionFuel rest

def fieldDefinitionsInputCoercionFuel : List FieldDefinition -> Nat
  | [] => 0
  | field :: rest =>
      inputValueDefinitionsCoercionFuel field.arguments
      + fieldDefinitionsInputCoercionFuel rest

def typeDefinitionInputCoercionFuel : TypeDefinition -> Nat
  | .object objectType => fieldDefinitionsInputCoercionFuel objectType.fields
  | .interface interfaceType =>
      fieldDefinitionsInputCoercionFuel interfaceType.fields
  | .inputObject inputObject =>
      inputValueDefinitionsCoercionFuel inputObject.inputFields
  | _ => 0

def typeDefinitionsInputCoercionFuel : List TypeDefinition -> Nat
  | [] => 0
  | typeDefinition :: rest =>
      typeDefinitionInputCoercionFuel typeDefinition
      + typeDefinitionsInputCoercionFuel rest

def schemaInputCoercionFuel (schema : Schema) : Nat :=
  typeDefinitionsInputCoercionFuel schema.types + schema.types.length + 1

-- Input coercion must distinguish an absent variable from an invalid supplied value.
-- The surrounding list, input-object, or argument location decides how `undefined` is
-- interpreted; `error` always aborts coercion at that location.
inductive InputCoercionResult where
  | undefined
  | success (value : CoercedInputValue)
  | error
deriving Repr

def inputObjectFieldsKnownBool (definitions : List InputValueDefinition)
    : List (Name × InputValue) -> Bool
  | [] => true
  | (name, _value) :: rest =>
      (Schema.lookupArgumentDefinition definitions name).isSome
      && inputObjectFieldsKnownBool definitions rest

mutual
  -- Raw schemas can contain cyclic input-object defaults, so coercion is deliberately
  -- fuel-bounded. The result carries either the successfully materialized ground value,
  -- an undefined variable, or a coercion error in one pass.
  def coerceInputValueBounded (schema : Schema) (variableValues : VariableValues)
      : Nat -> TypeRef -> InputValue -> InputCoercionResult
    | 0, _inputType, _value => .error
    | fuel + 1, inputType, .variable name =>
        match lookupVariableValue? variableValues name with
        | none => .undefined
        | some value =>
            coerceInputValueBounded schema variableValues fuel inputType
              value.toInputValue
    | _fuel + 1, .nonNull _inner, .null => .error
    | _fuel + 1, _inputType, .null => .success .null
    | fuel + 1, .nonNull inner, value =>
        coerceInputValueBounded schema variableValues fuel inner value
    | fuel + 1, .list inner, .list values =>
        match coerceInputValueListBounded schema variableValues fuel inner values with
        | .ok coerced => .success (.list coerced)
        | .error _ => .error
    | fuel + 1, .list inner, value =>
        match coerceInputValueBounded schema variableValues fuel inner value with
        | .undefined => .undefined
        | .success coerced => .success (.list [coerced])
        | .error => .error
    | fuel + 1, .named typeName, .object fields =>
        match schema.lookupInputObject typeName with
        | none => .error
        | some inputObject =>
            if inputObjectFieldsKnownBool inputObject.inputFields fields then
              match coerceInputObjectFieldsBounded schema variableValues fuel
                      inputObject.inputFields fields with
              | .ok coerced => .success (.object coerced)
              | .error _ => .error
            else
              .error
    | _fuel + 1, .named typeName, value =>
        match schema.lookupInputObject typeName with
        | none =>
            match ConstInputValue.ofInputValue? value with
            | some coerced => .success coerced
            | none => .error
        | some _inputObject => .error

  def coerceInputValueListBounded
      (schema : Schema) (variableValues : VariableValues)
      (fuel : Nat) (inputType : TypeRef)
      : List InputValue -> Except Unit (List CoercedInputValue)
    | [] => .ok []
    | value :: rest =>
        match coerceInputValueBounded schema variableValues fuel inputType value with
        | .error => .error ()
        | .undefined =>
            if inputType.isNonNull then
              .error ()
            else
              match coerceInputValueListBounded schema variableValues fuel inputType
                      rest with
              | .ok coerced => .ok (.null :: coerced)
              | .error _ => .error ()
        | .success coercedValue =>
            match coerceInputValueListBounded schema variableValues fuel inputType
                    rest with
            | .ok coerced => .ok (coercedValue :: coerced)
            | .error _ => .error ()

  def coerceInputObjectFieldsBounded
      (schema : Schema) (variableValues : VariableValues)
      (fuel : Nat)
      : List InputValueDefinition -> List (Name × InputValue)
        -> Except Unit (List (Name × CoercedInputValue))
    | [], _fields => .ok []
    | definition :: definitions, fields =>
        let suppliedResult :=
          match lookupInputObjectFieldValue? fields definition.name with
          | some value =>
              coerceInputValueBounded schema variableValues fuel
                definition.inputType value
          | none => .undefined
        let effectiveResult :=
          match suppliedResult with
          | .success value => InputCoercionResult.success value
          | .error => InputCoercionResult.error
          | .undefined =>
              match definition.defaultValue with
              | some value =>
                  coerceInputValueBounded schema variableValues fuel
                    definition.inputType value.toInputValue
              | none =>
                  if definition.inputType.isNonNull then
                    InputCoercionResult.error
                  else
                    InputCoercionResult.undefined
        match effectiveResult with
        | .error => .error ()
        | .undefined =>
            coerceInputObjectFieldsBounded schema variableValues fuel definitions fields
        | .success value =>
            match coerceInputObjectFieldsBounded schema variableValues fuel definitions
                    fields with
            | .error _ => .error ()
            | .ok coerced => .ok ((definition.name, value) :: coerced)
end

mutual
  -- Only variable values reachable from the input syntax contribute to its coercion
  -- budget. Unrelated operation defaults must not affect the arguments observed by a
  -- resolver.
  def referencedVariableValuesCoercionFuel (variableValues : VariableValues)
      : InputValue -> Nat
    | .variable name =>
        (lookupVariableValue? variableValues name).map
          (fun value => inputValueCoercionFuel value.toInputValue)
        |>.getD 0
    | .list values =>
        referencedVariableValueListCoercionFuel variableValues values
    | .object fields =>
        referencedVariableObjectFieldsCoercionFuel variableValues fields
    | _ => 0

  def referencedVariableValueListCoercionFuel (variableValues : VariableValues)
      : List InputValue -> Nat
    | [] => 0
    | value :: rest =>
        referencedVariableValuesCoercionFuel variableValues value
        + referencedVariableValueListCoercionFuel variableValues rest

  def referencedVariableObjectFieldsCoercionFuel (variableValues : VariableValues)
      : List (Name × InputValue) -> Nat
    | [] => 0
    | (_, value) :: rest =>
        referencedVariableValuesCoercionFuel variableValues value
        + referencedVariableObjectFieldsCoercionFuel variableValues rest
end

def coerceInputValueFuel (schema : Schema) (variableValues : VariableValues)
    (value : InputValue)
    : Nat :=
  schemaInputCoercionFuel schema
  + referencedVariableValuesCoercionFuel variableValues value
  + inputValueCoercionFuel value

-- Spec input coercion result used by execution. Undefined variables remain distinct
-- from invalid values so an enclosing argument or input-object field can apply its own
-- default.
def coerceInputValue (schema : Schema) (variableValues : VariableValues)
    (inputType : TypeRef) (value : InputValue)
    : InputCoercionResult :=
  coerceInputValueBounded schema variableValues
    (coerceInputValueFuel schema variableValues value)
    inputType value

-- Spec 6.1.2 `CoerceVariableValues`, default-value branch: partial; for every missing
-- variable, materialize its constant operation default, including an explicit `null`
-- default. Supplied values, including supplied `null`, take precedence. Full input
-- coercion and request errors remain outside the modeled execution result, so supplied
-- values are retained and assumed already coerced and type-conformant.
def coerceVariableValues (operation : Operation) (variableValues : VariableValues)
    : VariableValues :=
  operation.variableDefinitions.foldl
    (fun coercedValues variableDefinition =>
      match lookupVariableValue? coercedValues variableDefinition.name with
      | some _value => coercedValues
      | none =>
          match variableDefinition.defaultValue with
          | some defaultValue =>
              (variableDefinition.name, defaultValue) :: coercedValues
          | none => coercedValues)
    variableValues

inductive ArgumentCoercionResult where
  | success (arguments : CoercedArguments)
  | error
deriving Repr

namespace ArgumentCoercionResult

@[simp]
def isSuccess : ArgumentCoercionResult -> Bool
  | .success _arguments => true
  | .error => false

def equivalent : ArgumentCoercionResult -> ArgumentCoercionResult -> Prop
  | .success left, .success right => CoercedArgument.argumentsEquivalent left right
  | .error, .error => True
  | _, _ => False

end ArgumentCoercionResult

def coerceArgumentDefault
    (schema : Schema) (variableValues : VariableValues)
    (definition : InputValueDefinition)
    : InputCoercionResult :=
  match definition.defaultValue with
  | some value =>
      coerceInputValue schema variableValues definition.inputType value.toInputValue
  | none =>
      if definition.inputType.isNonNull then .error else .undefined

def coerceArgumentValue
    (schema : Schema) (variableValues : VariableValues)
    (definition : InputValueDefinition) (arguments : List Argument)
    : InputCoercionResult :=
  let suppliedResult :=
    match Argument.lookupValue? arguments definition.name with
    | some value =>
        coerceInputValue schema variableValues definition.inputType value
    | none => .undefined
  match suppliedResult with
  | .undefined => coerceArgumentDefault schema variableValues definition
  | result => result

-- Spec 6.4.1 `CoerceArgumentValues`. Undefined variables may activate an argument
-- default or omit a nullable argument. Invalid supplied/default values and missing
-- required arguments are execution errors.
def coerceArgumentValues (schema : Schema) (variableValues : VariableValues)
    : List InputValueDefinition -> List Argument -> ArgumentCoercionResult
  | [], _arguments => .success []
  | definition :: definitions, arguments =>
      match coerceArgumentValues schema variableValues definitions arguments with
      | .error => .error
      | .success coerced =>
          match coerceArgumentValue schema variableValues definition arguments with
          | .error => .error
          | .undefined => .success coerced
          | .success value =>
              .success ({ name := definition.name, value := value } :: coerced)

-- Spec 3.13.1 `@skip` / 3.13.2 `@include`: partial; resolves only Boolean literals or
-- variables bound to Boolean literals.
def inputValueBoolean? (variableValues : VariableValues) : InputValue -> Option Bool
  | .variable name => do
      let value <- lookupVariableValue? variableValues name
      value.toInputValue.staticBoolean?
  | value => value.staticBoolean?

-- Spec 6.3.2 `CollectFields` inline `@skip`/`@include` checks: local per-directive
-- helper, not a named spec algorithm.
def directiveAllowsSelectionBool (variableValues : VariableValues)
    : DirectiveApplication -> Bool
  | .skip ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => !value
      | none => false
  | .include ifArgument =>
      match inputValueBoolean? variableValues ifArgument with
      | some value => value
      | none => false

-- Spec 6.3.2 `CollectFields` inline directive checks: local helper over one selection's
-- directive list, not a named spec algorithm.
def selectionDirectivesAllowBool (variableValues : VariableValues)
    (directives : List DirectiveApplication)
    : Bool :=
  directives.all (fun directive => directiveAllowsSelectionBool variableValues directive)

-- Spec 6.3.2 `DoesFragmentTypeApply` needs a runtime object type when the source value
-- is object-like.
def runtimeObjectType? : ResolverValue ObjectRef -> Option Name
  | .object typeName _ref => some typeName
  | _ => none

-- Spec 6.3.2 `DoesFragmentTypeApply`: partial; faithful when runtime object type is
-- known, but falls back to parent/type overlap for non-object placeholder values.
def doesFragmentTypeApplyBool
    (schema : Schema) (parentType : Name)
    (source : ResolverValue ObjectRef) (typeCondition : Name)
    : Bool :=
  match runtimeObjectType? source with
  | some objectName => schema.typeIncludesObjectBool typeCondition objectName
  | none => schema.typesOverlapBool parentType typeCondition

-- Spec 6.3.2 collected field entries: non-spec helper carrying the data needed to execute
-- one grouped response name.
structure ExecutableField where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
deriving Repr

-- Spec 6.3.2 collected fields map helper: inserts one existing group into another map.
def addExecutableGroup (group : Name × List ExecutableField)
    : List (Name × List ExecutableField) -> List (Name × List ExecutableField)
  | [] => [group]
  | (responseName, fields) :: rest =>
      if responseName == group.fst then
        (responseName, fields ++ group.snd) :: rest
      else
        (responseName, fields) :: addExecutableGroup group rest

-- Spec 6.3.2 `CollectFields` grouping merge for list-backed response-name maps.
def mergeExecutableGroups (left right : List (Name × List ExecutableField))
    : List (Name × List ExecutableField) :=
  right.foldl (fun grouped group => addExecutableGroup group grouped) left

-- Fuel exhaustion is an internal truncation of the executable model, so it is modeled
-- as an execution error at the current response position.
def outOfFuel {α : Type} : Result α :=
  .error 1

-- Spec 6.4.4 `HandleFieldError`: the model records only one counted error. Nullable
-- fields complete as `null`; non-null fields propagate to the nearest nullable parent.
def handleFieldError (fieldType : TypeRef) : Result ResponseValue :=
  match fieldType with
  | .nonNull _inner => .error 1
  | _ => .ok (.null, 1)

-- Spec 6.4.3 non-null completion: when a non-null field completes to null without an
-- originating child/resolver error, the non-null field itself contributes one error.
def nonNullCompletion (completed : Result ResponseValue) : Result ResponseValue :=
  match completed with
  | .error errors => .error errors
  | .ok (.null, errors) =>
      .error
      <| match errors with
          | 0 => 1
          | errors + 1 => errors + 1
  | .ok (response, errors) => .ok (response, errors)

def singleFieldResult (responseName : Name) (completed : Result ResponseValue)
    : Result (List (Name × ResponseValue)) :=
  match completed with
  | .error errors => .error errors
  | .ok (response, errors) => .ok ([(responseName, response)], errors)

def catchBubbleAsNull {α : Type} (wrap : α -> ResponseValue) (completed : Result α)
    : Result ResponseValue :=
  match completed with
  | .error errors => .ok (.null, errors)
  | .ok (value, errors) => .ok (wrap value, errors)

-- Spec 6.3.2 `CollectFields` and `CollectSubfields`: partial; list-backed ordered
-- grouping of executable fields by response name.
mutual
  -- Spec 6.3.2 `CollectFields` selection step: partial; handles built-in directives and
  -- inline fragments.
  def collectSelection (schema : Schema) (variableValues : VariableValues)
      : Name -> ResolverValue ObjectRef -> Selection -> List (Name × List ExecutableField)
    | parentType,
      _source,
      .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [(
            responseName,
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
          )]
        else
          []
    | parentType, source, .inlineFragment none directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          collectFields schema variableValues parentType source selectionSet
        else
          []
    | parentType,
      source,
      .inlineFragment (some typeCondition) directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          if doesFragmentTypeApplyBool schema parentType source typeCondition then
            collectFields schema variableValues parentType source selectionSet
          else
            []
        else
          []

  -- Spec 6.3.2 `CollectFields`: partial; list-backed ordered grouping of executable
  -- fields by response name.
  def collectFields (schema : Schema) (variableValues : VariableValues)
      : Name -> ResolverValue ObjectRef -> List Selection
        -> List (Name × List ExecutableField)
    | _parentType, _source, [] => []
    | parentType, source, selection :: rest =>
        mergeExecutableGroups
          (collectSelection schema variableValues parentType source selection)
          (collectFields schema variableValues parentType source rest)

  -- Spec 6.3.2 `CollectSubfields`: all grouped fields for one response name
  -- contribute child selections, which are collected under the runtime object
  -- type.
  def collectSubfields
      (schema : Schema) (variableValues : VariableValues)
      (objectType : Name) (objectValue : ResolverValue ObjectRef)
      : List ExecutableField -> List (Name × List ExecutableField)
    | [] => []
    | field :: fields =>
        mergeExecutableGroups
          (collectFields schema variableValues objectType objectValue field.selectionSet)
          (collectSubfields schema variableValues objectType objectValue fields)
end

-- Spec 6.4.2 `ResolveFieldValue`: pass the argument values already coerced by
-- `ExecuteField` directly to the supplied resolver.
def resolveFieldValue (resolvers : Resolvers ObjectRef) (parentType fieldName : Name)
    (arguments : CoercedArguments) (source : ResolverValue ObjectRef)
    : Option (ResolverValue ObjectRef) :=
  resolvers.resolve parentType fieldName arguments source

-- Spec 6.3.3 `ExecuteCollectedFields`, 6.4 `ExecuteField`, and 6.4.3 `CompleteValue`:
-- partial fuel-bounded execution model with spec-shaped null bubbling through non-null
-- wrappers. `Except.error` carries a bubbling error count until a nullable parent can
-- turn it into response `null`.
mutual
  def executeCollectedFields
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (source : ResolverValue ObjectRef)
      : List (Name × List ExecutableField) -> Result (List (Name × ResponseValue))
    | [] => .ok ([], 0)
    | (responseName, fields) :: rest =>
        let head :=
          executeField schema resolvers variableValues fuel source responseName fields
        let tail :=
          executeCollectedFields schema resolvers variableValues fuel source rest
        Result.combine List.append head tail

  -- Spec 6.4 `ExecuteField`: resolves one grouped response name once and completes
  -- with merged subselections. Empty field groups and schema lookup misses are
  -- impossible for valid collected fields; this partial model reports them as counted
  -- execution errors rather than silently dropping the response name.
  def executeField
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (source : ResolverValue ObjectRef)
      (responseName : Name)
      : List ExecutableField -> Result (List (Name × ResponseValue))
    | [] => .error 1
    | field :: fields =>
        match fuel with
        | 0 => outOfFuel
        | fuel' + 1 =>
            match schema.lookupField field.parentType field.fieldName with
            | none => .error 1
            | some fieldDefinition =>
                match coerceArgumentValues schema variableValues
                        fieldDefinition.arguments field.arguments with
                | .error =>
                    singleFieldResult responseName
                      (handleFieldError fieldDefinition.outputType)
                | .success coercedArguments =>
                    match resolveFieldValue resolvers field.parentType field.fieldName
                            coercedArguments source with
                    | none =>
                        singleFieldResult responseName
                          (handleFieldError fieldDefinition.outputType)
                    | some resolved =>
                        singleFieldResult responseName
                          (completeValue schema resolvers variableValues
                            fuel' fieldDefinition.outputType
                            (field :: fields) resolved)

  -- Spec 6.4.3 `CompleteValue`: partial; follows null, list, non-null, and composite
  -- completion shape. Scalar/enum result coercion is collapsed to string scalar
  -- acceptance, and abstract type resolution is represented by the runtime object type
  -- carried by `ResolverValue.object`.
  def completeValue
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> TypeRef -> List ExecutableField -> ResolverValue ObjectRef
        -> Result ResponseValue
    | 0, _fieldType, _fields, _value =>
        outOfFuel
    | fuel, .nonNull inner, fields, value =>
        nonNullCompletion
          (completeValue schema resolvers variableValues fuel inner fields value)
    | _fuel + 1, _fieldType, _fields, .null =>
        .ok (.null, 0)
    | _fuel + 1, .named typeName, _fields, .scalar value =>
        if (TypeRef.named typeName).isCompositeBool schema then
          .error 1
        else
          .ok (.scalar value, 0)
    | fuel + 1, .named parentType, fields, source@(.object runtimeType _ref) =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          let completed :=
            executeCollectedFields schema resolvers variableValues fuel source
              (collectSubfields schema variableValues runtimeType source fields)
          catchBubbleAsNull ResponseValue.object completed
        else
          .error 1
    | fuel + 1, .list inner, fields, .list values =>
        let completed :=
          completeValueList schema resolvers variableValues fuel inner fields values
        catchBubbleAsNull ResponseValue.list completed
    | _fuel + 1, .named _typeName, _fields, .list _values =>
        .error 1
    | _fuel + 1, .list _inner, _fields, _value =>
        .error 1

  def completeValueList
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef)
      (fields : List ExecutableField)
      : List (ResolverValue ObjectRef) -> Result (List ResponseValue)
    | [] => .ok ([], 0)
    | value :: values =>
        let head :=
          completeValue schema resolvers variableValues fuel itemType fields value
        let tail :=
          completeValueList schema resolvers variableValues fuel itemType fields values
        Result.combine List.cons head tail
end

-- Spec 6.3.1 `ExecuteRootSelectionSet`
def executeRootSelectionSet
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    : List Selection -> Result (List (Name × ResponseValue))
  | selectionSet =>
      executeCollectedFields schema resolvers variableValues
        fuel source
        (collectFields schema variableValues parentType source selectionSet)

-- Compatibility wrapper of `executeRootSelectionSet` for proof modules using the older
-- name.
def executeSelectionSet
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    : List Selection -> Result (List (Name × ResponseValue)) :=
  executeRootSelectionSet schema resolvers variableValues fuel parentType source

-- Convert the internal selection-set completion result into a response envelope.
def selectionSetResultToResponse : Result (List (Name × ResponseValue)) -> Response
  | .error errors => { data := .null, errors := errors }
  | .ok (fields, errors) => { data := .object fields, errors := errors }

-- Fuel consumed while completing one resolver value before recursive object-field
-- execution. Non-null wrappers reuse the current fuel; list wrappers and the final
-- named type each consume one unit.
def typeRefExecutionCompletionFuel : TypeRef -> Nat
  | .named _name => 1
  | .list inner => typeRefExecutionCompletionFuel inner + 1
  | .nonNull inner => typeRefExecutionCompletionFuel inner

def fieldDefinitionsExecutionCompletionFuel : List FieldDefinition -> Nat
  | [] => 1
  | field :: rest =>
      max (typeRefExecutionCompletionFuel field.outputType)
        (fieldDefinitionsExecutionCompletionFuel rest)

def typeDefinitionsExecutionCompletionFuel : List TypeDefinition -> Nat
  | [] => 1
  | .object objectType :: rest =>
      max (fieldDefinitionsExecutionCompletionFuel objectType.fields)
        (typeDefinitionsExecutionCompletionFuel rest)
  | .interface interfaceType :: rest =>
      max (fieldDefinitionsExecutionCompletionFuel interfaceType.fields)
        (typeDefinitionsExecutionCompletionFuel rest)
  | _typeDefinition :: rest =>
      typeDefinitionsExecutionCompletionFuel rest

-- Schema-aware recursion fuel bound. The operation size bounds the number of
-- response-field boundaries along a path; the schema factor bounds list/type completion
-- between two such boundaries. Explicit-fuel execution remains available independently.
def executeQueryFuelBound (schema : Schema) (operation : Operation) : Nat :=
  operation.size * (typeDefinitionsExecutionCompletionFuel schema.types + 1) + 1

-- Spec 6.2.1 root execution expects a runtime object matching the operation root type.
-- The model still accepts arbitrary host values, but non-root sources produce a counted
-- execution error so equivalence statements are not forced to account for invalid roots.
def rootSourceAppliesBool
    (schema : Schema) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Bool :=
  match runtimeObjectType? source with
  | some objectName =>
      schema.typeIncludesObjectBool (operation.rootType schema) objectName
  | none => false

-- Spec 6.1.2 `CoerceVariableValues` followed by spec 6.2.1 `ExecuteQuery`, at an
-- explicit recursion fuel. Supplied values are prepared with operation defaults before
-- field collection.
def executeQueryWithFuel
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : Response :=
  let coercedVariableValues := coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    selectionSetResultToResponse
      (executeRootSelectionSet schema resolvers coercedVariableValues
        fuel (operation.rootType schema) source operation.selectionSet)
  else
    { data := .null, errors := 1 }

-- Default executable query entry point using the schema-aware completion bound.
def executeQuery
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  executeQueryWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound schema operation) source

-----------------------------------------------------------------------------------------
-- Semantic Equivalence of Responses
-----------------------------------------------------------------------------------------
namespace ResponseValue

def insertObjectFieldSorted (field : Name × ResponseValue)
    : List (Name × ResponseValue) -> List (Name × ResponseValue)
  | [] => [field]
  | candidate :: rest =>
      if field.1 <= candidate.1 then
        field :: candidate :: rest
      else
        candidate :: insertObjectFieldSorted field rest

def sortObjectFieldsByName : List (Name × ResponseValue) -> List (Name × ResponseValue)
  | [] => []
  | field :: rest =>
      insertObjectFieldSorted field (sortObjectFieldsByName rest)

mutual
  def canonical : ResponseValue -> ResponseValue
    | .null => .null
    | .scalar value => .scalar value
    | .list values => .list (canonicalList values)
    | .object fields =>
        .object (sortObjectFieldsByName (canonicalObjectFields fields))

  def canonicalList : List ResponseValue -> List ResponseValue
    | [] => []
    | value :: rest =>
        canonical value :: canonicalList rest

  def canonicalObjectFields : List (Name × ResponseValue) -> List (Name × ResponseValue)
    | [] => []
    | (name, value) :: rest =>
        (name, canonical value) :: canonicalObjectFields rest
end

def semanticEquivalent (left right : ResponseValue) : Prop :=
  canonical left = canonical right

instance semanticEquivalence : SemanticEquivalence ResponseValue where
  equivalent := semanticEquivalent

end ResponseValue
namespace Response

def semanticEquivalent (left right : Response) : Prop :=
  ResponseValue.semanticEquivalent left.data right.data ∧ left.errors = right.errors

instance semanticEquivalence : SemanticEquivalence Response where
  equivalent := semanticEquivalent

end Response

end Execution

end GraphQL
