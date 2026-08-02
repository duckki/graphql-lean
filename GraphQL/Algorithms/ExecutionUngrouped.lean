import GraphQL.Execution
import GraphQL.Algorithms.ExecutionCancelingSiblings
import GraphQL.Theories.NormalForm

/-!
Alternative GraphQL query execution semantics.

This module is an alternative implementation of the same query fragment as
`GraphQL.Execution`. It preserves response data and error presence, but not exact
error counts, while visiting selections directly instead of first constructing the
complete collected-fields map.

Ungrouped execution uses an internal field-level cache. The cache is the presence and
completion accumulator for response positions, and completed composite positions retain
the first raw resolver source needed by later compatible subselections. Public response
data is produced by stripping away the extra metadata. A null bubble cancels remaining
sibling selections in the same selection list, so this model may count fewer sibling
and subfield errors than collected execution.

This algorithm is intended to be lighter in CPU and memory usage than collected
execution for synchronous executors: it avoids constructing the full field map up
front, reuses field-level source state, and can stop walking sibling selections as soon
as null bubbling determines the enclosing result.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

inductive FieldCacheValue (ObjectRef : Type) where
  | null
  | scalar (value : String)
  | object
    (source : ResolverValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
  | list
    (sourceValues? : Option (List (ResolverValue ObjectRef)))
    (values : List (FieldCacheValue ObjectRef))
deriving Repr

instance {ObjectRef : Type} : Inhabited (FieldCacheValue ObjectRef) :=
  ⟨.null⟩

mutual
  def FieldCacheValue.output {ObjectRef : Type}
      : FieldCacheValue ObjectRef -> ResponseValue
    | .null => .null
    | .scalar value => .scalar value
    | .object _source fields => .object (outputFields fields)
    | .list _sourceValues? values => .list (outputValues values)

  def outputValues {ObjectRef : Type}
      : List (FieldCacheValue ObjectRef) -> List ResponseValue
    | [] => []
    | value :: rest => value.output :: outputValues rest

  def outputFields {ObjectRef : Type}
      : List (Name × FieldCacheValue ObjectRef) -> List (Name × ResponseValue)
    | [] => []
    | (responseName, value) :: rest => (responseName, value.output) :: outputFields rest
end

def outputResult {α β : Type} (output : α -> β) : Result α -> Result β
  | .error errors => .error errors
  | .ok (value, errors) => .ok (output value, errors)

def outputRootResult {ObjectRef : Type}
    : Result (List (Name × FieldCacheValue ObjectRef))
      -> Result (List (Name × ResponseValue)) :=
  outputResult (outputFields (ObjectRef := ObjectRef))

def lookupField? {ObjectRef : Type} (responseName : Name)
    : List (Name × FieldCacheValue ObjectRef) -> Option (FieldCacheValue ObjectRef)
  | [] => none
  | (fieldResponseName, response) :: rest =>
      if fieldResponseName == responseName then
        some response
      else
        lookupField? responseName rest

def objectField? {ObjectRef : Type} (responseName : Name)
    : FieldCacheValue ObjectRef -> Option (FieldCacheValue ObjectRef)
  | .object _source fields => lookupField? responseName fields
  | _ => none

def executableField (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    : ExecutableField :=
  {
    parentType := parentType
    responseName := responseName
    fieldName := fieldName
    arguments := arguments
    selectionSet := selectionSet
  }

-- Values with no retained composite source are final for this response position.
def reusablePreviousValue?
    : FieldCacheValue ObjectRef -> Option (FieldCacheValue ObjectRef)
  | .null => some .null
  | .scalar value => some (.scalar value)
  | .list none values => some (.list none values)
  | .object _source _fields => none
  | .list (some _sourceValues) _values => none

def reuseOrCreateObject? (source : ResolverValue ObjectRef)
    : Option (FieldCacheValue ObjectRef) -> Option (FieldCacheValue ObjectRef)
  | none => some (.object source [])
  | some previous@(.object _source _fields) => some previous
  | some _ => none

def reuseOrCreateList? (schema : Schema) (itemType : TypeRef)
    (sourceValues : List (ResolverValue ObjectRef))
    : Option (FieldCacheValue ObjectRef)
      -> Option
          (Option (List (ResolverValue ObjectRef)) × List (FieldCacheValue ObjectRef))
  | none =>
      some
        (
          if itemType.isCompositeBool schema then
            some sourceValues
          else
            none,
          []
        )
  | some (.list sourceValues? previousValues) => some (sourceValues?, previousValues)
  | some _ => none

mutual
  def mergeResponse
      : FieldCacheValue ObjectRef -> FieldCacheValue ObjectRef
        -> FieldCacheValue ObjectRef
    | .null, _ => .null
    | _, .null => .null
    | .object existingSource existingFields, .object _incomingSource incomingFields =>
        .object existingSource (mergeResponseFields existingFields incomingFields)
    | .list existingSourceValues? existingValues,
      .list _incomingSourceValues? incomingValues =>
        .list existingSourceValues? (mergeResponseLists existingValues incomingValues)
    | existing, _incoming => existing

  def mergeResponseFields
      : List (Name × FieldCacheValue ObjectRef) -> List (Name × FieldCacheValue ObjectRef)
        -> List (Name × FieldCacheValue ObjectRef)
    | existingFields, [] => existingFields
    | existingFields, (responseName, incoming) :: rest =>
        mergeResponseFields (mergeResponseField responseName incoming existingFields) rest

  def mergeResponseField (responseName : Name) (incoming : FieldCacheValue ObjectRef)
      : List (Name × FieldCacheValue ObjectRef) -> List (Name × FieldCacheValue ObjectRef)
    | [] => [(responseName, incoming)]
    | (fieldResponseName, existing) :: rest =>
        if fieldResponseName == responseName then
          (fieldResponseName, mergeResponse existing incoming) :: rest
        else
          (fieldResponseName, existing) :: mergeResponseField responseName incoming rest

  def mergeResponseLists
      : List (FieldCacheValue ObjectRef) -> List (FieldCacheValue ObjectRef)
        -> List (FieldCacheValue ObjectRef)
    | [], _incomingValues => []
    | existingValues, [] => existingValues
    | existing :: existingRest, incoming :: incomingRest =>
        mergeResponse existing incoming :: mergeResponseLists existingRest incomingRest
end

abbrev VisitStatus : Type :=
  Result Unit

structure VisitResult (ObjectRef : Type) where
  value : FieldCacheValue ObjectRef
  status : VisitStatus

def visitOk (errors : Nat := 0) : VisitStatus :=
  .ok ((), errors)

-- Extract the value from the incoming field-result, returning `.null` for errors and
-- null bubbles.
def resultValueOrNull {ObjectRef : Type}
    : Result (FieldCacheValue ObjectRef) -> FieldCacheValue ObjectRef
  | .error _errors => .null
  | .ok (value, _errors) => value

-- Extract the visitor status from the incoming field-result.
def resultStatus {α : Type} : Result α -> VisitStatus
  | .error errors => .error errors
  | .ok (_value, errors) => visitOk errors

def mergeResponseFieldIntoObject (responseName : Name)
    (incoming : FieldCacheValue ObjectRef)
    : FieldCacheValue ObjectRef -> FieldCacheValue ObjectRef
  | .object source fields =>
      .object source (mergeResponseField responseName incoming fields)
  | response => response

def mergeResponseFieldResult (responseName : Name)
    (fieldResult : Result (FieldCacheValue ObjectRef))
    (output : FieldCacheValue ObjectRef)
    : VisitResult ObjectRef :=
  {
    value :=
      mergeResponseFieldIntoObject responseName (resultValueOrNull fieldResult) output
    status := resultStatus fieldResult
  }

def combineVisitStatus (left right : VisitStatus) : VisitStatus :=
  Result.combine (fun _unit _unit => ()) left right

def catchVisitBubbleAsNull (value : FieldCacheValue ObjectRef) (status : VisitStatus)
    : Result (FieldCacheValue ObjectRef) :=
  match status with
  | .error errors => .ok (.null, errors)
  | .ok (_unit, errors) => .ok (value, errors)

def handleFieldError (fieldType : TypeRef) : Result (FieldCacheValue ObjectRef) :=
  match fieldType with
  | .nonNull _inner => .error 1
  | _ => .ok (.null, 1)

def nonNullCompletion
    : Result (FieldCacheValue ObjectRef) -> Result (FieldCacheValue ObjectRef)
  | .error errors => .error errors
  | .ok (.null, errors) =>
      .error
      <| match errors with
          | 0 => 1
          | errors + 1 => errors + 1
  | .ok (response, errors) => .ok (response, errors)

def catchBubbleAsNull {α : Type} (wrap : α -> FieldCacheValue ObjectRef)
    : Result α -> Result (FieldCacheValue ObjectRef)
  | .error errors => .ok (.null, errors)
  | .ok (value, errors) => .ok (wrap value, errors)

mutual
  -- Spec 6.3.2 `CollectFields`/`executeCollectedFields`: visitor over a selection list
  -- without constructing a grouped field map.
  def visitSubfields {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
      : List Selection -> FieldCacheValue ObjectRef -> VisitResult ObjectRef
    | [], output =>
        {
          value := output
          status := visitOk
        }
    | selection :: rest, output =>
        let head :=
          visitSelection schema resolvers variableValues fuel parentType source
            selection output
        match head.status with
        | .error errors =>
            {
              value := head.value
              status := .error errors
            }
        | .ok _ok =>
            let tail :=
              visitSubfields schema resolvers variableValues fuel parentType source
                rest head.value
            {
              value := tail.value
              status := combineVisitStatus head.status tail.status
            }

  -- Spec 6.3.2 `CollectFields`/`executeCollectedFields` selection step: handles built-in
  -- directives and inline fragments while updating the field cache directly.
  def visitSelection {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
      : Selection -> FieldCacheValue ObjectRef -> VisitResult ObjectRef
    | .field responseName fieldName arguments directives selectionSet, output =>
        if selectionDirectivesAllowBool variableValues directives then
          let previous? := objectField? responseName output
          let fieldResult :=
            match fuel with
            | 0 =>
                match previous? with
                | some previous => .ok (previous, 0)
                | none => outOfFuel
            | fuel' + 1 =>
                let field :=
                  executableField parentType responseName fieldName arguments selectionSet
                executeField schema resolvers variableValues fuel' source previous? field
          mergeResponseFieldResult responseName fieldResult output
        else
          {
            value := output
            status := visitOk
          }
    | .inlineFragment none directives selectionSet, output =>
        if !selectionDirectivesAllowBool variableValues directives then
          {
            value := output
            status := visitOk
          }
        else
          visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet output
    | .inlineFragment (some typeCondition) directives selectionSet, output =>
        if !selectionDirectivesAllowBool variableValues directives then
          {
            value := output
            status := visitOk
          }
        else if !doesFragmentTypeApplyBool schema parentType source typeCondition then
          {
            value := output
            status := visitOk
          }
        else
          visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet output

  -- Spec 6.4 `ExecuteField`: resolves a field once per response position. Later visits
  -- use the cached raw source stored in the field cache and thread the previous
  -- completed value through recursive completion.
  def executeField {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (completionFuel : Nat)
      (source : ResolverValue ObjectRef) (previous? : Option (FieldCacheValue ObjectRef))
      (field : ExecutableField)
      : Result (FieldCacheValue ObjectRef) :=
    match previous? with
    | some previous =>
        match reusablePreviousValue? previous with
        | some final => .ok (final, 0)
        | none =>
            match previous with
            | .object previousSource _fields =>
                match schema.lookupField field.parentType field.fieldName with
                | none => .error 1
                | some fieldDefinition =>
                    completeValue schema resolvers variableValues completionFuel
                      fieldDefinition.outputType field.selectionSet previousSource
                      (some previous)
            | .list (some sourceValues) _values =>
                match schema.lookupField field.parentType field.fieldName with
                | none => .error 1
                | some fieldDefinition =>
                    completeValue schema resolvers variableValues completionFuel
                      fieldDefinition.outputType field.selectionSet (.list sourceValues)
                      (some previous)
            | _ => .error 1
    | none =>
        match schema.lookupField field.parentType field.fieldName with
        | none => .error 1
        | some fieldDefinition =>
            match resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
            | none =>
                handleFieldError fieldDefinition.outputType
            | some resolved =>
                completeValue schema resolvers variableValues completionFuel
                  fieldDefinition.outputType field.selectionSet resolved none

  -- Spec 6.4.3 `CompleteValue`: partial; mirrors the spec executor's null/list/non-null
  -- completion while threading an optional previous field-cache value for ungrouped
  -- revisits. Scalar/enum result coercion and error metadata remain abstract.
  def completeValue {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> TypeRef -> List Selection -> ResolverValue ObjectRef
        -> Option (FieldCacheValue ObjectRef) -> Result (FieldCacheValue ObjectRef)
    | 0, _fieldType, _selectionSet, _value, _previous? =>
        outOfFuel
    | _fuel, _fieldType, _selectionSet, _value, some .null =>
        .ok (.null, 0)
    | _fuel, _fieldType, _selectionSet, _value, some (.scalar _previousValue) =>
        -- Previous scalar values are reusable before completion, so reaching this branch
        -- indicates a response-shape mismatch.
        .error 1
    | fuel, .nonNull inner, selectionSet, value, previous? =>
        nonNullCompletion
          (completeValue schema resolvers variableValues
            fuel inner selectionSet value previous?)
    | _fuel + 1, _fieldType, _selectionSet, .null, _previous? =>
        -- The new `.null` value may be a null bubble from a subfield visit.
        .ok (.null, 0)
    | _fuel + 1, .named typeName, _selectionSet, .scalar value, previous? =>
        match previous? with
        | none =>
            if (TypeRef.named typeName).isCompositeBool schema then
              .error 1
            else
              .ok (.scalar value, 0)
        | some _ => .error 1
    | fuel + 1,
      .named parentType,
      selectionSet,
      source@(.object runtimeType _ref),
      previous? =>
        if schema.typeIncludesObjectBool parentType runtimeType then
          match reuseOrCreateObject? source previous? with
          | some output =>
              let visited :=
                visitSubfields schema resolvers variableValues fuel runtimeType source
                  selectionSet output
              catchVisitBubbleAsNull visited.value visited.status
          | none => .error 1
        else
          .error 1
    | fuel + 1, .list inner, selectionSet, .list values, previous? =>
        match reuseOrCreateList? schema inner values previous? with
        | some (sourceValues?, previousValues) =>
            let completed :=
              completeValueList schema resolvers variableValues fuel inner
                selectionSet values previousValues
            catchBubbleAsNull (FieldCacheValue.list sourceValues?) completed
        | none => .error 1
    | _fuel + 1, .named _typeName, _selectionSet, .list _values, _previous? =>
        .error 1
    | _fuel + 1, .list _inner, _selectionSet, _value, _previous? =>
        .error 1

  def completeValueList {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (itemType : TypeRef)
      (selectionSet : List Selection)
      : List (ResolverValue ObjectRef) -> List (FieldCacheValue ObjectRef)
        -> Result (List (FieldCacheValue ObjectRef))
    | [], _ :: _ => .error 1
    | [], [] => .ok ([], 0)
    | value :: values, previousValues =>
        let previous? := previousValues.head?
        let remainingPrevious := previousValues.tail
        let head :=
          match previous? with
          | some .null => .ok (.null, 0)
          | _ =>
              completeValue schema resolvers variableValues
                fuel itemType selectionSet value previous?
        let tail :=
          completeValueList schema resolvers variableValues fuel itemType
            selectionSet values remainingPrevious
        Result.combine List.cons head tail
end

-- Spec 6.3.1 `ExecuteRootSelectionSet`, after projecting away field-cache metadata.
def executeRootSelectionSet {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Result (List (Name × ResponseValue)) :=
  let visited :=
    visitSubfields schema resolvers variableValues fuel parentType source
      selectionSet (.object source [])
  outputRootResult
  <| match visited.status with
      | .error errors => .error errors
      | .ok (_unit, errors) =>
          match visited.value with
          | .object _source fields => .ok (fields, errors)
          | _ => .error (errors + 1)

-- Compatibility wrapper of `executeRootSelectionSet` for proof modules using the older
-- name.
def executeSelectionSet {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    : List Selection -> Result (List (Name × ResponseValue)) :=
  executeRootSelectionSet schema resolvers variableValues fuel parentType source

-- Spec 6.2.1 `ExecuteQuery`
def executeQueryWithFuel {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : Response :=
  let coercedVariableValues :=
    GraphQL.Execution.coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    Execution.selectionSetResultToResponse
      (executeRootSelectionSet schema resolvers coercedVariableValues
        fuel (operation.rootType schema) source operation.selectionSet)
  else
    { data := .null, errors := 1 }

-- Spec 6.2.1 `ExecuteQuery`: Default executable query entry point using the local
-- operation-derived fuel bound.
def executeQuery {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  executeQueryWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound operation) source

-----------------------------------------------------------------------------------------
-- Correctness theorem: ungroupedExecutionPreservesSpecExecution
-----------------------------------------------------------------------------------------

-- A helper definition where response data is equal and the presence of execution errors
-- stays the same, but the number of errors may differ.
def responseDataAndErrorPresenceEquivalent (ungrouped spec : Response) : Prop :=
  ungrouped.data = spec.data
  ∧ (spec.errors = 0 -> ungrouped.errors = 0)
  ∧ (0 < spec.errors -> 0 < ungrouped.errors)

-- Resolver-parametric correctness statement for ungrouped execution. Ungrouped execution
-- preserves response data and whether execution errors are present, but it may count
-- fewer sub-field errors after a null-bubble has already set the response position to
-- `null`. See example `duplicateHeroNullBubbleQuery` in
-- `Tests/GraphQL/Algorithms/ExecutionUngrouped.lean`.
def ungroupedExecutionPreservesSpecExecution (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
        variableValues fuel (source : ResolverValue ObjectRef),
      NormalForm.operationBoolVarsComplete operation
        (GraphQL.Execution.coerceVariableValues operation variableValues)
      -> responseDataAndErrorPresenceEquivalent
          (executeQueryWithFuel schema resolvers variableValues operation fuel source)
          (GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
            operation fuel source)

-- Resolver-parametric equivalence between ungrouped execution and the
-- sibling-canceling collected executor. The equivalence includes response data
-- and error presence, but not the exact `Nat` error count. Collection groups
-- later occurrences of a response name with its first occurrence, which can
-- move their errors before an interleaved sibling that bubbles; syntax-order
-- ungrouped execution may cancel those later occurrences instead.
def ungroupedExecutionEquivalentToCancelingSiblingsExecution
    (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
        variableValues fuel (source : ResolverValue ObjectRef),
      NormalForm.operationBoolVarsComplete operation
        (GraphQL.Execution.coerceVariableValues operation variableValues)
      -> responseDataAndErrorPresenceEquivalent
          (executeQueryWithFuel schema resolvers variableValues operation fuel source)
          (ExecutionCancelingSiblings.executeQueryWithFuel schema resolvers
            variableValues operation fuel source)

end ExecutionUngrouped
end Algorithms

end GraphQL
