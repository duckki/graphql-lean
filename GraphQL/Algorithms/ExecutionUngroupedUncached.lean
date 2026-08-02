import GraphQL.Execution
import GraphQL.Algorithms.ExecutionCancelingSiblings
import GraphQL.Theories.NormalForm

/-!
Uncached variant of the ungrouped GraphQL query execution semantics.

This module is an alternative implementation of the same query fragment as
`GraphQL.Execution`. It is a specialized version of `ExecutionUngrouped` that drops
resolved-value caching: later compatible composite selections reuse the previous
completed response value, but call the resolver again to recover the source value for
additional subselections. This is a useful simplification when calling resolvers is as
cheap as caching their returned source values.

Like `ExecutionUngrouped`, it preserves response data and error presence, but not exact
error counts, while visiting selections directly instead of first constructing the
complete collected-fields map. Field visits normally call the resolver. Later visits
to the same response key reuse the previous value: composite values are revisited
through their subselections, while a previous `null` is final for that response
position. A null bubble cancels remaining sibling selections in the same selection
list, so this model may count fewer sibling and subfield errors than collected
execution.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached

open GraphQL.Execution

instance : Inhabited ResponseValue := ⟨.null⟩

def lookupResponseField? (responseName : Name)
    : List (Name × ResponseValue) -> Option ResponseValue
  | [] => none
  | (fieldResponseName, response) :: rest =>
      if fieldResponseName == responseName then
        some response
      else
        lookupResponseField? responseName rest

def responseObjectField? (responseName : Name) : ResponseValue -> Option ResponseValue
  | .object fields => lookupResponseField? responseName fields
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

-- A previous response value is always reusable as the completion accumulator. This
-- helper only decides when that previous value is already final for this response
-- position, so field execution can stop instead of resolving and completing more
-- subfields.
def reusablePreviousValue? (schema : Schema)
    : TypeRef -> Option ResponseValue -> Option ResponseValue
  | _fieldType, none =>
      none
  | _fieldType, some .null =>
      some .null
  | fieldType, some previous =>
      if fieldType.isCompositeBool schema then
        none
      else
        some previous

def reuseOrCreateObject? : Option ResponseValue -> Option ResponseValue
  | none => some (.object [])
  | some previous@(.object _fields) => some previous
  | some _ => none

def reuseOrCreateList? : Option ResponseValue -> Option (List ResponseValue)
  | none => some []
  | some (.list previousValues) => some previousValues
  | some _ => none

mutual
  def mergeResponse (existing incoming : ResponseValue) : ResponseValue :=
    match existing, incoming with
    | .null, _ =>
        .null
    | _, .null =>
        .null
    | .object existingFields, .object incomingFields =>
        .object (mergeResponseFields existingFields incomingFields)
    | .list existingValues, .list incomingValues =>
        .list (mergeResponseLists existingValues incomingValues)
    | _, _ => existing

  def mergeResponseFields
      : List (Name × ResponseValue) -> List (Name × ResponseValue)
        -> List (Name × ResponseValue)
    | existingFields, [] => existingFields
    | existingFields, (responseName, incoming) :: rest =>
        mergeResponseFields (mergeResponseField responseName incoming existingFields) rest

  def mergeResponseField (responseName : Name) (incoming : ResponseValue)
      : List (Name × ResponseValue) -> List (Name × ResponseValue)
    | [] => [(responseName, incoming)]
    | (fieldResponseName, existing) :: rest =>
        if fieldResponseName == responseName then
          (fieldResponseName, mergeResponse existing incoming) :: rest
        else
          (fieldResponseName, existing) :: mergeResponseField responseName incoming rest

  def mergeResponseLists : List ResponseValue -> List ResponseValue -> List ResponseValue
    | [], _incomingValues => []
    | existingValues, [] => existingValues
    | existing :: existingRest, incoming :: incomingRest =>
        mergeResponse existing incoming :: mergeResponseLists existingRest incomingRest
end

abbrev VisitStatus : Type :=
  Result Unit

def visitOk (errors : Nat := 0) : VisitStatus :=
  .ok ((), errors)

-- Extract the value from the incoming `Result ResponseValue`, returning `.null` for
-- errors and null bubbles.
def resultValueOrNull : Result ResponseValue -> ResponseValue
  | .error _errors => .null
  | .ok (value, _errors) => value

-- Extract the status from the incoming `Result ResponseValue`.
def resultStatus {α : Type} : Result α -> VisitStatus
  | .error errors => .error errors
  | .ok (_value, errors) => visitOk errors

def mergeResponseFieldIntoObject (responseName : Name) (incoming : ResponseValue)
    : ResponseValue -> ResponseValue
  | .object fields => .object (mergeResponseField responseName incoming fields)
  | response => response

def mergeResponseFieldResult (responseName : Name)
    (fieldResult : Result ResponseValue) (output : ResponseValue)
    : ResponseValue × VisitStatus :=
  (
    mergeResponseFieldIntoObject responseName (resultValueOrNull fieldResult) output,
    resultStatus fieldResult
  )

def combineVisitStatus (left right : VisitStatus) : VisitStatus :=
  Result.combine (fun _unit _unit => ()) left right

def catchVisitBubbleAsNull (value : ResponseValue) (status : VisitStatus)
    : Result ResponseValue :=
  match status with
  | .error errors => .ok (.null, errors)
  | .ok (_unit, errors) => .ok (value, errors)

mutual
  -- Spec 6.3.2 `CollectFields`/`executeCollectedFields`: visitor over a selection list
  -- without constructing a grouped field map.
  def visitSubfields {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
      : List Selection -> ResponseValue -> ResponseValue × VisitStatus
    | [], output => (output, visitOk)
    | selection :: rest, output =>
        let head :=
          visitSelection schema resolvers variableValues fuel parentType source
            selection output
        match head.snd with
        | .error errors => (head.fst, .error errors)
        | .ok _ok =>
            let tail :=
              visitSubfields schema resolvers variableValues fuel parentType source
                rest head.fst
            (tail.fst, combineVisitStatus head.snd tail.snd)

  -- Spec 6.3.2 `CollectFields`/`executeCollectedFields` selection step: handles built-in
  -- directives and inline fragments while updating an output object directly.
  def visitSelection {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
      : Selection -> ResponseValue -> ResponseValue × VisitStatus
    | .field responseName fieldName arguments directives selectionSet, output =>
        if selectionDirectivesAllowBool variableValues directives then
          let previous? := responseObjectField? responseName output
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
          (output, visitOk)
    | .inlineFragment none directives selectionSet, output =>
        if !selectionDirectivesAllowBool variableValues directives then
          (output, visitOk)
        else
          visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet output
    | .inlineFragment (some typeCondition) directives selectionSet, output =>
        if !selectionDirectivesAllowBool variableValues directives then
          (output, visitOk)
        else if !doesFragmentTypeApplyBool schema parentType source typeCondition then
          (output, visitOk)
        else
          visitSubfields schema resolvers variableValues fuel parentType source
            selectionSet output

  -- Spec 6.4 `ExecuteField`: resolves a field unless the declared return type is
  -- non-composite and a previous response slice can be reused. Schema lookup misses are
  -- invalid-operation cases and are modeled as counted execution errors. A previous
  -- `null` is reused after the field definition is found because it may represent an
  -- already-counted field error or null bubble.
  def executeField {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (completionFuel : Nat)
      (source : ResolverValue ObjectRef) (previous? : Option ResponseValue)
      (field : ExecutableField)
      : Result ResponseValue :=
    match schema.lookupField field.parentType field.fieldName with
    | none => .error 1
    | some fieldDefinition =>
        match reusablePreviousValue? schema fieldDefinition.outputType previous? with
        | some previous => .ok (previous, 0)
        | none =>
            match resolvers.resolve field.parentType field.fieldName
                    field.arguments source with
            | none =>
                handleFieldError fieldDefinition.outputType
            | some resolved =>
                completeValue schema resolvers variableValues completionFuel
                  fieldDefinition.outputType field.selectionSet resolved previous?

  -- Spec 6.4.3 `CompleteValue`: partial; mirrors the spec executor's null/list/non-null
  -- completion while threading an optional previous response slice for ungrouped
  -- revisits. Scalar/enum result coercion and error metadata remain abstract.
  def completeValue {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> TypeRef -> List Selection -> ResolverValue ObjectRef
        -> Option ResponseValue -> Result ResponseValue
    | 0, _fieldType, _selectionSet, _value, _previous? =>
        outOfFuel
    | _fuel, _fieldType, _selectionSet, _value, some .null =>
        .ok (.null, 0)
    | _fuel, _fieldType, _selectionSet, _value, some (.scalar _previousValue) =>
        -- Previous scalar values are reusable for valid non-composite return types, so
        -- reaching completion with one indicates a response-shape mismatch.
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
          match reuseOrCreateObject? previous? with
          | some output =>
              let visited :=
                visitSubfields schema resolvers variableValues fuel runtimeType source
                  selectionSet output
              catchVisitBubbleAsNull visited.fst visited.snd
          | none => .error 1
        else
          .error 1
    | fuel + 1, .list inner, selectionSet, .list values, previous? =>
        match reuseOrCreateList? previous? with
        | some previousValues =>
            let completed :=
              completeValueList schema resolvers variableValues fuel inner
                selectionSet values previousValues
            catchBubbleAsNull ResponseValue.list completed
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
      : List (ResolverValue ObjectRef) -> List ResponseValue
        -> Result (List ResponseValue)
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

-- Spec 6.3.1 `ExecuteRootSelectionSet`
def executeRootSelectionSet {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet: List Selection)
    : Result (List (Name × ResponseValue)) :=
  let visited :=
    visitSubfields schema resolvers variableValues fuel parentType source
      selectionSet (.object [])
  match visited.snd with
  | .error errors => .error errors
  | .ok (_unit, errors) =>
      match visited.fst with
      | .object fields => .ok (fields, errors)
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
def responseDataAndErrorPresenceEquivalent (ungrouped spec : GraphQL.Execution.Response)
    : Prop :=
  ungrouped.data = spec.data
  ∧ (spec.errors = 0 -> ungrouped.errors = 0)
  ∧ (0 < spec.errors -> 0 < ungrouped.errors)

-- Resolver-parametric correctness statement for ungrouped execution. Ungrouped execution
-- preserves response data and whether execution errors are present, but it may count
-- fewer sub-field errors after a null-bubble has already set the response position to
-- `null`. See example `duplicateHeroNullBubbleQuery` in
-- `Tests/GraphQL/Algorithms/ExecutionUngrouped.lean`.
-- Proof witness:
-- `ExecutionUngroupedUncached.ungroupedExecutionPreservesSpecExecution_proof`
-- in `Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.
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
-- Proof witness:
-- `ExecutionUngroupedUncached.ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof`
-- in `Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.
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

end ExecutionUngroupedUncached
end Algorithms

end GraphQL
