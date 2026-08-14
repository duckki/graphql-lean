import GraphQL.Algorithms.ExecutionUngroupedUncached

/-!
Alternative GraphQL query execution semantics.

This legacy eager model is retained only as a proof reference for the canceling
implementation. It is otherwise the same proof-facing implementation of the same
query fragment as
`GraphQL.Execution`. It preserves response data and error presence, but not exact
error counts, while visiting selections directly instead of first constructing the
complete collected-fields map. Field visits normally call the resolver. Later visits
to the same response key reuse the previous value: composite values are revisited
through their subselections, while a previous `null` short-circuits sibling
subselections and may therefore count fewer subfield errors than collected execution.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

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
            match resolveFieldValue schema resolvers variableValues fieldDefinition
                    field.parentType field.fieldName field.arguments source with
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
-- Proof witness: `Eager.ungroupedExecutionPreservesSpecExecution_proof` in
-- `Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.
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

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
