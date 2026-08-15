import GraphQL.Execution

/-!
Sibling-canceling GraphQL query execution.

This algorithm keeps the spec-facing executor's collected-field representation,
resolver behavior, and value-completion rules. The only operational difference is
that a bubbling field result cancels the remaining sibling response positions in
the same collected selection set. It therefore preserves response data and error
presence while potentially counting fewer execution errors than
`GraphQL.Execution`.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionCancelingSiblings

open GraphQL.Execution

variable {ObjectRef : Type}

-- Spec 6.3.3 `ExecuteCollectedFields`, with cancellation after the first field
-- result that bubbles through the current selection set.
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
        match head with
        | .error errors => .error errors
        | .ok _result =>
            let tail :=
              executeCollectedFields schema resolvers variableValues fuel source rest
            Result.combine List.append head tail

  -- Spec 6.4 `ExecuteField`, using sibling-canceling completion recursively.
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

  -- Spec 6.4.3 `CompleteValue`, using sibling-canceling execution for nested
  -- collected selection sets.
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

-- Spec 6.3.1 `ExecuteRootSelectionSet`, with cancellation between collected
-- sibling response positions.
def executeRootSelectionSet
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    : List Selection -> Result (List (Name × ResponseValue))
  | selectionSet =>
      executeCollectedFields schema resolvers variableValues
        fuel source
        (collectFields schema variableValues parentType source selectionSet)

def executeSelectionSet
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    : List Selection -> Result (List (Name × ResponseValue)) :=
  executeRootSelectionSet schema resolvers variableValues fuel parentType source

-- Spec 6.1.2 `CoerceVariableValues` followed by sibling-canceling query
-- execution at an explicit recursion fuel.
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

def executeQuery
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  executeQueryWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound schema operation) source

-- Response data and the presence of execution errors agree, although exact
-- execution-error counts may differ.
def responseDataAndErrorPresenceEquivalent (canceling spec : Response) : Prop :=
  canceling.data = spec.data
  ∧ (spec.errors = 0 -> canceling.errors = 0)
  ∧ (0 < spec.errors -> 0 < canceling.errors)

-- Resolver-parametric correctness statement for sibling-canceling execution.
-- Proof witness:
-- `ExecutionCancelingSiblings.siblingCancelingExecutionPreservesSpecExecution_proof`
-- in `Proofs/GraphQL/Algorithms/ExecutionCancelingSiblings/Semantics.lean`.
def siblingCancelingExecutionPreservesSpecExecution
    (schema : Schema) (operation : Operation)
    : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef)
    variableValues fuel (source : ResolverValue ObjectRef),
    responseDataAndErrorPresenceEquivalent
      (executeQueryWithFuel schema resolvers variableValues operation fuel source)
      (GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
        operation fuel source)

end ExecutionCancelingSiblings
end Algorithms

end GraphQL
