import GraphQL.Execution

/-!
Data-only projections of the response-producing execution model.

These declarations are compatibility helpers for proof surfaces that reason only about
response data. The spec-facing executor in `GraphQL.Execution` returns a response
envelope with data and execution-error count.
-/

namespace GraphQL

namespace Execution

variable {ObjectRef : Type}

def completeValueData
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (fieldType : TypeRef)
    (fields : List ExecutableField) (value : ResolverValue ObjectRef)
    : ResponseValue :=
  Result.getD .null
    (completeValue schema resolvers variableValues fuel fieldType fields value)

def executeFieldData
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (responseName : Name) (fields : List ExecutableField)
    : List (Name × ResponseValue) :=
  Result.getD []
    (executeField schema resolvers variableValues fuel source responseName fields)

def executeCollectedFieldsData
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (fields : List (Name × List ExecutableField))
    : List (Name × ResponseValue) :=
  Result.getD []
    (executeCollectedFields schema resolvers variableValues fuel source fields)

def executeRootSelectionSetData
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : List (Name × ResponseValue) :=
  Result.getD []
    (executeRootSelectionSet schema resolvers variableValues fuel parentType
      source selectionSet)

def executeSelectionSetData
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : List (Name × ResponseValue) :=
  executeRootSelectionSetData schema resolvers variableValues fuel parentType
    source selectionSet

-- Compatibility data projection for proof modules that predate the response envelope.
def executeQueryDataWithFuel
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : ResponseValue :=
  (executeQueryWithFuel schema resolvers variableValues operation fuel source).data

-- Default compatibility data projection using the local operation-derived fuel bound.
def executeQueryData
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : ResponseValue :=
  executeQueryDataWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound operation) source

end Execution

end GraphQL
