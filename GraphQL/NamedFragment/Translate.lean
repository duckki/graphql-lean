import GraphQL.NamedFragment.Inline

/-! Translation from spread-free named-fragment operations to core operations. -/

namespace GraphQL
namespace NamedFragment
namespace Translate

mutual
  def reduceSelection : Selection -> List GraphQL.Selection
    | .field responseName fieldName arguments directives selectionSet =>
        [.field responseName fieldName arguments directives
          (reduceSelectionSet selectionSet)]
    | .inlineFragment typeCondition directives selectionSet =>
        [.inlineFragment typeCondition directives (reduceSelectionSet selectionSet)]
    | .fragmentSpread _fragmentName _directives => []

  def reduceSelectionSet : List Selection -> List GraphQL.Selection
    | [] => []
    | selection :: rest =>
        reduceSelection selection ++ reduceSelectionSet rest
end

def reduceOperation (operation : Operation) : GraphQL.Operation :=
  {
    name := operation.name
    operationType := operation.operationType
    variableDefinitions := operation.variableDefinitions
    selectionSet := reduceSelectionSet operation.selectionSet
  }

end Translate

namespace Semantics

-- Reducing an inlined operation preserves execution semantics.
-- Witness: `GraphQL.NamedFragment.Semantics.fragmentAwareInlinedExecutionEquivalentToSpecExecution_holds`.
def fragmentAwareInlinedExecutionEquivalentToSpecExecution
    (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
  -> operationInlined operation
  -> ∀ {ObjectRef : Type} (resolvers : GraphQL.Execution.Resolvers ObjectRef)
        variableValues fuel (source : GraphQL.Execution.ResolverValue ObjectRef),
      Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          (Translate.reduceOperation operation) fuel source

-- Inlining and then reducing preserves execution semantics.
-- Witness: `GraphQL.NamedFragment.Semantics.fragmentAwareInlineExecutionEquivalentToSpecExecution_holds`.
def fragmentAwareInlineExecutionEquivalentToSpecExecution
    (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
  -> ∀ {ObjectRef : Type} (resolvers : GraphQL.Execution.Resolvers ObjectRef)
        variableValues fuel (source : GraphQL.Execution.ResolverValue ObjectRef),
      Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          (Translate.reduceOperation (Inline.inlineOperation operation)) fuel source

-- Reducing an inlined operation preserves validity.
-- Witness: `GraphQL.NamedFragment.Semantics.fragmentAwareInlinedValidityPreservedToSpec_holds`.
def fragmentAwareInlinedValidityPreservedToSpec (schema : Schema) (operation : Operation)
    : Prop :=
  GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
  -> operationInlined operation
  -> GraphQL.Validation.operationDefinitionValid schema
      (Translate.reduceOperation operation)

-- Inlining and then reducing preserves validity.
-- Witness: `GraphQL.NamedFragment.Semantics.fragmentAwareInlineValidityPreservedToSpec_holds`.
def fragmentAwareInlineValidityPreservedToSpec (schema : Schema) (operation : Operation)
    : Prop :=
  GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation
  -> GraphQL.Validation.operationDefinitionValid schema
      (Translate.reduceOperation (Inline.inlineOperation operation))

end Semantics
end NamedFragment
end GraphQL
