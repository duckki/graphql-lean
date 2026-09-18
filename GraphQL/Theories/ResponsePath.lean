import GraphQL.Theories.ExecutionReadiness

/-!
GraphQL response paths and selected-field footprints.

A response path is a chain of concrete field steps. The footprint predicate is grounded
directly in `Execution.collectFields` and `Execution.collectSubfields`: it describes which
paths an operation selects under one Boolean assignment, without executing resolvers and
without computing any intermediate response structure. Query inclusion compares two
operations' footprints pathwise in `GraphQL.Theories.QueryInclusion`.
-/

namespace GraphQL
namespace ResponsePath

open Execution

-----------------------------------------------------------------------------------------
-- Response-path syntax
-----------------------------------------------------------------------------------------

-- Field identity and output information at one concrete response position.
structure FieldHead where
  fieldName : Name
  arguments : List Argument
  outputType : TypeRef
deriving Repr

-- One concrete field step in a response path: the concrete object type executing the
-- step, the response name produced, and the field identity behind it.
structure PathStep where
  parentObject : Name
  responseName : Name
  field : FieldHead
deriving Repr

-----------------------------------------------------------------------------------------
-- Selected-path footprint
-----------------------------------------------------------------------------------------

-- A collected executable field has the identity and concrete-object schema entry recorded
-- by one path step. GraphQL field collection ignores argument order, so arguments are
-- compared by the order-insensitive equivalence rather than syntactic equality.
def executableFieldMatchesPathStep (schema : Schema) (field : ExecutableField)
    (step : PathStep)
    : Prop :=
  field.fieldName = step.field.fieldName
  ∧ Argument.argumentsEquivalent field.arguments step.field.arguments
  ∧ ∃ fieldDefinition,
      schema.lookupField step.parentObject step.field.fieldName = some fieldDefinition
      ∧ fieldDefinition.outputType = step.field.outputType

-- A nonempty concrete-object-indexed path occurs in already-collected field groups. Any
-- member of the response-name group may witness the current step; child collection
-- nevertheless merges the selection sets of the entire group, exactly as
-- `Execution.collectSubfields` does. Before collecting those children, the next concrete
-- object must be reachable from the current field's output scope.
def collectedFieldsSelectPath (schema : Schema) (variableValues : VariableValues)
    : List (Name × List ExecutableField) -> List PathStep -> Prop
  | _groupedFields, [] => False
  | groupedFields, [step] =>
      ∃ fields,
        (step.responseName, fields) ∈ groupedFields
        ∧ ∃ field, field ∈ fields ∧ executableFieldMatchesPathStep schema field step
  | groupedFields, step :: next :: rest =>
      ∃ fields,
        (step.responseName, fields) ∈ groupedFields
        ∧ (∃ field, field ∈ fields ∧ executableFieldMatchesPathStep schema field step)
        ∧ schema.typeIncludesObject step.field.outputType.namedType next.parentObject
        ∧ collectedFieldsSelectPath schema variableValues
            (collectSubfields schema variableValues next.parentObject
              (.object next.parentObject PUnit.unit) fields)
            (next :: rest)

-- The selected-field footprint of an operation under one Boolean assignment. Empty paths
-- are not selected. A synthetic object value supplies the concrete root object consulted
-- by fragment applicability during field collection. For permissive operation syntax this
-- proposition describes field selection, not successful field execution; relating it to
-- executable response positions therefore requires operation validity.
def operationSelectsPath (schema : Schema) (operation : Operation) (assignment : BoolCase)
    : List PathStep -> Prop
  | [] => False
  | step :: rest =>
      let variableValues := boolCaseVariableValues assignment
      schema.typeIncludesObject (operation.rootType schema) step.parentObject
      ∧ collectedFieldsSelectPath schema variableValues
          (collectFields schema variableValues (operation.rootType schema)
            (.object step.parentObject PUnit.unit) operation.selectionSet)
          (step :: rest)

end ResponsePath
end GraphQL
