import GraphQL.Theories.QueryInclusion

/-!
GraphQL response paths and path-based syntactic query inclusion.

A response path is a chain of concrete field steps. The footprint predicate is grounded
directly in `Execution.collectFields` and `Execution.collectSubfields`: it describes which
paths an operation selects under one Boolean assignment, without executing resolvers and
without computing any intermediate response structure. Path-based inclusion then compares
two operations' footprints pathwise. It is oriented like `QueryInclusion.includes`: the
left operation must select every path the right operation selects.
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
-- Selected-field footprint
-----------------------------------------------------------------------------------------

-- A collected executable field has the identity and concrete-object schema entry recorded
-- by one path step. GraphQL field collection ignores argument order, so arguments are
-- compared by the order-insensitive equivalence rather than syntactic equality.
def executableFieldMatchesPathStep (schema : Schema) (field : ExecutableField)
    (step : PathStep)
    : Prop :=
  field.responseName = step.responseName
  ∧ field.fieldName = step.field.fieldName
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

-----------------------------------------------------------------------------------------
-- Path-based syntactic query inclusion
-----------------------------------------------------------------------------------------

-- Path-based syntactic query inclusion. `left` includes `right` when shared variable
-- definitions have the same types and equivalent defaults and, under every Boolean
-- assignment covering the comparison condition variables, every response path selected by
-- `right` is selected by `left`. Path steps carry the right operation's own argument
-- syntax, and the step matcher absorbs argument reordering, so a shared path witnesses
-- provenance-compatible selections on both sides without a separate path envelope.
def includes (schema : Schema) (left right : Operation) : Prop :=
  QueryInclusion.sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
    right.variableDefinitions
  ∧ ∀ (assignment : BoolCase),
      boolVarsComplete
        (QueryInclusion.comparisonConditionVariables left.selectionSet right.selectionSet)
        (boolCaseVariableValues assignment)
      -> ∀ path,
          operationSelectsPath schema right assignment path
          -> operationSelectsPath schema left assignment path

-----------------------------------------------------------------------------------------
-- Agreement with semantic query inclusion
-----------------------------------------------------------------------------------------

-- Correspondence, first direction: semantic query inclusion reduces to the path-based
-- syntactic relation. For valid operations under a well-formed schema, syntactic
-- inclusion implies semantic inclusion. Its theorem witness is
-- `ResponsePath.includesSemanticToSyntactic` in the corresponding proof module.
def IncludesSemanticToSyntactic (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> includes schema left right
  -> QueryInclusion.includes schema left right

-- Correspondence, second direction: the path-based syntactic relation reduces to
-- semantic query inclusion. The premises mirror `QueryInclusion.IncludesBoolComplete`:
-- argument-coercible branch extensions and composite-return inhabitance rule out vacuous
-- semantic inclusion by supplying an error-free execution witness for every selected
-- path. Its theorem witness is `ResponsePath.includesSyntacticToSemantic` in the
-- corresponding proof module.
def IncludesSyntacticToSemantic (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> QueryInclusion.operationCompositeFieldTypesInhabited schema left
  -> QueryInclusion.operationCompositeFieldTypesInhabited schema right
  -> QueryInclusion.comparisonBranchesArgumentCoercible schema left right
  -> QueryInclusion.includes schema left right
  -> includes schema left right

end ResponsePath
end GraphQL
