import GraphQL.Execution
import GraphQL.Theories.ResponseShape.Syntax

/-!
The execution-facing selected-field footprint of an operation.

This specification is grounded directly in `Execution.collectFields` and
`Execution.collectSubfields`. It does not depend on response-shape computation
or denotation.
-/

namespace GraphQL

namespace ResponseShape

/--
A collected executable field has the identity and concrete-object schema entry
recorded by one response-shape path step.
-/
def executableFieldMatchesPathStep
    (schema : Schema) (field : Execution.ExecutableField)
    (step : PathStep) : Prop :=
  field.responseName = step.responseName
  ∧ field.fieldName = step.field.fieldName
  ∧ Argument.argumentsEquivalent field.arguments step.field.arguments
  ∧ ∃ fieldDefinition,
      schema.lookupField step.parentObject step.field.fieldName =
          some fieldDefinition
      ∧ fieldDefinition.outputType = step.field.outputType

/--
A nonempty concrete-object-indexed path occurs in already-collected field
groups. Any member of the response-name group may witness the current step;
child collection nevertheless merges the selection sets of the entire group.
Before collecting those children, the next concrete object must be reachable
from the current field's output scope.
-/
def collectedFieldsSelectPath
    (schema : Schema) (variableValues : Execution.VariableValues)
    : List (Name × List Execution.ExecutableField) -> List PathStep -> Prop
  | _groupedFields, [] => False
  | groupedFields, [step] =>
      ∃ fields,
        (step.responseName, fields) ∈ groupedFields
        ∧ ∃ field,
          field ∈ fields
          ∧ executableFieldMatchesPathStep schema field step
  | groupedFields, step :: next :: rest =>
      ∃ fields,
        (step.responseName, fields) ∈ groupedFields
        ∧ (∃ field,
          field ∈ fields
          ∧ executableFieldMatchesPathStep schema field step)
        ∧ schema.typeIncludesObject
          step.field.outputType.namedType next.parentObject
        ∧ collectedFieldsSelectPath
          schema variableValues
          (Execution.collectSubfields
            schema variableValues next.parentObject
            (.object next.parentObject ()) fields)
          (next :: rest)

/--
The selected-field footprint of an operation under a complete Boolean
assignment. Empty paths are not selected. A synthetic object value supplies
the concrete root object used by fragment applicability during field
collection.

For permissive operation syntax this proposition describes field selection,
not successful field execution. Relating it to executable response positions
therefore requires operation validity.
-/
def operationSelectsPath
    (schema : Schema) (operation : Operation)
    (assignment : NormalForm.BoolCase) : List PathStep -> Prop
  | [] => False
  | step :: rest =>
      let variableValues := NormalForm.boolCaseVariableValues assignment
      schema.typeIncludesObject
          (operation.rootType schema) step.parentObject
      ∧ collectedFieldsSelectPath schema variableValues
          (Execution.collectFields
            schema variableValues (operation.rootType schema)
            (.object step.parentObject ()) operation.selectionSet)
          (step :: rest)

end ResponseShape

end GraphQL
