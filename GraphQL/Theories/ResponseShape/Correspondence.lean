import GraphQL.Theories.ResponseShape.Denotation
import GraphQL.Theories.ResponseShape.Footprint
import GraphQL.Theories.ResponseShape.Validity

/-!
Semantic path matching at the response-shape/field-collection boundary.

Field collection compares argument lists as unordered semantic sets, whereas a
decoded shape retains one concrete representative list. Correspondence is
therefore stated against a pointwise semantic match rather than syntactic path
equality.
-/

namespace GraphQL

namespace ResponseShape

/-- Two path steps identify the same concrete response field. Argument order
and input-object field order are interpreted by `Argument.argumentsEquivalent`.
-/
def PathStep.SemanticallyEquivalent (left right : PathStep) : Prop :=
  left.parentObject = right.parentObject
  ∧ left.responseName = right.responseName
  ∧ left.field.fieldName = right.field.fieldName
  ∧ Argument.argumentsEquivalent left.field.arguments right.field.arguments
  ∧ left.field.outputType = right.field.outputType

/-- Executable semantic equivalence for one response-path step. -/
def PathStep.semanticallyEquivalentBool (left right : PathStep) : Bool :=
  decide (left.parentObject = right.parentObject)
  && (decide (left.responseName = right.responseName)
      && (decide (left.field.fieldName = right.field.fieldName)
          && (argumentsEquivalentBool left.field.arguments right.field.arguments
              && decide (left.field.outputType = right.field.outputType))))

/-- Pointwise semantic equivalence of response paths. -/
def PathsSemanticallyEquivalent : List PathStep -> List PathStep -> Prop
  | [], [] => True
  | left :: leftRest, right :: rightRest =>
      left.SemanticallyEquivalent right
      ∧ PathsSemanticallyEquivalent leftRest rightRest
  | _, _ => False

/-- Executable pointwise semantic equivalence of response paths. -/
def pathsSemanticallyEquivalentBool : List PathStep -> List PathStep -> Bool
  | [], [] => true
  | left :: leftRest, right :: rightRest =>
      left.semanticallyEquivalentBool right
      && pathsSemanticallyEquivalentBool leftRest rightRest
  | _, _ => false

/-- A query path semantically represented by some concrete path retained in a
response shape. -/
def ResponseShape.DenotesEquivalentPath
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (shape : ResponseShape)
    (path : List PathStep) : Prop :=
  ∃ denotedPath,
    shape.DenotesPath schema assignment parentType denotedPath
    ∧ PathsSemanticallyEquivalent denotedPath path

/-- An operation shape represents an obligation up to semantic path identity,
at a complete assignment of its declared Boolean support. -/
def OperationShape.DenotesEquivalent
    (schema : Schema) (shape : OperationShape)
    (obligation : ShapeObligation) : Prop :=
  NormalForm.completeNormalBoolCase shape.boolSupport obligation.assignment
  ∧ shape.root.DenotesEquivalentPath schema obligation.assignment
      shape.rootType obligation.path

end ResponseShape

end GraphQL
