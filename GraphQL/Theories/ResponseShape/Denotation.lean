import GraphQL.Theories.ResponseShape.Clause

/-! Relational path denotation for response shapes. -/

namespace GraphQL

namespace ResponseShape

/--
A nonempty path selected by a shape for one Boolean assignment. Each step
chooses a concrete runtime object and an active stored field definition.
-/
inductive ResponseShape.DenotesPath
    (schema : Schema) (assignment : NormalForm.BoolCase)
    : Name -> ResponseShape -> List PathStep -> Prop where
  /-- Every selected field contributes its singleton path. -/
  | field
      {positions : List ResponsePosition}
      {position : ResponsePosition}
      {possible : PossibleDefinitions}
      {definition : ShapeDefinition}
      {runtimeObject : GroundObject}
      (runtimePossible : schema.typeIncludesObject parentType runtimeObject)
      (positionMem : position ∈ positions)
      (possibleMem : possible ∈ position.possibleDefinitions)
      (runtimeMem : runtimeObject ∈ possible.objectTypes)
      (definitionMem : definition ∈ possible.definitions)
      (clauseHolds : definition.clause.HoldsIn assignment) :
      DenotesPath schema assignment parentType (.object positions)
        [{ parentObject := runtimeObject
           responseName := position.responseName
           field := definition.field }]
  /-- A selected composite field prefixes every path selected by its child. -/
  | child
      {positions : List ResponsePosition}
      {position : ResponsePosition}
      {possible : PossibleDefinitions}
      {definition : ShapeDefinition}
      {runtimeObject : GroundObject}
      {childShape : ResponseShape}
      {childPath : List PathStep}
      (runtimePossible : schema.typeIncludesObject parentType runtimeObject)
      (positionMem : position ∈ positions)
      (possibleMem : possible ∈ position.possibleDefinitions)
      (runtimeMem : runtimeObject ∈ possible.objectTypes)
      (definitionMem : definition ∈ possible.definitions)
      (clauseHolds : definition.clause.HoldsIn assignment)
      (subshapeEq : definition.subshape = some childShape)
      (childDenotes :
        DenotesPath schema assignment definition.field.outputType.namedType
          childShape childPath) :
      DenotesPath schema assignment parentType (.object positions)
        ({ parentObject := runtimeObject
           responseName := position.responseName
           field := definition.field } :: childPath)

/-- The assignment and nonempty path represented by a raw shape obligation. -/
def ResponseShape.Denotes
    (schema : Schema) (parentType : Name) (shape : ResponseShape)
    (obligation : ShapeObligation) : Prop :=
  shape.DenotesPath schema obligation.assignment parentType obligation.path

/--
An operation shape denotes an obligation only at a complete assignment of its
declared Boolean support.
-/
def OperationShape.Denotes
    (schema : Schema) (shape : OperationShape)
    (obligation : ShapeObligation) : Prop :=
  NormalForm.completeNormalBoolCase shape.boolSupport obligation.assignment
  ∧ shape.root.Denotes schema shape.rootType obligation

end ResponseShape

end GraphQL
