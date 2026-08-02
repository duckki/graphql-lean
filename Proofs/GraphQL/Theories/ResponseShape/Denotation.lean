import GraphQL.Theories.ResponseShape.Denotation

/-! Basic facts about response-shape path denotation. -/

namespace GraphQL

namespace ResponseShape

namespace Clause

/-- The executable clause check decides logical clause activation. -/
theorem holdsInBool_iff (assignment : NormalForm.BoolCase) (clause : Clause) :
    clause.holdsInBool assignment = true ↔ clause.HoldsIn assignment := by
  simp [holdsInBool, HoldsIn]

end Clause

/-- A denoted path always contains at least one field step. -/
theorem ResponseShape.DenotesPath.nonempty
    {schema : Schema} {assignment : NormalForm.BoolCase} {parentType : Name}
    {shape : ResponseShape} {path : List PathStep}
    (denotes : DenotesPath schema assignment parentType shape path) :
    path ≠ [] := by
  cases denotes <;> simp

/-- Every denoted path also denotes its singleton first-field prefix. -/
theorem ResponseShape.DenotesPath.singletonPrefix
    {schema : Schema} {assignment : NormalForm.BoolCase} {parentType : Name}
    {shape : ResponseShape} {step : PathStep} {rest : List PathStep}
    (denotes : DenotesPath schema assignment parentType shape (step :: rest)) :
    DenotesPath schema assignment parentType shape [step] := by
  cases denotes with
  | field runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds =>
      exact .field runtimePossible positionMem possibleMem runtimeMem
        definitionMem clauseHolds
  | child runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds _subshapeEq _childDenotes =>
      exact .field runtimePossible positionMem possibleMem runtimeMem
        definitionMem clauseHolds

/-- Builds operation denotation from assignment completeness and root denotation. -/
theorem OperationShape.denotes_intro
    {schema : Schema} {shape : OperationShape}
    {obligation : ShapeObligation}
    (completeAssignment :
      NormalForm.completeNormalBoolCase
        shape.boolSupport obligation.assignment)
    (rootDenotes : shape.root.Denotes schema shape.rootType obligation) :
    shape.Denotes schema obligation :=
  ⟨completeAssignment, rootDenotes⟩

/-- A denoted operation obligation has a complete Boolean assignment. -/
theorem OperationShape.Denotes.completeAssignment
    {schema : Schema} {shape : OperationShape}
    {obligation : ShapeObligation}
    (denotes : shape.Denotes schema obligation) :
    NormalForm.completeNormalBoolCase
      shape.boolSupport obligation.assignment :=
  denotes.1

/-- Operation denotation contains the corresponding raw root denotation. -/
theorem OperationShape.Denotes.rootDenotes
    {schema : Schema} {shape : OperationShape}
    {obligation : ShapeObligation}
    (denotes : shape.Denotes schema obligation) :
    shape.root.Denotes schema shape.rootType obligation :=
  denotes.2

end ResponseShape

end GraphQL
