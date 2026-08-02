import GraphQL.Theories.ResponseShape.Validity
import Proofs.GraphQL.Argument
import Proofs.GraphQL.Algorithms.Common.SyntaxEq

/-! Correctness of executable response-shape validity helpers. -/

namespace GraphQL

namespace ResponseShape

/-- The executable input-value check decides semantic input-value equivalence. -/
theorem inputValueEquivalentBool_iff (left right : InputValue) :
    inputValueEquivalentBool left right = true
      ↔ left.equivalent right := by
  constructor
  · intro h
    have hequal : left.canonical = right.canonical :=
      Algorithms.inputValueEqBool_eq h
    rw [InputValue.equivalent, hequal]
    exact InputValue.structuralEquivalent_refl right.canonical
  · intro h
    have hequal : left.canonical = right.canonical :=
      InputValue.eq_of_structuralEquivalent h
    rw [inputValueEquivalentBool, hequal]
    exact Algorithms.inputValueEqBool_self right.canonical

/-- The executable one-argument check decides `Argument.equivalent`. -/
theorem argumentEquivalentBool_iff (left right : Argument) :
    argumentEquivalentBool left right = true
      ↔ left.equivalent right := by
  cases left with
  | mk leftName leftValue =>
      cases right with
      | mk rightName rightValue =>
          simp [argumentEquivalentBool, Argument.equivalent,
            inputValueEquivalentBool_iff]

/-- The executable argument-list check decides semantic argument set equivalence. -/
theorem argumentsEquivalentBool_iff (left right : List Argument) :
    argumentsEquivalentBool left right = true
      ↔ Argument.argumentsEquivalent left right := by
  simp [argumentsEquivalentBool, Argument.argumentsEquivalent,
    argumentEquivalentBool_iff]

end ResponseShape

end GraphQL
