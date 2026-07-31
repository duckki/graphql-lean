import Proofs.GraphQL.Theories.ResponseShape.Compute.Totality
import Tests.GraphQL.Theories.ResponseShape.Compute

namespace GraphQL
namespace Tests
namespace ResponseShape

open GraphQL.ResponseShape

/-- Executable check of the computation theorem's returned-shape conclusion. -/
def computationTotalityConclusionBool
    (schema : Schema) (operation : Operation) : Bool :=
  match computeOperationShape schema operation with
  | .error _ => false
  | .ok shape =>
      decide (shape.WellFormed schema)
      && decide shape.FullMinterm
      && shape.boolSupport == NormalForm.operationBoolVars operation

/-- The executable conclusion is equivalent to an explicit returned witness. -/
theorem computationTotalityConclusionBool_eq_true_iff
    (schema : Schema) (operation : Operation) :
    computationTotalityConclusionBool schema operation = true ↔
      ∃ shape,
        computeOperationShape schema operation = .ok shape
        ∧ shape.WellFormed schema
        ∧ shape.FullMinterm
        ∧ shape.boolSupport = NormalForm.operationBoolVars operation := by
  unfold computationTotalityConclusionBool
  cases hcompute : computeOperationShape schema operation <;> simp [and_assoc]

/-- The universal theorem's conclusion is non-vacuous on the Boolean fixture. -/
theorem twoVariableComputationTotalitySmoke :
    ∃ shape,
      computeOperationShape NormalForm.groundTypingSchema
          NormalForm.completeNormalizationDirectiveInputQuery = .ok shape
      ∧ shape.WellFormed NormalForm.groundTypingSchema
      ∧ shape.FullMinterm
      ∧ shape.boolSupport =
          NormalForm.operationBoolVars
            NormalForm.completeNormalizationDirectiveInputQuery := by
  apply (computationTotalityConclusionBool_eq_true_iff
    NormalForm.groundTypingSchema
    NormalForm.completeNormalizationDirectiveInputQuery).mp
  native_decide

/-- The same conclusion has a witness for a distinct schema and operation. -/
theorem aliasedArgumentComputationTotalitySmoke :
    ∃ shape,
      computeOperationShape argumentSchema aliasedArgumentOperation = .ok shape
      ∧ shape.WellFormed argumentSchema
      ∧ shape.FullMinterm
      ∧ shape.boolSupport =
          NormalForm.operationBoolVars aliasedArgumentOperation := by
  apply (computationTotalityConclusionBool_eq_true_iff
    argumentSchema aliasedArgumentOperation).mp
  native_decide

end ResponseShape
end Tests
end GraphQL
