import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality

/-!
Boolean-support facts derived from complete-normal equality up to reordering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReorderingWithCoercion
    {schema : Schema} {left right : Operation}
    (hequal : completeNormalOperationsEqualUpToReorderingWithCoercion schema left right)
    : operationBoolVarsEquivalent left right :=
  hequal.2.1

end CompleteNormalization

end NormalForm

end GraphQL
