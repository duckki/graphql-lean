import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Statements

/-!
Proof-only selection-set semantic equivalence restricted to runtime environments
that bind every Boolean variable used to select a complete-normal branch.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

def selectionSetsSemanticallyEquivalentForCompleteBoolVars
    (schema : Schema) (variables : List BoolVar)
    (parentType : Name) (left right : List Selection)
    : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
      variableValues fuel (source : Execution.ResolverValue ObjectRef),
    boolVarsComplete variables variableValues
    -> (∃ runtimeType ref,
          source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
    -> Execution.Response.semanticEquivalent
        (Execution.executeSelectionSetAsResponse schema resolvers
          variableValues fuel parentType source left)
        (Execution.executeSelectionSetAsResponse schema resolvers
          variableValues fuel parentType source right)

end CompleteNormalization

end NormalForm

end GraphQL
