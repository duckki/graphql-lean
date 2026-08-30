import Proofs.GraphQL.Theories.TreeSummary.AnnotationErasure

namespace GraphQL
namespace Tests
namespace TreeSummary
namespace Soundness

open GraphQL.TreeSummary
open GraphQL.AnnotatedExecution

def unitConcreteAlgebra : ConcreteAlgebra :=
  {
    Summary := Unit
    empty := ()
    field := fun _definition _value _child => ()
    combine := fun _left _right => ()
  }

theorem foldAnnotatedResponseApiSmoke (response : AnnotatedResponse)
    : foldAnnotatedResponse unitConcreteAlgebra response = () := by
  rfl

theorem executeQueryAnnotatedToResponseApiSmoke
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (source : Execution.ResolverValue ObjectRef)
    : (executeQueryAnnotated schema resolvers variableValues operation source).toResponse
      = Execution.executeQuery schema resolvers variableValues operation source :=
  executeQueryAnnotated_equal schema operation ObjectRef resolvers variableValues source

theorem exactAnalysisSoundApiSmoke
    {concrete : ConcreteAlgebra} {abstract : Algebra} {schema : Schema}
    (soundnessFor
      : ∀ values, ExactCases.SoundnessWithFactoring concrete abstract schema values)
    (operation : Operation)
    : ExactCases.AnalysisSound soundnessFor operation :=
  ExactCases.analysisSound soundnessFor operation

theorem syntacticAnalysisSoundApiSmoke
    {concrete : ConcreteAlgebra} {abstract : Algebra} {schema : Schema}
    (soundnessFor : ∀ values, Syntactic.Soundness concrete abstract schema values)
    (operation : Operation)
    : Syntactic.AnalysisSound soundnessFor operation :=
  Syntactic.analysisSound soundnessFor operation

end Soundness
end TreeSummary
end Tests
end GraphQL
