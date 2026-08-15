import Proofs.GraphQL.Theories.AnnotatedExecution
import Tests.GraphQL.Execution

namespace GraphQL
namespace Tests
namespace AnnotatedExecution

open GraphQL.AnnotatedExecution

theorem executeQueryAnnotatedToResponseApiSmoke
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (source : Execution.ResolverValue ObjectRef)
    : (executeQueryAnnotated schema resolvers variableValues operation source).toResponse
      = Execution.executeQuery schema resolvers variableValues operation source :=
  executeQueryAnnotated_equal schema operation ObjectRef resolvers variableValues source

theorem annotatedExecutorRecordsCoercedResolverArguments
    : (let response :=
          executeQueryAnnotated GraphQL.Tests.Execution.coercedResolverSchema
            GraphQL.Tests.Execution.resolverArgumentPresenceResolvers []
            GraphQL.Tests.Execution.omittedResolverArgumentOperation
            (.object "Query" ())
        let callCheck :=
          match response.data with
          | .object "Query" [.resolved "echo" call (.scalar "present")] =>
              call.originalArguments.isEmpty
              && match call.coercedArguments with
                  | .success arguments =>
                      Algorithms.argumentListEqBool
                        (arguments.map Execution.CoercedArgument.toArgument)
                        [{
                          name := "payload"
                          value := GraphQL.Tests.Execution.defaultedResolverPayload
                        }]
                  | .error => false
          | _ => false
        response.errors == 0 && callCheck)
      = true := by
  native_decide

end AnnotatedExecution
end Tests
end GraphQL
