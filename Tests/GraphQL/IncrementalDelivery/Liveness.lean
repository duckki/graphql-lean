import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIdentity
import Tests.GraphQL.IncrementalDelivery.QueryObservation

/-! Finite-run liveness is independent of syntax, execution success, and batching. -/

namespace GraphQL.IncrementalDelivery.Tests.Liveness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The public liveness witness applies to every operation. -/
example (schema : Schema) (operation : Operation)
    : deliveryIDsEventuallyComplete schema operation :=
  deliveryIDsEventuallyComplete_holds schema operation

/-- Any conforming complete query observation inherits causal ID completion. -/
example {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : ExecutionObservation}
    (observed : queryOutcome schema resolvers variables operation fuel source result)
    : result.idsEventuallyComplete :=
  deliveryIDsEventuallyComplete_holds schema operation resolvers variables fuel source
    result observed

/-- The actual fixture source's complete response observation inherits work liveness. -/
example (response : Response)
    : ExecutionObservation.idsEventuallyComplete
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) :=
  WorkObservation.idsEventuallyComplete
    (executionFromWork_observes_workHistory QueryObservation.scheduler response
      WorkScheduler.work QueryObservation.conforms (QueryObservation.observed response))

/-- The witness also covers arbitrary admitted raw work, not only query-produced work. -/
example {response work result} (observed : WorkObservation response work true result)
    : result.idsEventuallyComplete :=
  observed.idsEventuallyComplete

end GraphQL.IncrementalDelivery.Tests.Liveness
