import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIdentity
import Tests.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.QueryObservation

/-! Universal identity witnesses and occurrence-sensitive observation regressions. -/

namespace GraphQL.IncrementalDelivery.Tests.Identity
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- Public witnesses require neither successful execution nor stream-free syntax. -/
example (schema : Schema) (operation : Operation)
    : deliveryIDsUnique schema operation
      ∧ deliveryIDsCompleteExactlyOnce schema operation :=
  ⟨
    deliveryIDsUnique_holds schema operation,
    deliveryIDsCompleteExactlyOnce_holds schema operation
  ⟩

/-- Prefix identity also holds for arbitrary raw work with an independent history. -/
example {response work complete result}
    (observed : WorkObservation response work complete result)
    : result.idsUnique ∧ UniqueCompletions result :=
  observed.uniqueIDs

/-- The actual conforming fixture's observed response has unique IDs and completions. -/
example (response : Response)
    : (replayResponse response SourceObservation.queue.initialGroups
        SourceObservation.queue.initialStreams [[SourceObservation.events]]).idsUnique :=
  (executionFromWork_observes_workHistory QueryObservation.scheduler response
    WorkScheduler.work QueryObservation.conforms
    (QueryObservation.observed response)).uniqueIDs.1

/-- No query prefix may contain the malformed duplicate announcement fixture. -/
example {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ¬queryObservation schema resolvers variables operation fuel source
        Tests.Correctness.duplicateAnnouncement := by
  intro observed
  have unique := deliveryIDsUnique_holds schema operation resolvers variables fuel source
    _ observed
  simp [Tests.Correctness.duplicateAnnouncement, ExecutionObservation.idsUnique,
    DeliveryTrace.pendingIDs, List.nodup_cons] at unique

/-- No complete query outcome may contain duplicate completion notices. -/
example {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ¬queryOutcome schema resolvers variables operation fuel source
        Tests.Correctness.duplicateCompletion := by
  intro observed
  have once := deliveryIDsCompleteExactlyOnce_holds schema operation resolvers variables
    fuel source Tests.Correctness.duplicateCompletion observed
  simp [Tests.Correctness.duplicateCompletion, ExecutionObservation.idsCompleteExactlyOnce,
    DeliveryTrace.pendingIDs, DeliveryTrace.completedIDs] at once

/-- Coalescing may reorder notices inside a batch, but preserves multiplicity. -/
example {events batches}
    (grouped : GraphQL.IncrementalDelivery.WorkScheduler.WorkBatching events batches)
    : (GraphQL.IncrementalDelivery.WorkScheduler.pendingKeys batches.flatten).Perm
        (GraphQL.IncrementalDelivery.WorkScheduler.pendingKeys events) :=
  grouped.keyPermutation.pending

end GraphQL.IncrementalDelivery.Tests.Identity
