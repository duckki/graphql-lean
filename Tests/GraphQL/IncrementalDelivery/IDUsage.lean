import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryIDUsage
import Tests.GraphQL.IncrementalDelivery.Correctness

/-! Open-ID safety is unconditional over admitted observations, including interrupted
prefixes, errors, and all work/response batching. Malformed wire traces are excluded.
-/

namespace GraphQL.IncrementalDelivery.Tests.IDUsage

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

example (schema : Schema) (operation : Operation)
    : deliveryIDUsageValid schema operation ∧ deliveryPatchesAnnounced schema operation :=
  ⟨
    deliveryIDUsageValid_holds schema operation,
    deliveryPatchesAnnounced_holds schema operation
  ⟩

/-- The source/history bridge supplies open-ID safety for arbitrary admitted raw work. -/
example {response work complete result}
    (observed : WorkObservation response work complete result)
    : result.idUsageValid :=
  observed.idUsageValid

/-- Initial-only prefixes are legal safety observations, not completed delivery. -/
example : Tests.Correctness.incompleteObservation.idUsageValid := by
  simp [Tests.Correctness.incompleteObservation, QueryResult.idUsageValid,
    DeliveryTrace.idUsageValid, List.nodup_cons]

example : Tests.Correctness.sameUpdateNotice.idUsageValid := by
  simp [Tests.Correctness.sameUpdateNotice, QueryResult.idUsageValid,
    DeliveryTrace.idUsageValid, IncrementalResult.id, List.nodup_cons]

example {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ¬queryObservation schema resolvers variables operation fuel source
        Tests.Correctness.closedReference := by
  intro observed
  have safe := deliveryIDUsageValid_holds schema operation resolvers variables fuel source
    Tests.Correctness.closedReference observed
  simp [Tests.Correctness.closedReference, QueryResult.idUsageValid, DeliveryTrace.idUsageValid,
    IncrementalResult.id, List.nodup_cons] at safe

example {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ¬queryObservation schema resolvers variables operation fuel source
        Tests.Correctness.lateAnnouncement := by
  intro observed
  have safe := deliveryPatchesAnnounced_holds schema operation resolvers variables fuel source
    Tests.Correctness.lateAnnouncement observed
  simp [Tests.Correctness.lateAnnouncement, QueryResult.patchesAnnounced,
    DeliveryTrace.patchesAnnounced, IncrementalResult.id] at safe

def unannouncedCompletion : QueryResult :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
    [{ hasNext := false, completed := [{ id := "unknown" }] }]

example {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ¬queryObservation schema resolvers variables operation fuel source
        unannouncedCompletion := by
  intro observed
  have safe := deliveryIDUsageValid_holds schema operation resolvers variables fuel source
    unannouncedCompletion observed
  simp [unannouncedCompletion, QueryResult.idUsageValid, DeliveryTrace.idUsageValid,
    List.nodup_cons] at safe

end GraphQL.IncrementalDelivery.Tests.IDUsage
