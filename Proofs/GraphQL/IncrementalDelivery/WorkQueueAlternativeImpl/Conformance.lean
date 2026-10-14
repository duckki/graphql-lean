import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance

/-! Transfer the independent WorkQueue contract through exact observable-factory equality. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- All four contract clauses follow from the existing reference witness, under its exact
executed-work, nonemptiness, and source premises. No host-effect property is assumed.
-/
theorem createWorkQueueForScheduleConforms_holds
    : createWorkQueueForScheduleConforms := by
  exact createWorkQueueForScheduleConforms_of_factory
    createWorkQueueForScheduleMatchesReference_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
