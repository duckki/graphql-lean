import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.EligibleFailureBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureErrors

/-! Source-settlement projections remain separate from cached reporting availability. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The bookkeeping failure list reverses exactly the object-failure source labels.
Witness: each source constructor selects the same occurrence in the two list encodings.
-/
theorem GraphEvent.failureSettlements_eq_objectFailures_reverse (events : List GraphEvent)
    : GraphEvent.failureSettlements events
      = (events.filterMap GraphEvent.objectFailure?).reverse := by
  unfold GraphEvent.failureSettlements
  congr 1
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [GraphEvent.groupFailures, List.filterMap_cons,
        GraphEvent.objectFailure?, ih]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
