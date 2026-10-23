import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! Retain full contributor-bearing object values across the actual host batch boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- A proof projection of actual raw batches, before publisher erasure
-----------------------------------------------------------------------------------------

/-- The raw object-value sequence produced by successive actual queue batches.
Unlike wire payloads, these values still include their full contributor descriptors.
This projection changes neither the executable queue nor its received source inputs.
-/
def State.batchedObjectValues (queue : State)
    : List (List GraphEvent) → List ExecutionGroupValue
  | [] => []
  | batch :: rest =>
      let next := queue.handleGraphEvents batch
      next.2.flatMap WorkQueueEvent.objectValues ++ next.1.batchedObjectValues rest

/-- Raw actual batches retain the exact full contributor-bearing object sequence.
Witness: both projections follow the same handler output and next queue for each batch.
No flattening or eventwise state equivalence is required.
-/
theorem State.batchedObjectValues_rawBatches (queue : State)
    (batches : List (List GraphEvent))
    : queue.batchedObjectValues batches
      = (queue.rawBatches batches).2.flatMap WorkQueueEvent.objectValues := by
  induction batches generalizing queue with
  | nil => rfl
  | cons batch rest ih =>
      simp only [State.batchedObjectValues, State.rawBatches, List.flatMap_append, ih]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
