import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedClosureLedger

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

/-- Started batches preserve the exact full raw-value sequence of sequential replay.
Witness: a later started batch excludes intermediate termination; the optional final
marker contains no object value. Full contributor lists survive, not just serialized data.
-/
theorem State.batchedObjectValues_flattened (queue : State)
    (batches : List (List GraphEvent)) (started : queue.batchesStarted batches = true)
    : queue.batchedObjectValues batches
      = (queue.rawEventReplay batches.flatten).2.flatMap WorkQueueEvent.objectValues := by
  induction batches generalizing queue with
  | nil => rfl
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      rw [State.batchedObjectValues, queue.handleGraphEvents_objectValues batch running]
      cases rest with
      | nil => simp [State.batchedObjectValues]
      | cons next tail =>
          have remains := ((queue.handleGraphEvents batch).1.batchesStarted_cons next tail later).1
          rw [ih _ later, queue.handleGraphEvents_nonterminalState batch running remains]
          simp only [List.flatten_cons, State.rawEventReplay_append, List.flatMap_append,
            State.rawEventReplay_state]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
