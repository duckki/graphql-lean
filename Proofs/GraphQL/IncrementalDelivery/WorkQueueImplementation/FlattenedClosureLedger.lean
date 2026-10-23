import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedCarrierReplay

/-! Batch certificates retain their labels and actual rejection snapshots. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Taking the ledger at the full raw object count preserves every handler slice
-----------------------------------------------------------------------------------------

/-- A replay certificate inspects only labels within its actual raw object-value count.
Witness: take/drop identities align each handler's slice and the remaining suffix.
No exact length or payload equality premise is needed, even for a short supplied ledger.
-/
theorem State.replayClosuresCovered_take_iff (queue : State)
    (events : List GraphEvent) (published : List ObjectPublication)
    (available : List (Occurrence × Nat) := [])
    : queue.ReplayClosuresCovered events
        (published.take
          ((queue.rawEventReplay events available).2.flatMap
            WorkQueueEvent.objectValues).length) available
      ↔ queue.ReplayClosuresCovered events published available := by
  induction events generalizing queue published with
  | nil => rfl
  | cons event rest ih =>
      simp only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        State.ReplayClosuresCovered, List.take_take, Nat.min_eq_left (Nat.le_add_right _ _),
        List.drop_take, Nat.add_sub_cancel_left]
      rw [ih]

/-- Replay certificates concatenate at the exact earlier raw object count.
Witness: peel the first inputs, preserve their local certificates, and add their
value counts when dropping labels for the continuation. No new labels are selected.
-/
theorem State.ReplayClosuresCovered.append {queue : State}
    {available : List (Occurrence × Nat)} {published} (before after : List GraphEvent)
    (first : queue.ReplayClosuresCovered before published available)
    (last
      : (queue.replayGraphEvents before available).ReplayClosuresCovered after
          (published.drop
            ((queue.rawEventReplay before available).2.flatMap
              WorkQueueEvent.objectValues).length) available)
    : queue.ReplayClosuresCovered (before ++ after) published available := by
  induction before generalizing queue published with
  | nil => exact last
  | cons event rest ih =>
      refine ⟨first.1, first.2.1, first.2.2.1, first.2.2.2.1,
        first.2.2.2.2.1, first.2.2.2.2.2.1, first.2.2.2.2.2.2.1,
        first.2.2.2.2.2.2.2.1, first.2.2.2.2.2.2.2.2.1, ?_⟩
      apply ih first.tail
      simpa only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.drop_drop, State.replayGraphEvents, List.foldl_cons] using last

-----------------------------------------------------------------------------------------
-- Batch output uses its own snapshot and adds only object-free control notices
-----------------------------------------------------------------------------------------

/-- An open batch has the same object values as replay with that batch's cache snapshot.
Witness: forwarded startup failures and the optional termination marker contain no object
values. Different batches retain different snapshots, so this is not a flattening law.
-/
theorem State.handleGraphEvents_objectValues (queue : State) (events : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.objectValues
      = (queue.rawEventReplay events (GraphEvent.availableFailures events)).2.flatMap
          WorkQueueEvent.objectValues := by
  rw [State.handleGraphEvents_eq_rawEventReplay queue events]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split <;> simp only [List.flatMap_append, List.flatMap_singleton,
    WorkQueueEvent.objectValues, List.append_nil]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
