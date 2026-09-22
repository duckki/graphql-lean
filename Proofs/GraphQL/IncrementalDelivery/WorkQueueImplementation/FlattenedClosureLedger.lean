import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedCarrierReplay

/-! Batch certificates retain their occurrence labels when source inputs are flattened. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Taking the ledger at the full raw object count preserves every handler slice
-----------------------------------------------------------------------------------------

/-- A replay certificate inspects only labels within its actual raw object-value count.
Witness: take/drop identities align each handler's slice and the remaining suffix.
No exact length or payload equality premise is needed, even for a short supplied ledger.
-/
theorem State.replayClosuresCovered_take_iff (queue : State)
    (events : List GraphEvent) (published : List ObjectPublication)
    : queue.ReplayClosuresCovered events
        (published.take
          ((queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues).length)
      ↔ queue.ReplayClosuresCovered events published := by
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
theorem State.ReplayClosuresCovered.append {queue : State} {published}
    (before after : List GraphEvent)
    (first : queue.ReplayClosuresCovered before published)
    (last
      : (queue.replayGraphEvents before).ReplayClosuresCovered after
          (published.drop
            ((queue.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length))
    : queue.ReplayClosuresCovered (before ++ after) published := by
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
-- Started batches add no intervening state change before another accepted input
-----------------------------------------------------------------------------------------

/-- An open batch wrapper preserves the raw object-value sequence exactly.
Witness: its only optional output is a terminal control marker, whose object list is empty.
-/
theorem State.handleGraphEvents_objectValues (queue : State) (events : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.handleGraphEvents events).2.flatMap WorkQueueEvent.objectValues
      = (queue.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split
  · simp [WorkQueueEvent.objectValues]
  · rfl

/-- Every started batch certificate is a certificate for the flattened source replay.
Witness: batch wrappers preserve object counts, and a following accepted batch proves
the previous wrapper did not terminate or alter the sequential queue state. Concatenation
retains the same ledger, including unused labels after an interrupted prefix.
-/
theorem State.BatchClosuresCovered.flatten {queue : State} {batches published}
    (covered : queue.BatchClosuresCovered batches published)
    (started : queue.batchesStarted batches = true)
    : queue.ReplayClosuresCovered batches.flatten published := by
  induction batches generalizing queue published with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have counts := congrArg List.length (queue.handleGraphEvents_objectValues batch running)
      have first := covered.1
      rw [counts] at first
      have initial := (queue.replayClosuresCovered_take_iff batch published).mp first
      cases rest with
      | nil =>
          simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using initial
      | cons next tail =>
          have openNext := ((queue.handleGraphEvents batch).1.batchesStarted_cons
            next tail later).1
          have remaining := ih covered.2.2 later
          rw [counts, queue.handleGraphEvents_nonterminalState batch running openNext]
            at remaining
          exact initial.append batch ((next :: tail).flatten) remaining

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
