import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedClosureLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! Closure-ledger convenience projections preserve host cache boundaries explicitly. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

/-- A single host batch retains its complete supplied snapshot and full publication ledger. -/
theorem State.BatchClosuresCovered.singleton {queue events published}
    (covered : State.BatchClosuresCovered queue [events] published)
    (running : queue.terminated = false)
    : queue.ReplayClosuresCovered events published
        (GraphEvent.availableFailures events) := by
  apply (queue.replayClosuresCovered_take_iff events published
    (GraphEvent.availableFailures events)).mp
  rw [← queue.handleGraphEvents_objectValues events running]
  exact covered.1

/-- The empty-snapshot specialization still requires that batch's cache to be empty. -/
theorem State.BatchClosuresCovered.singleton_emptyCache {queue events published}
    (covered : State.BatchClosuresCovered queue [events] published)
    (running : queue.terminated = false)
    (empty : GraphEvent.availableFailures events = [])
    : queue.ReplayClosuresCovered events published := by
  simpa only [empty] using covered.singleton running

/-- Flattening is valid for closure certificates only when every host snapshot is empty.
Started batches supply running boundaries; nonempty rejection snapshots cannot use this bridge.
-/
theorem State.BatchClosuresCovered.flatten_emptyCache {queue batches published}
    (covered : State.BatchClosuresCovered queue batches published)
    (started : queue.batchesStarted batches = true)
    (empty : ∀ batch ∈ batches, GraphEvent.availableFailures batch = [])
    : queue.ReplayClosuresCovered batches.flatten published := by
  induction batches generalizing queue published with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have noCache := empty batch List.mem_cons_self
      have first : queue.ReplayClosuresCovered batch published := by
        apply (queue.replayClosuresCovered_take_iff batch published).mp
        rw [← noCache, ← queue.handleGraphEvents_objectValues batch running]
        exact covered.1
      cases rest with
      | nil =>
          simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using first
      | cons next later =>
          have rawRunning : (queue.replayGraphEvents batch).terminated = false := by
            rw [← State.rawEventReplay_state, State.rawEventReplay_terminated]
            exact running
          have nextRunning := ((queue.handleGraphEvents batch).1.batchesStarted_cons next later
            restStarted).1
          obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
          have flag := congrArg State.terminated same
          change (queue.handleGraphEvents batch).1.terminated = terminal at flag
          have flagFalse := flag.symm.trans nextRunning
          have stateEq : (queue.handleGraphEvents batch).1 = queue.replayGraphEvents batch := by
            rw [same, flagFalse]
            simp only [noCache]
            rw [← rawRunning]
          have last := ih covered.2.2 restStarted
            (fun more member => empty more (List.mem_cons_of_mem _ member))
          rw [stateEq] at last
          apply first.append batch (next :: later).flatten
          rw [← noCache, ← queue.handleGraphEvents_objectValues batch running, noCache]
          exact last

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
