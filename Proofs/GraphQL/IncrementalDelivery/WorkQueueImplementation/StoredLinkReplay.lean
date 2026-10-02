import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredLinkPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay

/-! Generated source replay establishes buffered contributor memberships unconditionally. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Fresh source prefixes supply the internal unsettled-membership ledger
-----------------------------------------------------------------------------------------

/-- Every accepted valid source suffix preserves buffered contributor links.
Witness: joint use of the existing pending ledger and the buffered-link handler theorem;
source freshness keeps newly stored successes distinct from prior settlements.
-/
theorem State.StoredTaskLinks.replayGraphEvents {queue : State} {work before}
    (linked : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).StoredTaskLinks := by
  induction events generalizing queue before with
  | nil => exact linked
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have included := GraphEvent.taskSettlements_subsetIdentities before
      have nextLinks := linked.handleGraphEvent accounted included event matching fresh
      have next := accounted.handleGraphEvent generated included event matching fresh accepts.1
      rw [← GraphEvent.taskSettlements_append] at next
      exact ih nextLinks next
        (by simpa only [List.append_assoc, List.singleton_append] using valid) accepts.2

/-- Batch termination changes no buffered membership fact.
Witness: event replay followed by the control-only terminal-flag update.
-/
theorem State.StoredTaskLinks.handleGraphEvents {queue : State} {work before}
    (linked : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.StoredTaskLinks := by
  have next := linked.replayGraphEvents accounted generated events valid accepted
  unfold State.handleGraphEvents
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split <;> simpa only [State.foldGraphEvents_state, State.StoredTaskLinks,
    State.TaskLinkedOn] using next

/-- Arbitrary valid started batching preserves buffered contributor memberships.
Witness: batch induction with the existing pending ledger at each source-prefix boundary.
Neither output admission nor any chosen publication matching is a premise.
-/
theorem State.StoredTaskLinks.runNormalized {queue : State} {work before}
    (linked : queue.StoredTaskLinks)
    (accounted : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.StoredTaskLinks := by
  rw [State.runNormalized_stateFold]
  induction batches generalizing queue before with
  | nil => exact linked
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp only [List.flatten_cons, List.append_assoc]⟩
      have nextLinks := linked.handleGraphEvents accounted generated batch (valid.prefix earlier)
        running accepted
      have next := accounted.handleGraphEvents generated batch (valid.prefix earlier)
        running accepted
      exact ih nextLinks next
        (by simpa only [List.flatten_cons, List.append_assoc] using valid) restStarted

-----------------------------------------------------------------------------------------
-- Entry points for generated event streams
-----------------------------------------------------------------------------------------

/-- Generated valid started replay supplies buffered links at every event boundary.
Witness: the event-suffix induction initialized with no values and the initial pending ledger.
The queue-state invariant is derived from existing source laws, not added to those laws.
-/
theorem ExecutedWork.replayGraphEvents_storedTaskLinks {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).StoredTaskLinks :=
  (createWorkQueue_storedTaskLinks _).replayGraphEvents (before := [])
    (createWorkQueue_pendingAccounting work) generated events valid accepted

/-- Generated valid started batches supply buffered links at every normalized boundary.
Witness: the batch induction from initialization; interrupted prefixes and retained failure
caches are included. This is an internal membership result, not complete conformance.
-/
theorem ExecutedWork.runNormalized_storedTaskLinks {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.StoredTaskLinks :=
  (createWorkQueue_storedTaskLinks _).runNormalized (before := [])
    (createWorkQueue_pendingAccounting work) generated batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
