import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Bounded all-owner pending accounting along admitted source replays. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A valid nonempty source prefix exposes its last event's provenance and freshness.
Witness: injectivity of list concatenation in the source derivation.
-/
theorem validGraphEvents_last {work : Execution.Work} {before : List GraphEvent}
    {event : GraphEvent} (valid : ValidGraphEvents work (before ++ [event]))
    : ValidGraphEvents work before ∧ event.MatchesWork work ∧ event.Fresh before := by
  generalize same : before ++ [event] = events at valid
  cases valid with
  | nil => simp at same
  | @append earlier last prior matching fresh ready =>
      obtain ⟨sameBefore, sameLast⟩ := List.append_inj' same (by simp)
      have equal : event = last := by simpa using sameLast
      subst earlier
      subst last
      exact ⟨prior, matching, fresh⟩

/-- Every accepted valid source-event suffix preserves the all-owner ledger.
Witness: sequential handler preservation, retaining only already processed task outcomes.
-/
theorem State.PendingAccounting.replayGraphEvents
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    (prior : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).PendingAccounting work
        (GraphEvent.taskSettlements (before ++ events)) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := by
        exact ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have next := prior.handleGraphEvent generated
        (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh accepts.1
      rw [← GraphEvent.taskSettlements_append] at next
      have retained := ih next
        (by simpa [List.append_assoc] using valid) accepts.2
      simpa [State.replayGraphEvents, List.append_assoc] using retained

/-- Batch termination only changes the control flag, leaving the ledger unchanged. -/
theorem State.PendingAccounting.withTerminated
    {queue : State} {work : Execution.Work} {settled : List Occurrence}
    (prior : queue.PendingAccounting work settled) (terminated : Bool)
    : ({queue with terminated := terminated}).PendingAccounting work settled :=
  ⟨
    prior.pending,
    prior.links,
    prior.keys,
    prior.memberships,
    prior.liveGroups,
    prior.taskGroups,
    prior.sound,
    prior.matching,
    prior.started
  ⟩

/-- An accepted batch preserves safe counters even when it terminates the queue.
Witness: event replay followed by the control-only termination update.
-/
theorem State.PendingAccounting.handleGraphEvents
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    (prior : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.PendingAccounting work
        (GraphEvent.taskSettlements (before ++ events)) := by
  have accounted := prior.replayGraphEvents generated events valid accepted
  unfold State.handleGraphEvents
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split
  · simpa only [State.foldGraphEvents_state] using accounted.withTerminated true
  · simpa only [State.foldGraphEvents_state] using accounted

/-- Valid started source batches preserve all-owner accounting at every replay boundary.
Witness: batch induction, keeping the source prefix and processed task identities aligned.
-/
theorem State.PendingAccounting.runNormalized
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    (prior : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.PendingAccounting work
        (GraphEvent.taskSettlements (before ++ batches.flatten)) := by
  rw [State.runNormalized_stateFold]
  induction batches generalizing queue before with
  | nil => simpa using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ :=
        queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next :=
        prior.handleGraphEvents generated batch (valid.prefix earlier)
          running accepted
      have retained := ih next
        (by simpa [List.append_assoc] using valid) restStarted
      simpa [List.append_assoc] using retained

/-- Generated replay bounds counters against all successful and failed source settlements.
Ignored settlements remain in this membership ledger but need not be failure witnesses.
Witness: the all-owner batch induction instantiated with the empty source prefix.
-/
theorem ExecutedWork.runNormalized_pendingLedger {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.PendingAccounting
        work (GraphEvent.taskSettlements batches.flatten) := by
  exact (createWorkQueue_pendingAccounting work).runNormalized (before := [])
    generated batches valid (by rwa [inputsStarted_eq_batchesStarted] at started)

/-- Every generated valid started replay has safe pending bounds for all live groups,
including latent failed owners. The ledger contains only processed source task outcomes.
Witness: initialization and the all-owner batch induction; no output admission is assumed.
-/
theorem ExecutedWork.runNormalized_pendingAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ settled,
        settled.Subset (batches.flatten.flatMap (fun event => event.identities.1))
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.PendingAccounting
            work settled := by
  exact ⟨GraphEvent.taskSettlements batches.flatten,
    GraphEvent.taskSettlements_subsetIdentities batches.flatten,
    generated.runNormalized_pendingLedger batches valid started⟩

/-- Actual source replay supplies the drain's bound for every live group, without a
healthy-owner restriction. Witness: bounded counters and inclusion in source settlements.
-/
theorem ExecutedWork.runNormalized_pendingBound {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.PendingBound
        (fun _ => True) (batches.flatten.flatMap (fun event => event.identities.1)) := by
  obtain ⟨settled, included, accounted⟩ :=
    generated.runNormalized_pendingAccounting batches valid started
  exact accounted.pending.weakenSettled included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
