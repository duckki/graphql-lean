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
theorem State.PendingAccounting.replayGraphEvents_ofMatching
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {available : List (Occurrence × Nat)}
    (prior : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : (queue.replayGraphEvents events available).PendingAccounting work
        (GraphEvent.taskSettlements (before ++ events)) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := by
        exact ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := prior.dispatchGraphEvent_ofMatching generated
        (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh
        available
      rw [← GraphEvent.taskSettlements_append] at next
      have retained := ih next
        (by simpa [List.append_assoc] using valid)
      simpa [State.replayGraphEvents, List.append_assoc] using retained

/-- Strict eventwise specialization of matching replay accounting. -/
theorem State.PendingAccounting.replayGraphEvents
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {available : List (Occurrence × Nat)}
    (prior : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (_accepted : State.eventsStarted available queue events = true)
    : (queue.replayGraphEvents events available).PendingAccounting work
        (GraphEvent.taskSettlements (before ++ events)) :=
  prior.replayGraphEvents_ofMatching generated events valid

/-- An accepted batch preserves safe counters even when it terminates the queue.
Witness: event replay followed by the control-only termination update.
-/
theorem State.PendingAccounting.handleGraphEvents
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    (prior : queue.PendingAccounting work (GraphEvent.taskSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (_accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.PendingAccounting work
        (GraphEvent.taskSettlements (before ++ events)) := by
  have accounted := prior.replayGraphEvents_ofMatching
    (available := GraphEvent.availableFailures events) generated events valid
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact accounted.withTerminated terminal

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
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
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
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using retained

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
  exact (createWorkQueue_pendingAccounting work generated.declarations).runNormalized
    (before := []) generated batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)

/-- Actual batch and FIFO prefixes retain all-owner accounting at the consumed source cut.
Witness: whole-batch replay establishes the boundary ledger; prefix acceptance uses the
entire current batch's availability snapshot, independently of FIFO consumption.
-/
theorem ExecutedWork.pendingLedger_atBatchPrefix {work : Execution.Work}
    (generated : ExecutedWork work) (earlier : List (List GraphEvent))
    (batch : List GraphEvent) (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : let queue :=
        ((State.initialize (Work.fromExecution work)).replayBatches
          earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch)
      queue.PendingAccounting work
        (GraphEvent.taskSettlements (earlier.flatten ++ fifo)) := by
  let initial := State.initialize (Work.fromExecution work)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have before := (createWorkQueue_pendingAccounting work generated.declarations).runNormalized
    (before := []) generated earlier validEarlier checked.1
  rw [State.runNormalized_replayBatches] at before
  simp only [List.nil_append] at before
  obtain ⟨tail, same⟩ := prefixOfBatch
  have validFifo : ValidGraphEvents work (earlier.flatten ++ fifo) := by
    apply valid.prefix
    refine ⟨tail ++ later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, ← same, List.append_assoc]
  exact before.replayGraphEvents_ofMatching generated fifo validFifo

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

/-- Successful settlements alone supply the pending bound retained across rejection.
Witness: replay the same handlers, retaining failed tasks in the unsettled coordinate.
-/
theorem State.PendingAccounting.replayGraphEvents_successes_ofMatching
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {available : List (Occurrence × Nat)}
    (prior : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    : (queue.replayGraphEvents events available).PendingAccounting work
        (GraphEvent.groupSettlements (before ++ events)) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := by
        exact ⟨rest, by simp⟩
      obtain ⟨_, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := prior.dispatchGraphEvent_successes_ofMatching generated
        (GraphEvent.groupSettlements_subsetIdentities before) event matching fresh
        available
      rw [← GraphEvent.groupSettlements_append] at next
      have retained := ih next
        (by simpa [List.append_assoc] using valid)
      simpa [State.replayGraphEvents, List.append_assoc] using retained

/-- Strict eventwise specialization of matching replay accounting. -/
theorem State.PendingAccounting.replayGraphEvents_successes
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    {available : List (Occurrence × Nat)}
    (prior : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (_accepted : State.eventsStarted available queue events = true)
    : (queue.replayGraphEvents events available).PendingAccounting work
        (GraphEvent.groupSettlements (before ++ events)) :=
  prior.replayGraphEvents_successes_ofMatching generated events valid

/-- A complete host batch preserves the successful-settlement ledger under its snapshot. -/
theorem State.PendingAccounting.handleGraphEvents_successes
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    (prior : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (_accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.PendingAccounting work
        (GraphEvent.groupSettlements (before ++ events)) := by
  have accounted := prior.replayGraphEvents_successes_ofMatching
    (available := GraphEvent.availableFailures events) generated events valid
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact accounted.withTerminated terminal

/-- Successful-settlement accounting follows actual host batches and their cache snapshots. -/
theorem State.PendingAccounting.runNormalized_successes
    {queue : State} {work : Execution.Work} {before : List GraphEvent}
    (prior : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.PendingAccounting work
        (GraphEvent.groupSettlements (before ++ batches.flatten)) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents_successes generated batch (valid.prefix earlier)
        running accepted
      have retained := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using retained

/-- Started normalized replay preserves the successful-settlement counter ledger. -/
theorem ExecutedWork.runNormalized_successLedger {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.PendingAccounting
        work (GraphEvent.groupSettlements batches.flatten) :=
  (createWorkQueue_pendingAccounting work generated.declarations).runNormalized_successes
    (before := []) generated batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
