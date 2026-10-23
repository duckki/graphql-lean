import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchReplay

/-! Replay preserves host-batch boundaries. Eventwise reasoning within one batch uses
that entire batch's fixed availability snapshot, including its unconsumed suffix.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Replay one batch prefix under an explicitly supplied computation-availability snapshot. -/
def State.replayGraphEvents (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : State :=
  events.foldl (fun current event => (current.dispatchGraphEvent event available).1) queue

/-- Appending inputs composes event replay while preserving the availability snapshot. -/
theorem State.replayGraphEvents_append (queue : State) (before after : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : queue.replayGraphEvents (before ++ after) available
      = (queue.replayGraphEvents before available).replayGraphEvents after available := by
  simp only [State.replayGraphEvents, List.foldl_append]

/-- The recursive form of the public source start/stop checker. -/
def State.batchesStarted : State → List (List GraphEvent) → Bool
  | _, [] => true
  | queue, batch :: rest =>
      let next := (queue.handleGraphEvents batch).1
      !queue.terminated
      && !batch.isEmpty
      && queue.acceptsBatch batch
      && next.batchesStarted rest

theorem State.fold_started_eq
    (queue : State) (valid : Bool) (batches : List (List GraphEvent))
    : (batches.foldl
        (fun (state, good) batch =>
          let next := (state.handleGraphEvents batch).1
          (next, good && !state.terminated && !batch.isEmpty && state.acceptsBatch batch))
        (queue, valid)).2
      = (valid && queue.batchesStarted batches) := by
  induction batches generalizing queue valid with
  | nil => simp [State.batchesStarted]
  | cons batch rest ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [State.batchesStarted, Bool.and_assoc]

/-- The public source checker is the recursive predicate at concrete initialization. -/
theorem inputsStarted_eq_batchesStarted (work : Execution.Work)
    (batches : List (List GraphEvent))
    : inputsStarted work batches
      = (State.initialize (Work.fromExecution work)).batchesStarted batches := by
  unfold inputsStarted
  rw [State.fold_started_eq]
  rfl

/-- A valid batch exposes acceptance and the actual next batch's starting state. -/
theorem State.batchesStarted_cons (queue : State) (batch : List GraphEvent)
    (rest : List (List GraphEvent))
    (valid : queue.batchesStarted (batch :: rest) = true)
    : queue.terminated = false
      ∧ queue.acceptsBatch batch = true
      ∧ ((queue.handleGraphEvents batch).1).batchesStarted rest = true := by
  simp [State.batchesStarted] at valid
  exact ⟨valid.1.1.1, valid.1.2, valid.2⟩

/-- Batch-start checks concatenate through the actual batch-aware state replay. -/
theorem State.batchesStarted_append (queue : State)
    (before after : List (List GraphEvent))
    : queue.batchesStarted (before ++ after)
      = (queue.batchesStarted before
          && (queue.replayBatches before).batchesStarted after) := by
  induction before generalizing queue with
  | nil => simp [State.batchesStarted, State.replayBatches]
  | cons batch rest ih =>
      simp only [List.cons_append, State.batchesStarted, State.replayBatches, List.foldl_cons]
      rw [ih]
      simp only [State.replayBatches, Bool.and_assoc]

/-- Output accumulation leaves the dispatch fold's state unchanged. -/
theorem State.foldGraphEvents_state (queue : State) (outputs : List WorkQueueEvent)
    (events : List GraphEvent) (available : List (Occurrence × Nat))
    : (events.foldl
        (fun (current, accumulated) event =>
          let (next, produced) := current.dispatchGraphEvent event available
          (next, accumulated ++ produced))
        (queue, outputs)).1
      = queue.replayGraphEvents events available := by
  induction events generalizing queue outputs with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.foldl_cons, State.replayGraphEvents]
      exact ih (queue.dispatchGraphEvent event available).1
        (outputs ++ (queue.dispatchGraphEvent event available).2)

/-- Publisher normalization preserves exact complete-batch state replay. -/
theorem State.runNormalized_stateFold (queue : State) (batches : List (List GraphEvent))
    : (queue.runNormalized batches).1
      = batches.foldl (fun current batch => (current.handleGraphEvents batch).1) queue :=
  queue.runNormalized_replayBatches batches

/-- Strict eventwise start checking is a proof-only language for conditional lemmas.
Unlike public batch admission, it requires membership at every consumption step. It is
not derived from `inputsStarted` or used to restrict the public source domain.
-/
def State.eventsStarted (available : List (Occurrence × Nat))
    : State → List GraphEvent → Bool
  | _, [] => true
  | queue, event :: rest =>
      queue.acceptsGraphEvent event
      && State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest

/-- Strict eventwise checks compose with the same computation snapshot. -/
theorem State.eventsStarted_append (queue : State) (available : List (Occurrence × Nat))
    (before after : List GraphEvent)
    : State.eventsStarted available queue (before ++ after)
      = (State.eventsStarted available queue before
          && State.eventsStarted available (queue.replayGraphEvents before available)
              after) := by
  induction before generalizing queue with
  | nil => simp [State.eventsStarted, State.replayGraphEvents]
  | cons event rest ih =>
      simp only [List.cons_append, State.eventsStarted]
      rw [ih]
      simp only [State.replayGraphEvents, List.foldl_cons, Bool.and_assoc]

/-- A strict eventwise prefix retains its fixed availability snapshot. -/
theorem State.eventsStarted_prefix {queue : State} {before after : List GraphEvent}
    {available : List (Occurrence × Nat)}
    (accepted : State.eventsStarted available queue (before ++ after) = true)
    : State.eventsStarted available queue before = true := by
  rw [State.eventsStarted_append] at accepted
  exact (Bool.and_eq_true_iff.mp accepted).1

/-- Eligibility retained from dispatch boundaries strictly before the replayed history ends. -/
def State.replayEligibility (earlier : GraphEvent → Bool)
    (available : List (Occurrence × Nat))
    : State → List GraphEvent → GraphEvent → Bool
  | _, [] => earlier
  | queue, event :: rest =>
      State.replayEligibility
        (fun candidate => earlier candidate || queue.acceptsGraphEvent candidate)
        available (queue.dispatchGraphEvent event available).1 rest

/-- Within-batch checks compose with accumulated eligibility and fixed cache availability. -/
theorem State.acceptsBatch_go_append (earlier : GraphEvent → Bool) (queue : State)
    (available : List (Occurrence × Nat)) (before after : List GraphEvent)
    : State.acceptsBatch.go earlier available queue (before ++ after)
      = (State.acceptsBatch.go earlier available queue before
          && State.acceptsBatch.go
              (State.replayEligibility earlier available queue before) available
              (queue.replayGraphEvents before available) after) := by
  induction before generalizing queue earlier with
  | nil => simp [State.acceptsBatch.go, State.replayGraphEvents, State.replayEligibility]
  | cons event rest ih =>
      simp only [List.cons_append, State.acceptsBatch.go]
      rw [ih]
      simp only [State.replayGraphEvents, State.replayEligibility, List.foldl_cons,
        Bool.and_assoc]

/-- Admission retains the accumulated eligibility and checks the residual FIFO. -/
theorem State.acceptsBatch_go_cons_eligible (earlier : GraphEvent → Bool) (queue : State)
    (available : List (Occurrence × Nat)) (event : GraphEvent) (rest : List GraphEvent)
    (accepted : State.acceptsBatch.go earlier available queue (event :: rest) = true)
    : (earlier event || queue.acceptsGraphEvent event) = true
      ∧ State.acceptsBatch.go
          (fun candidate => earlier candidate || queue.acceptsGraphEvent candidate)
          available (queue.dispatchGraphEvent event available).1 rest
        = true := by
  have first := (Bool.and_eq_true_iff.mp accepted).1
  have later := (Bool.and_eq_true_iff.mp accepted).2
  refine ⟨?_, later⟩
  cases event with
  | groupFailure failure => simp only [Bool.or_eq_true]; exact Or.inr first
  | taskSuccess | taskFailure | streamItems | streamSuccess | streamFailure => exact first

/-- A within-batch history retains the complete batch's eligibility and cache visibility. -/
theorem State.acceptsBatch_go_prefix {earlier : GraphEvent → Bool} {queue : State}
    {before after : List GraphEvent} {available : List (Occurrence × Nat)}
    (accepted : State.acceptsBatch.go earlier available queue (before ++ after) = true)
    : State.acceptsBatch.go earlier available queue before = true := by
  rw [State.acceptsBatch_go_append] at accepted
  exact (Bool.and_eq_true_iff.mp accepted).1

/-- Accumulated permission has an actual earlier dispatch-boundary witness. -/
theorem State.replayEligibility_witness (earlier : GraphEvent → Bool) (queue : State)
    (available : List (Occurrence × Nat)) (before : List GraphEvent) (event : GraphEvent)
    (eligible : State.replayEligibility earlier available queue before event = true)
    : earlier event = true
      ∨ ∃ history,
          history.IsPrefix before
          ∧ (queue.replayGraphEvents history available).acceptsGraphEvent event
            = true := by
  induction before generalizing earlier queue with
  | nil => exact Or.inl eligible
  | cons first rest ih =>
      rcases ih _ _ eligible with prior | ⟨history, isPrefix, accepted⟩
      · simp only [Bool.or_eq_true] at prior
        rcases prior with old | current
        · exact Or.inl old
        · exact Or.inr ⟨[], ⟨first :: rest, rfl⟩, current⟩
      · obtain ⟨suffix, same⟩ := isPrefix
        exact Or.inr ⟨first :: history, ⟨suffix, by simp [same]⟩, accepted⟩

/-- Admission under a fixed snapshot identifies an actual earlier eligibility boundary. -/
theorem State.acceptsBatch_go_eachAccepted (queue : State)
    (events before : List GraphEvent) (event : GraphEvent)
    (available : List (Occurrence × Nat))
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    (earlier : (before ++ [event]).IsPrefix events)
    : ∃ history,
        history.IsPrefix before
        ∧ (queue.replayGraphEvents history available).acceptsGraphEvent event = true := by
  obtain ⟨after, joined⟩ := earlier
  have all : State.acceptsBatch.go (fun _ => false) available queue
      ((before ++ [event]) ++ after) = true := joined ▸ accepted
  have prefixAccepted := all |> State.acceptsBatch_go_prefix
  rw [State.acceptsBatch_go_append] at prefixAccepted
  have last := (Bool.and_eq_true_iff.mp prefixAccepted).2
  have permission := (State.acceptsBatch_go_cons_eligible _ _ _ event [] last).1
  simp only [Bool.or_eq_true] at permission
  rcases permission with previous | current
  · rcases State.replayEligibility_witness _ queue _ before event previous with impossible | witness
    · cases impossible
    · exact witness
  · exact ⟨before, ⟨[], by simp⟩, current⟩

/-- Prefix invariants may use the evidence established at every earlier history cut. -/
theorem prefix_invariant {α : Type} (events : List α) (property : List α → Prop)
    (initial : property [])
    (step
      : ∀ history event rest,
          events = history ++ event :: rest
          → (∀ earlier, earlier.IsPrefix history → property earlier)
          → property (history ++ [event]))
    : property events := by
  have loop (remaining history : List α) (split : events = history ++ remaining)
      (known : ∀ earlier, earlier.IsPrefix history → property earlier)
      : property events := by
    induction remaining generalizing history with
    | nil => simpa only [split, List.append_nil] using known history (List.prefix_refl _)
    | cons event rest ih =>
        have next := step history event rest split known
        apply ih (history ++ [event]) (by simp [split, List.append_assoc])
        intro earlier before
        by_cases shorter : earlier.length ≤ history.length
        · exact known earlier (List.prefix_of_prefix_length_le before
            (List.prefix_append _ _) shorter)
        · have same : earlier = history ++ [event] := before.eq_of_length_le (by
            simp only [List.length_append, List.length_singleton]
            omega)
          exact same ▸ next
  exact loop events []
    (by simp)
    (fun earlier before => by
      have empty := List.eq_nil_of_prefix_nil before
      exact empty ▸ initial)

/-- Every admitted callback was eligible at a boundary at or before its consumption. -/
theorem State.acceptsBatch_eachAccepted (queue : State) (batch before : List GraphEvent)
    (event : GraphEvent) (accepted : queue.acceptsBatch batch = true)
    (earlier : (before ++ [event]).IsPrefix batch)
    : ∃ history,
        history.IsPrefix before
        ∧ (queue.replayGraphEvents history
            (GraphEvent.availableFailures batch)).acceptsGraphEvent
            event
          = true := by
  obtain ⟨after, joined⟩ := earlier
  have all : State.acceptsBatch.go (fun _ => false) (GraphEvent.availableFailures batch) queue
      ((before ++ [event]) ++ after) = true := by
    simpa only [joined, State.acceptsBatch] using accepted
  have prefixAccepted := all |> State.acceptsBatch_go_prefix
  rw [State.acceptsBatch_go_append] at prefixAccepted
  have last := (Bool.and_eq_true_iff.mp prefixAccepted).2
  have permission := (State.acceptsBatch_go_cons_eligible _ _ _ event [] last).1
  simp only [Bool.or_eq_true] at permission
  rcases permission with previous | current
  · rcases State.replayEligibility_witness _ queue _ before event previous with impossible | witness
    · cases impossible
    · exact witness
  · exact ⟨before, ⟨[], by simp⟩, current⟩

/-- An accepted batch history exposes a later batch at the batch-aware history state. -/
theorem State.batchesStarted_eachBatch (queue : State)
    (before : List (List GraphEvent)) (batch : List GraphEvent)
    (after : List (List GraphEvent))
    (valid : queue.batchesStarted (before ++ batch :: after) = true)
    : (queue.replayBatches before).acceptsBatch batch = true := by
  rw [State.batchesStarted_append] at valid
  exact ((queue.replayBatches before).batchesStarted_cons batch after
    (Bool.and_eq_true_iff.mp valid).2).2.1

/-- The public start discipline licenses an event with its original host-batch snapshot. -/
theorem inputsStarted_eachAccepted (work : Execution.Work)
    (beforeBatches afterBatches : List (List GraphEvent))
    (batch before : List GraphEvent) (event : GraphEvent)
    (started : inputsStarted work (beforeBatches ++ batch :: afterBatches) = true)
    (earlier : (before ++ [event]).IsPrefix batch)
    : ∃ history,
        history.IsPrefix before
        ∧ (((State.initialize (Work.fromExecution work)).replayBatches
              beforeBatches).replayGraphEvents
            history (GraphEvent.availableFailures batch)).acceptsGraphEvent
            event
          = true := by
  rw [inputsStarted_eq_batchesStarted] at started
  exact State.acceptsBatch_eachAccepted _ batch before event
    (State.batchesStarted_eachBatch _ beforeBatches batch afterBatches started) earlier

/-- One unfinished batch uses fixed-snapshot event replay, then may set termination. -/
theorem State.handleGraphEvents_stateCore (queue : State) (events : List GraphEvent)
    (startOpen : queue.terminated = false)
    : ∃ terminal : Bool,
        (queue.handleGraphEvents events).1
        = {
          queue.replayGraphEvents events (GraphEvent.availableFailures events) with
            terminated := terminal
        } := by
  let available := GraphEvent.availableFailures events
  let step (acc : State × List WorkQueueEvent) (event : GraphEvent) :=
    let (next, produced) := acc.1.dispatchGraphEvent event available
    (next, acc.2 ++ produced)
  have folded : (events.foldl step (queue, [])).1
      = queue.replayGraphEvents events available :=
    queue.foldGraphEvents_state [] events available
  unfold State.handleGraphEvents
  simp only [startOpen, Bool.false_eq_true, ite_false]
  split
  · refine ⟨true, ?_⟩
    change { (events.foldl step (queue, [])).1 with terminated := true }
      = { queue.replayGraphEvents events available with terminated := true }
    exact congrArg (fun current => { current with terminated := true }) folded
  · refine ⟨(events.foldl step (queue, [])).1.terminated, ?_⟩
    change (events.foldl step (queue, [])).1
      = { queue.replayGraphEvents events available with
          terminated := (events.foldl step (queue, [])).1.terminated }
    rw [folded]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
