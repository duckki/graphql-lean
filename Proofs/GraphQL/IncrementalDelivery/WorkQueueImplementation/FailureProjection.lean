import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskSettlements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Distinct proof projections for live failure consumption and buffered source admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The object-failure token accepted by the handler's task-presence check.
`queue` is the actual state before `event`; stream failures have a separate item inventory.
This proof-only projection records possible contributions, not licensed failure cuts.
-/
def State.objectFailureContribution (queue : State) : GraphEvent → List Occurrence
  | .taskFailure occurrence _ =>
      match queue.taskNode? occurrence with
      | none => []
      | some _ => [occurrence]
  | _ => []

/-- Contributing object failures in reverse order under one fixed availability snapshot.
The projection neither filters inputs nor changes execution. The default empty snapshot
is an eventwise proof language; actual host batches supply their full snapshot below.
-/
def State.objectFailureContributions (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : List Occurrence :=
  match events with
  | [] => []
  | event :: rest =>
      (queue.dispatchGraphEvent event available).1.objectFailureContributions rest
        available
      ++ queue.objectFailureContribution event

/-- Splitting source replay preserves the task-presence state at every recorded contribution.
Witness: list induction through the same executable handlers used by sequential replay.
-/
theorem State.objectFailureContributions_append (queue : State)
    (before after : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : queue.objectFailureContributions (before ++ after) available
      = (queue.replayGraphEvents before available).objectFailureContributions after
          available
        ++ queue.objectFailureContributions before available := by
  induction before generalizing queue with
  | nil => simp [objectFailureContributions, replayGraphEvents]
  | cons event rest ih =>
      simp only [List.cons_append, objectFailureContributions, replayGraphEvents, ih,
        List.append_assoc, List.foldl_cons]

/-- Contributing object failures form an order-preserving subset of source failures.
Witness: each task-presence check either keeps its one failure token or omits it;
induction composes those choices through the actual successive queue states.
-/
theorem State.objectFailureContributions_sublist (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : (queue.objectFailureContributions events available).Sublist
        (GraphEvent.failureSettlements events) := by
  induction events generalizing queue with
  | nil => exact .refl _
  | cons event rest ih =>
      have order : GraphEvent.failureSettlements (event :: rest)
          = GraphEvent.failureSettlements rest ++ event.groupFailures := by
        cases event <;> simp [GraphEvent.failureSettlements, GraphEvent.groupFailures]
      rw [objectFailureContributions, order]
      apply List.Sublist.append (ih (queue.dispatchGraphEvent event available).1)
      cases event <;> simp only [objectFailureContribution, GraphEvent.groupFailures]
      all_goals try exact .refl _
      split
      · exact List.nil_sublist _
      · exact .refl _

/-- Every task-failure input accepted under a fixed snapshot contributes its occurrence. -/
theorem State.objectFailureContributions_eq_of_accepts (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat))
    (accepted : State.eventsStarted available queue events = true)
    : queue.objectFailureContributions events available
      = GraphEvent.failureSettlements events := by
  induction events generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have current : queue.objectFailureContribution event = event.groupFailures := by
        cases event with
        | taskFailure occurrence errors =>
            cases found : queue.taskNode? occurrence with
            | none => simp [State.acceptsGraphEvent, found] at accepts
            | some node =>
                simp [State.objectFailureContribution, found, GraphEvent.groupFailures]
        | taskSuccess | groupFailure | streamItems | streamSuccess | streamFailure => rfl
      simp only [State.objectFailureContributions, GraphEvent.failureSettlements_cons,
        ih _ accepts.2, current]

/-- Accepted-failure projection over actual host batches, with their own cache snapshots.
This proof-only fold records no failures after termination and adds no runtime ledger.
-/
def State.objectFailureContributionsForBatches (queue : State)
    : List (List GraphEvent) → List Occurrence
  | [] => []
  | batch :: rest =>
      if queue.terminated then
        []
      else
        (queue.handleGraphEvents batch).1.objectFailureContributionsForBatches rest
        ++ queue.objectFailureContributions batch (GraphEvent.availableFailures batch)

/-- The actual accepted-failure projection contains only supplied source failures. -/
theorem State.objectFailureContributionsForBatches_sublist (queue : State)
    (batches : List (List GraphEvent))
    : (queue.objectFailureContributionsForBatches batches).Sublist
        (GraphEvent.failureSettlements batches.flatten) := by
  induction batches generalizing queue with
  | nil => exact .refl _
  | cons batch rest ih =>
      simp only [State.objectFailureContributionsForBatches]
      split
      · exact List.nil_sublist _
      · rw [List.flatten_cons, GraphEvent.failureSettlements_append_list]
        exact (ih _).append (queue.objectFailureContributions_sublist
          batch (GraphEvent.availableFailures batch))

/-- Source-admitted failure tokens retain eligibility accumulated within this host batch.
This proof projection does not claim that an already retired task is processed again.
-/
def State.admittedObjectFailureContributions (earlier : GraphEvent → Bool) (queue : State)
    (events : List GraphEvent) (available : List (Occurrence × Nat))
    : List Occurrence :=
  match events with
  | [] => []
  | event :: rest =>
      State.admittedObjectFailureContributions
        (fun candidate => earlier candidate || queue.acceptsGraphEvent candidate)
        (queue.dispatchGraphEvent event available).1 rest available
      ++ if earlier event || queue.acceptsGraphEvent event then
            event.groupFailures
          else
            []

/-- Admission can retain or omit a supplied failure, never invent a failure token. -/
theorem State.admittedObjectFailureContributions_sublist (earlier : GraphEvent → Bool)
    (queue : State) (events : List GraphEvent) (available : List (Occurrence × Nat))
    : (State.admittedObjectFailureContributions earlier queue events available).Sublist
        (GraphEvent.failureSettlements events) := by
  induction events generalizing queue earlier with
  | nil => exact .refl _
  | cons event rest ih =>
      rw [State.admittedObjectFailureContributions, GraphEvent.failureSettlements_cons]
      apply List.Sublist.append (ih _ _)
      split
      · exact .refl _
      · exact List.nil_sublist _

/-- Every source-admitted task failure is retained even if its FIFO callback is ignored. -/
theorem State.admittedObjectFailureContributions_eq_of_accepts
    (earlier : GraphEvent → Bool) (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat))
    (accepted : State.acceptsBatch.go earlier available queue events = true)
    : State.admittedObjectFailureContributions earlier queue events available
      = GraphEvent.failureSettlements events := by
  induction events generalizing queue earlier with
  | nil => rfl
  | cons event rest ih =>
      have accepts := State.acceptsBatch_go_cons_eligible earlier queue available event rest accepted
      simp only [State.admittedObjectFailureContributions, accepts.1, ite_true,
        ih _ _ accepts.2, GraphEvent.failureSettlements_cons]

/-- Source-admitted failure inventory over actual batches and their full snapshots.
The guard-accepted projection above remains separate: stale notification consumption can
omit a cause that was already available to group startup. Neither projection is state.
-/
def State.admittedObjectFailureContributionsForBatches (queue : State)
    : List (List GraphEvent) → List Occurrence
  | [] => []
  | batch :: rest =>
      if queue.terminated then
        []
      else
        (queue.handleGraphEvents batch).1.admittedObjectFailureContributionsForBatches
          rest
        ++ State.admittedObjectFailureContributions (fun _ => false) queue batch
            (GraphEvent.availableFailures batch)

/-- Source-admitted batch failures are all supplied by the host history. -/
theorem State.admittedObjectFailureContributionsForBatches_sublist (queue : State)
    (batches : List (List GraphEvent))
    : (queue.admittedObjectFailureContributionsForBatches batches).Sublist
        (GraphEvent.failureSettlements batches.flatten) := by
  induction batches generalizing queue with
  | nil => exact .refl _
  | cons batch rest ih =>
      simp only [State.admittedObjectFailureContributionsForBatches]
      split
      · exact List.nil_sublist _
      · rw [List.flatten_cons, GraphEvent.failureSettlements_append_list]
        exact (ih _).append (State.admittedObjectFailureContributions_sublist (fun _ => false) queue batch
          (GraphEvent.availableFailures batch))

/-- Checked batches retain the complete source failure inventory, including buffered stale
callbacks. This equality concerns admission, independently of live handler consumption.
-/
theorem State.admittedObjectFailureContributionsForBatches_eq_of_started (queue : State)
    (batches : List (List GraphEvent)) (started : queue.batchesStarted batches = true)
    : queue.admittedObjectFailureContributionsForBatches batches
      = GraphEvent.failureSettlements batches.flatten := by
  induction batches generalizing queue with
  | nil => rfl
  | cons batch rest ih =>
      obtain ⟨running, accepted, remaining⟩ := queue.batchesStarted_cons batch rest started
      simp only [State.admittedObjectFailureContributionsForBatches, running,
        Bool.false_eq_true, ite_false, ih _ remaining,
        State.admittedObjectFailureContributions_eq_of_accepts _ _ _ _ accepted,
        List.flatten_cons, GraphEvent.failureSettlements_append_list]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
