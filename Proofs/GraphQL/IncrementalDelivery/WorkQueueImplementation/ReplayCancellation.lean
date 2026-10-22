import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyEligibility

/-! Accepted rejection accounting and snapshot cancellation for retained rejections.
Source admission checks task presence; causal health is proof evidence, not a runtime guard.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An accepted handler records exactly the source event's object-failure token. -/
theorem State.objectFailureContribution_eq_groupFailures {queue : State}
    {event : GraphEvent} (accepted : queue.acceptsGraphEvent event = true)
    : queue.objectFailureContribution event = event.groupFailures := by
  cases event <;> simp only [objectFailureContribution, GraphEvent.groupFailures]
  split
  · simp_all [acceptsGraphEvent]
  · rfl

/-- Accepted sequential replay retains every source object rejection, including redundant
ones. Selected failure cuts are a separate proof inventory. -/
theorem State.replayGraphEvents_objectFailureContributions {queue : State}
    {events : List GraphEvent}
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → (queue.replayGraphEvents before).acceptsGraphEvent event = true)
    : queue.objectFailureContributions events = GraphEvent.failureSettlements events := by
  induction events generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      have accepted : queue.acceptsGraphEvent event = true := by
        simpa [replayGraphEvents] using acceptedAt [] event (by simp)
      rw [objectFailureContributions, State.objectFailureContribution_eq_groupFailures accepted]
      have acceptedRest : ∀ before next, (before ++ [next]).IsPrefix rest
          → ((queue.dispatchGraphEvent event).1.replayGraphEvents before).acceptsGraphEvent
              next = true := by
        intro before next earlier
        have accepted := acceptedAt (event :: before) next (by
          obtain ⟨tail, same⟩ := earlier
          exact ⟨tail, by simpa using congrArg (List.cons event) same⟩)
        simpa [replayGraphEvents, List.foldl_cons] using accepted
      rw [ih acceptedRest]
      cases event <;> simp [GraphEvent.failureSettlements, GraphEvent.groupFailures]

/-- The executable start checker preserves all failures in actual host-batch accounting. -/
theorem inputsStarted_objectFailureContributions {work : Execution.Work}
    {batches : List (List GraphEvent)} (started : inputsStarted work batches = true)
    : (State.initialize
        (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
        batches
      = GraphEvent.failureSettlements batches.flatten :=
  State.admittedObjectFailureContributionsForBatches_eq_of_started _ batches
    (by rwa [← inputsStarted_eq_batchesStarted])

/-- A retained rejected computation has no healthy contributor and cannot publish later.
This snapshot conclusion uses its stored rejection; it imposes no source-settlement guard.
-/
theorem State.OwnerAccounting.rejectedTask_cancelled {queue : State}
    {work parents before occurrence taskNode published}
    (prior : queue.OwnerAccounting work parents before)
    (generated : ExecutedWork work)
    (found : queue.taskNode? occurrence = some taskNode)
    (rejected : taskNode.rejection.isSome = true)
    (unpublished : ¬published occurrence)
    : Causality.TaskCancelled work (GraphEvent.failureSettlements before)
        published occurrence := by
  have member := List.mem_of_find?_eq_some found
  have registered := prior.pending.started taskNode member
  obtain ⟨⟨_, payload, producer, _, known⟩, _⟩ := prior.pending.matching taskNode.task registered
  have same : taskNode.task.occurrence = occurrence := (occurrence_beq_iff_eq _ _).mp
    (List.find?_some (p := fun candidate : TaskNode =>
      candidate.task.occurrence == occurrence) found)
  rw [same] at known
  refine .owners ⟨producer, payload, known⟩ unpublished
    (generated.taskOwners_nonempty known) ?_
  intro ref contributes
  exact (prior.supported.rejectedTask_ownersInvalidated member rejected
    ref contributes).toCausality published

/-- Generated replay cancels a retained rejected task relative to its accepted source
inventory. Nonpublication is explicit; this does not assert ordered report placement. -/
theorem ExecutedWork.runNormalized_rejectedTask_cancelled {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    {occurrence taskNode published}
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.taskNode?
          occurrence
        = some taskNode)
    (rejected : taskNode.rejection.isSome = true)
    (unpublished : ¬published occurrence)
    : Causality.TaskCancelled work
        ((State.initialize
            (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
          batches)
        published occurrence := by
  obtain ⟨parents, _, replayed⟩ := generated.runNormalized_ownerAncestry batches valid started
  rw [inputsStarted_objectFailureContributions started]
  exact replayed.accounting.rejectedTask_cancelled generated found rejected unpublished

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
