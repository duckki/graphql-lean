import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationDispatch
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! Exact generated host-batch correspondence, including queued notices and termination. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

private theorem referenceDispatchFold_terminated (events : List GraphEvent)
    (acc : ReferenceDispatchAcc) (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (events.foldl (referenceDispatchStep available) acc).1.terminated
      = acc.1.terminated := by
  induction events generalizing acc with
  | nil => rfl
  | cons event rest ih =>
      exact (ih (referenceDispatchStep available acc event)).trans
        (by
          simpa only [referenceDispatchStep, ReferenceWorkQueue.State.dispatchGraphEvent,
            ReferenceWorkQueue.State.enqueueGroupFailures]
            using acc.1.handleGraphEvent_terminated event available)

private theorem reference_handleGraphEvents_eq (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    : queue.handleGraphEvents batch
      = if queue.terminated then
          (queue, [])
        else
          let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
          let folded := batch.foldl (referenceDispatchStep available) (queue, [])
          if folded.1.rootGroups.isEmpty
              && folded.1.rootStreams.isEmpty
              && folded.1.groupFailureEvents.isEmpty then
            ({ folded.1 with terminated := true }, folded.2 ++ [.workQueueTermination])
          else
            (folded.1, folded.2) :=
  rfl

/-- An actual generated host batch has the reference's exact residual and wire output.
Witness: fixed-snapshot FIFO correspondence preserves the pending internal queue and emitted
output. The shared termination test requires all controls to be consumed before cleanup.
-/
theorem referencePrefix_handleGraphEvents {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ batch :: later) = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
          earlier
      let reference := queue.handleGraphEvents batch
      let alternative := (State.fromReference queue).handleGraphEvents batch
      alternative.state = State.fromReference reference.1
      ∧ alternative.workQueueEvents = reference.2 := by
  let queue := (ReferenceWorkQueue.State.initialize
    (ReferenceWorkQueue.Work.fromExecution work)).replayBatches earlier
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  have checked : (ReferenceWorkQueue.State.initialize
      (ReferenceWorkQueue.Work.fromExecution work)).batchesStarted (earlier ++ batch :: later)
      = true := by rwa [← ReferenceWorkQueue.inputsStarted_eq_batchesStarted]
  rw [ReferenceWorkQueue.State.batchesStarted_append, Bool.and_eq_true] at checked
  have running : queue.terminated = false :=
    (queue.batchesStarted_cons batch later checked.2).1
  have core := referenceBatch_graphFold_projection generated earlier batch later valid started
  have stopped := graphDispatchFold_stopped batch
    ({ state := { queue } } : GraphBatchResult) available
  have terminal := referenceDispatchFold_terminated batch (queue, []) available
  have starting : State.fromReference queue = ({ queue } : State) := by
    simp only [State.fromReference, running, Bool.false_eq_true, ↓reduceIte]
  cases folded
        : batch.foldl (fun acc event => acc.handleGraphEvent event available)
            ({ state := { queue } } : GraphBatchResult) with
  | mk state events effects =>
      cases state with
      | mk current guard =>
          change ((batch.foldl (fun acc event => acc.handleGraphEvent event available)
            ({ state := { queue } } : GraphBatchResult)).state.queue,
            (batch.foldl (fun acc event => acc.handleGraphEvent event available)
              ({ state := { queue } } : GraphBatchResult)).workQueueEvents)
            = batch.foldl (referenceDispatchStep available) (queue, []) at core
          rw [folded] at core stopped
          change guard = false at stopped
          subst guard
          dsimp only at core
          rw [← core] at terminal
          change current.terminated = queue.terminated at terminal
          rw [running] at terminal
          change ((State.fromReference queue).handleGraphEvents batch).state
              = State.fromReference (queue.handleGraphEvents batch).1
            ∧ ((State.fromReference queue).handleGraphEvents batch).workQueueEvents
              = (queue.handleGraphEvents batch).2
          rw [starting, reference_handleGraphEvents_eq]
          dsimp only [available] at folded
          simp only [State.handleGraphEvents, running, Bool.false_or, Bool.false_eq_true,
            ↓reduceIte, folded]
          rw [← core]
          dsimp only
          by_cases empty : (current.rootGroups.isEmpty && current.rootStreams.isEmpty
              && current.groupFailureEvents.isEmpty) = true
          · simp [empty, State.fromReference, State.cancel, State.clearRecords]
          · simp [empty, State.fromReference, terminal]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
