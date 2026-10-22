import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames

/-! Actual startup source-event frames retain cache snapshots and consumed-input cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Valid buffered host input derives both source frames and earlier dispatch-boundary eligibility. -/
theorem ExecutedWork.startup_uncancelledFrames_atBatchEvent {work parents batches}
    (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (List.flatten batches))
    (started : inputsStarted work batches startup = true)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent) (event : GraphEvent)
    (tail : List GraphEvent) (split : batches = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ event :: tail)
    : let current :=
        (((State.initialize (Work.fromExecution work) startup)).replayBatches
          earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch)
      ValidGraphEvents work (earlier.flatten ++ fifo ++ [event])
      ∧ (∃ seen,
          seen.IsPrefix fifo
          ∧ ((((State.initialize (Work.fromExecution work) startup).replayBatches
                earlier).replayGraphEvents
                seen (GraphEvent.availableFailures batch)).acceptsGraphEvent
                event
              = true))
      ∧ UncancelledReplayFrame current work parents (earlier.flatten ++ fifo)
      ∧ UncancelledReplayFrame
          (current.dispatchGraphEvent event (GraphEvent.availableFailures batch)).1 work
          parents (earlier.flatten ++ fifo ++ [event]) := by
  let initial := (State.initialize (Work.fromExecution work) startup)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  have sourceValid := valid.prefix (show (earlier.flatten ++ fifo ++ [event]).IsPrefix
    batches.flatten from ⟨tail ++ later.flatten, by simp [split, batchEq, List.append_assoc]⟩)
  have starts := split ▸ started
  rw [inputsStartedWithStartup_eq_batchesStarted, State.batchesStarted_append, Bool.and_eq_true]
    at starts
  obtain ⟨_, accepted, _⟩ := boundary.batchesStarted_cons batch later starts.2
  have sourceAccepted := boundary.acceptsBatch_eachAccepted batch fifo event accepted
    ⟨tail, by simp [batchEq, List.append_assoc]⟩
  have beforeFrame := generated.startup_uncancelledFrame_atBatchPrefix canonical startup matched
    earlier batch later fifo
    (split ▸ valid) (split ▸ started) ⟨event :: tail, batchEq.symm⟩
  have afterFrame := generated.startup_uncancelledFrame_atBatchPrefix canonical startup matched
    earlier batch later
    (fifo ++ [event]) (split ▸ valid) (split ▸ started)
    ⟨tail, by simp [batchEq, List.append_assoc]⟩
  refine ⟨sourceValid, sourceAccepted, beforeFrame, ?_⟩
  simpa only [State.replayGraphEvents_append, State.replayGraphEvents, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.append_assoc]
    using afterFrame

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
