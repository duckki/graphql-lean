import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay

/-! Source frames on both sides of an actual batch/FIFO input retain its cache snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Valid buffered host input derives both source frames and eligibility at an earlier dispatch boundary. -/
theorem ExecutedWork.uncancelledFrames_atBatchEvent {work parents batches}
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (List.flatten batches))
    (started : inputsStarted work batches = true)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent) (event : GraphEvent)
    (tail : List GraphEvent) (split : batches = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ event :: tail)
    : let current :=
        ((State.initialize (Work.fromExecution work)).replayBatches
          earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch)
      ValidGraphEvents work (earlier.flatten ++ fifo ++ [event])
      ∧ (∃ seen,
          seen.IsPrefix fifo
          ∧ (((State.initialize (Work.fromExecution work)).replayBatches
                earlier).replayGraphEvents
              seen (GraphEvent.availableFailures batch)).acceptsGraphEvent
              event
            = true)
      ∧ UncancelledReplayFrame current work parents (earlier.flatten ++ fifo)
      ∧ UncancelledReplayFrame
          (current.handleGraphEvent event (GraphEvent.availableFailures batch)).1 work
          parents (earlier.flatten ++ fifo ++ [event]) := by
  let initial := State.initialize (Work.fromExecution work)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  have sourceValid := valid.prefix (show (earlier.flatten ++ fifo ++ [event]).IsPrefix
    batches.flatten from ⟨tail ++ later.flatten, by simp [split, batchEq, List.append_assoc]⟩)
  have starts := split ▸ started
  rw [inputsStarted_eq_batchesStarted, State.batchesStarted_append, Bool.and_eq_true] at starts
  obtain ⟨_, accepted, _⟩ := boundary.batchesStarted_cons batch later starts.2
  have sourceAccepted := boundary.acceptsBatch_eachAccepted batch fifo event accepted
    ⟨tail, by simp [batchEq, List.append_assoc]⟩
  have beforeFrame := generated.uncancelledFrame_atBatchPrefix canonical earlier batch later fifo
    (split ▸ valid) (split ▸ started) ⟨event :: tail, batchEq.symm⟩
  have afterFrame := generated.uncancelledFrame_atBatchPrefix canonical earlier batch later
    (fifo ++ [event]) (split ▸ valid) (split ▸ started)
    ⟨tail, by simp [batchEq, List.append_assoc]⟩
  refine ⟨sourceValid, sourceAccepted, beforeFrame, ?_⟩
  have dispatched : UncancelledReplayFrame
      ((boundary.replayGraphEvents fifo available).dispatchGraphEvent event available).1
      work parents (earlier.flatten ++ fifo ++ [event]) := by
    simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc]
      using afterFrame
  exact dispatched.withGroupFailures
    (((boundary.replayGraphEvents fifo available).handleGraphEvent event
        available).1.groupFailureEvents)

/-- A processed object callback registers its complete child chunk, and the permanent
catalogue retains those tasks through the remaining FIFO inputs and later host batches.
-/
theorem TaskAt.executionGroup_registered_after_batch_object
    {work inputs earlier batch later fifo tail producer result node address owners
      payload}
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    (matching : (GraphEvent.taskSuccess producer result).MatchesWork work)
    (started : inputsStarted work inputs = true)
    (split : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ .taskSuccess producer result :: tail)
    (found
      : ((((State.initialize (Work.fromExecution work)).replayBatches
            earlier).replayGraphEvents
            fifo (GraphEvent.availableFailures batch)).cacheTaskFailures
          (GraphEvent.availableFailures batch)).taskNode?
          producer
        = some node)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  let initial := State.initialize (Work.fromExecution work)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  obtain ⟨task, member, identity, groups⟩ :=
    State.taskSuccess_child_registered found matching known available
  have afterMember : task ∈
      (current.dispatchGraphEvent (.taskSuccess producer result) available).1.tasks
      := member
  have remaining := (current.dispatchGraphEvent (.taskSuccess producer result)
    available).1.replayGraphEvents_tasks_subset tail available afterMember
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← split, ← inputsStarted_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  obtain ⟨running, _, _⟩ := boundary.batchesStarted_cons batch later checked.2
  obtain ⟨terminal, core⟩ := boundary.handleGraphEvents_stateCore batch running
  have batchMember : task ∈ (boundary.handleGraphEvents batch).1.tasks := by
    rw [core]
    change task ∈ (boundary.replayGraphEvents batch available).tasks
    rw [batchEq, State.replayGraphEvents_append _ _ _ available]
    exact remaining
  have retained := (boundary.handleGraphEvents batch).1.replayBatches_tasks_subset later batchMember
  refine ⟨task, ?_, identity, groups⟩
  simpa only [initial, boundary, State.runNormalized_replayBatches, split,
    State.replayBatches, List.foldl_append, List.foldl_cons]
    using retained

/-- Actual replay registers child tasks or certifies cancellation of every producer owner. -/
theorem ExecutedWork.runNormalized_producerRegistrationAccounting {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.ProducerRegistrationAccounting
        work inputs.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := (initial_uncancelledReplayFrame generated canonical).runNormalized
    (before := []) generated canonical inputs valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)
  exact frame.producerRegistrations

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
