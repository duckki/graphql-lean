import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExactOutputCuts

/-! Arbitrary output projections retain exact positions across actual host-batch boundaries. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A fixed-snapshot output cut retains its handler and exact earlier projection count. -/
theorem State.rawEventReplay_output_projected_atSnapshot {α : Type}
    (project : WorkQueueEvent → List α) (queue : State)
    (received : List GraphEvent) (available : List (Occurrence × Nat)) {index output}
    (selected : (queue.rawEventReplay received available).2[index]? = some output)
    : ∃ before event after position,
        received = before ++ event :: after
        ∧ ((queue.replayGraphEvents before available).handleGraphEvent event
            available).2.1[position]?
          = some output
        ∧ (((queue.rawEventReplay received available).2.take index).flatMap
            project).length
          = ((queue.rawEventReplay before available).2.flatMap project).length
            + ((((queue.replayGraphEvents before available).handleGraphEvent event
                  available).2.1.take
                  position).flatMap
                project).length := by
  obtain ⟨before, event, after, position, split, atEvent, prefixEq⟩ :=
    queue.rawEventReplay_output_prefix_atSnapshot received available selected
  exact ⟨
    before,
    event,
    after,
    position,
    split,
    atEvent,
    by
      rw [prefixEq, List.flatMap_append, List.length_append]
  ⟩

/-- A raw output cut retains its actual host batch and earlier projection count. -/
theorem State.rawBatches_output_projected_at {α : Type}
    (project : WorkQueueEvent → List α) (queue : State) (batches : List (List GraphEvent))
    {index output} (selected : (queue.rawBatches batches).2[index]? = some output)
    : ∃ earlier batch later position,
        batches = earlier ++ batch :: later
        ∧ ((queue.replayBatches earlier).handleGraphEvents batch).2[position]?
          = some output
        ∧ (((queue.rawBatches batches).2.take index).flatMap project).length
          = ((queue.rawBatches earlier).2.flatMap project).length
            + ((((queue.replayBatches earlier).handleGraphEvents batch).2.take
                  position).flatMap
                project).length := by
  obtain ⟨earlier, batch, later, position, split, atEvent, prefixEq⟩ :=
    queue.rawBatches_output_prefix_at batches selected
  exact ⟨
    earlier,
    batch,
    later,
    position,
    split,
    atEvent,
    by
      rw [prefixEq, List.flatMap_append, List.length_append]
  ⟩

/-- An immediate batch output retains its exact FIFO position and projected prefixEq. -/
theorem State.handleGraphEvents_startup_immediate_projectedPrefix {α : Type}
    (project : WorkQueueEvent → List α) (queue : State)
    (batch : List GraphEvent) {index output}
    (selected : (queue.handleGraphEvents batch).2[index]? = some output)
    (notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2[index]?
        = some output
      ∧ (((queue.handleGraphEvents batch).2.take index).flatMap project).length
        = (((queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.take
              index).flatMap
            project).length := by
  obtain ⟨atReplay, prefixEq⟩ := queue.handleGraphEvents_immediate_rawPrefix batch selected
    notStartup notTermination
  exact ⟨atReplay, congrArg (fun events => (events.flatMap project).length) prefixEq⟩

/-- Ordinary projected-prefix accounting uses the exact FIFO output-prefix proof. -/
theorem State.handleGraphEvents_immediate_projectedPrefix {α : Type}
    (project : WorkQueueEvent → List α) (queue : State)
    (batch : List GraphEvent) {index output}
    (selected : (queue.handleGraphEvents batch).2[index]? = some output)
    (notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2[index]?
        = some output
      ∧ (((queue.handleGraphEvents batch).2.take index).flatMap project).length
        = (((queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.take
              index).flatMap
            project).length :=
  queue.handleGraphEvents_startup_immediate_projectedPrefix project batch selected
    notStartup notTermination

/-- An immediate output retains its actual batch/FIFO handler and projected offset. -/
theorem State.rawBatches_immediate_projectedCut {α : Type}
    (project : WorkQueueEvent → List α) (queue : State)
    (batches : List (List GraphEvent)) {index output}
    (selected : (queue.rawBatches batches).2[index]? = some output)
    (notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : ∃ earlier batch later fifo source tail position,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ (((queue.replayBatches earlier).replayGraphEvents fifo
              (GraphEvent.availableFailures batch)).handleGraphEvent
            source (GraphEvent.availableFailures batch)).2.1[position]?
          = some output
        ∧ (((queue.rawBatches batches).2.take index).flatMap project).length
          = ((queue.rawBatches earlier).2.flatMap project).length
            + (((queue.replayBatches earlier).rawEventReplay fifo
                  (GraphEvent.availableFailures batch)).2.flatMap
                project).length
            + (((((queue.replayBatches earlier).replayGraphEvents fifo
                    (GraphEvent.availableFailures batch)).handleGraphEvent
                  source (GraphEvent.availableFailures batch)).2.1.take
                  position).flatMap
                project).length := by
  obtain ⟨earlier, batch, later, localIndex, split, atBatch, batchCount⟩ :=
    queue.rawBatches_output_projected_at project batches selected
  obtain ⟨atReplay, sameCount⟩ :=
    (queue.replayBatches earlier).handleGraphEvents_immediate_projectedPrefix project batch atBatch
      notStartup notTermination
  obtain ⟨fifo, source, tail, position, batchEq, atHandler, handlerCount⟩ :=
    (queue.replayBatches earlier).rawEventReplay_output_projected_atSnapshot project batch
      (GraphEvent.availableFailures batch) atReplay
  exact ⟨
    earlier,
    batch,
    later,
    fifo,
    source,
    tail,
    position,
    split,
    batchEq,
    atHandler,
    by rw [batchCount, sameCount, handlerCount, Nat.add_assoc]
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
