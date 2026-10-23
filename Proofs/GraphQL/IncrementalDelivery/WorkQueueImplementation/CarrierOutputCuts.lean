import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProjectedOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawCarrierCoverage

/-! Successful raw carriers retain actual batch and fixed-snapshot handler positions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A fixed-snapshot output cut retains its source handler and exact earlier value count. -/
theorem State.rawEventReplay_output_atSnapshot (queue : State)
    (received : List GraphEvent) (available : List (Occurrence × Nat)) {index output}
    (selected : (queue.rawEventReplay received available).2[index]? = some output)
    : ∃ before event after position,
        received = before ++ event :: after
        ∧ ((queue.replayGraphEvents before available).handleGraphEvent event
            available).2.1[position]?
          = some output
        ∧ (((queue.rawEventReplay received available).2.take index).flatMap
            WorkQueueEvent.objectValues).length
          = ((queue.rawEventReplay before available).2.flatMap
              WorkQueueEvent.objectValues).length
            + ((((queue.replayGraphEvents before available).handleGraphEvent event
                  available).2.1.take
                  position).flatMap
                WorkQueueEvent.objectValues).length :=
  queue.rawEventReplay_output_projected_atSnapshot WorkQueueEvent.objectValues received
    available selected

/-- A raw batch output cut retains the actual preceding batches and object count. -/
theorem State.rawBatches_output_at (queue : State) (batches : List (List GraphEvent))
    {index output} (selected : (queue.rawBatches batches).2[index]? = some output)
    : ∃ earlier batch later position,
        batches = earlier ++ batch :: later
        ∧ ((queue.replayBatches earlier).handleGraphEvents batch).2[position]?
          = some output
        ∧ (((queue.rawBatches batches).2.take index).flatMap
            WorkQueueEvent.objectValues).length
          = ((queue.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
            + ((((queue.replayBatches earlier).handleGraphEvents batch).2.take
                  position).flatMap
                WorkQueueEvent.objectValues).length :=
  queue.rawBatches_output_projected_at WorkQueueEvent.objectValues batches selected

/-- An immediate output precedes forwarded startup failures and termination at the same cut. -/
theorem State.handleGraphEvents_immediate_prefix (queue : State)
    (batch : List GraphEvent) {index output}
    (selected : (queue.handleGraphEvents batch).2[index]? = some output)
    (notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2[index]?
        = some output
      ∧ (((queue.handleGraphEvents batch).2.take index).flatMap
          WorkQueueEvent.objectValues).length
        = (((queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.take
              index).flatMap
            WorkQueueEvent.objectValues).length :=
  queue.handleGraphEvents_immediate_projectedPrefix WorkQueueEvent.objectValues batch
    selected notStartup notTermination

/-- Every batched successful carrier retains one actual FIFO handler and strict object count. -/
theorem State.rawBatches_immediate_handlerCut (queue : State)
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
        ∧ (((queue.rawBatches batches).2.take index).flatMap
            WorkQueueEvent.objectValues).length
          = ((queue.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
            + (((queue.replayBatches earlier).rawEventReplay fifo
                  (GraphEvent.availableFailures batch)).2.flatMap
                WorkQueueEvent.objectValues).length
            + (((((queue.replayBatches earlier).replayGraphEvents fifo
                    (GraphEvent.availableFailures batch)).handleGraphEvent
                  source (GraphEvent.availableFailures batch)).2.1.take
                  position).flatMap
                WorkQueueEvent.objectValues).length :=
  queue.rawBatches_immediate_projectedCut WorkQueueEvent.objectValues batches selected
    notStartup notTermination

/-- A successful carrier retains its actual batch/FIFO origin and strict object count. -/
theorem State.rawBatches_groupSuccess_handlerCut (queue : State)
    (batches : List (List GraphEvent)) {index group groups streams}
    (selected
      : (queue.rawBatches batches).2[index]? = some (.groupSuccess group groups streams))
    : ∃ earlier batch later fifo source tail position,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ (((queue.replayBatches earlier).replayGraphEvents fifo
              (GraphEvent.availableFailures batch)).handleGraphEvent
            source (GraphEvent.availableFailures batch)).2.1[position]?
          = some (.groupSuccess group groups streams)
        ∧ (((queue.rawBatches batches).2.take index).flatMap
            WorkQueueEvent.objectValues).length
          = ((queue.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
            + (((queue.replayBatches earlier).rawEventReplay fifo
                  (GraphEvent.availableFailures batch)).2.flatMap
                WorkQueueEvent.objectValues).length
            + (((((queue.replayBatches earlier).replayGraphEvents fifo
                    (GraphEvent.availableFailures batch)).handleGraphEvent
                  source (GraphEvent.availableFailures batch)).2.1.take
                  position).flatMap
                WorkQueueEvent.objectValues).length :=
  queue.rawBatches_immediate_handlerCut batches selected
    (by intro _ _ impossible; cases impossible)
    (by intro impossible; cases impossible)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
