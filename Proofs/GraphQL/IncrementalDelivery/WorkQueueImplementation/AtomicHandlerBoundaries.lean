import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchImmediateBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes

/-! Canonical atomic outputs retain a joint source and publication boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Publisher normalization and atomization preserve the full object-payload sequence.
Witness: each atomization preserves values, followed by the publisher's payload equation.
-/
theorem IncrementalPublisher.normalizeBatch_atomicObjectValues
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : ((publisher.normalizeBatch events).2.flatMap publicationAtoms).flatMap
        normalizedObjectValues
      = (events.flatMap WorkQueueEvent.objectValues) := by
  have atoms (outputs : List Execution.WorkQueueEvent)
      : (outputs.flatMap publicationAtoms).flatMap normalizedObjectValues
        = outputs.flatMap normalizedObjectValues := by
    induction outputs with
    | nil => rfl
    | cons output rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append, (publicationAtoms_values output).1, ih]
  rw [atoms, publisher.normalizeBatch_objectValues]

/-- Every immediate atomic output retains its actual batch/FIFO handler and object offset. -/
theorem State.sourceRunBlocks_immediateBoundary (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent)) {index output}
    (selected
      : ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)[index]?
        = some output)
    (notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : ∃ earlier batch later fifo source tail,
      ∃ currentPublisher : IncrementalPublisher,
      ∃ localIndex,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ let current :=
            (queue.replayBatches earlier).replayGraphEvents fifo
              (GraphEvent.availableFailures batch)
          ((currentPublisher.normalizeBatch
              (current.handleGraphEvent source
                (GraphEvent.availableFailures batch)).2.1).2.flatMap
              publicationAtoms)[localIndex]?
            = some output
          ∧ ((((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd).take
                index).flatMap
              normalizedObjectValues).length
            = ((queue.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
              + (((queue.replayBatches earlier).rawEventReplay fifo
                    (GraphEvent.availableFailures batch)).2.flatMap
                  WorkQueueEvent.objectValues).length
              + ((((currentPublisher.normalizeBatch
                      (current.handleGraphEvent source
                        (GraphEvent.availableFailures batch)).2.1).2.flatMap
                    publicationAtoms).take
                    localIndex).flatMap
                  normalizedObjectValues).length := by
  obtain ⟨earlier, batch, later, batchIndex, split, atBatch, position⟩ :=
    queue.sourceRunBlocks_atomicBatch publisher batches selected
  let first := queue.sourceRunBlocks publisher earlier
  let current := queue.replayBatches earlier
  let atoms := (current.sourceBatchBlocks first.2.1 batch).2.2.flatMap Prod.snd
  have immediate := current.sourceBatchBlocks_immediatePrefix first.2.1 batch atBatch
    notStartup notTermination
  obtain ⟨fifo, source, tail, handlerPublisher, localIndex, batchEq, atHandler, _, strict⟩ :=
    current.sourceOutputBlocks_atomicImmediate first.2.1 batch
      (GraphEvent.availableFailures batch) immediate.1
  have cut : ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd).take index
      = first.2.2.flatMap Prod.snd ++ atoms.take batchIndex := by
    rw [split, State.sourceRunBlocks_append]
    change ((first.2.2 ++ _).flatMap Prod.snd).take index = _
    rw [List.flatMap_append]
    have sameState : first.1 = current := queue.sourceRunBlocks_state publisher earlier
    change ((_ ++ (first.1.sourceRunBlocks first.2.1 (batch :: later)).2.2.flatMap
      Prod.snd).take index) = _
    rw [sameState, State.sourceRunBlocks, List.flatMap_append, position,
      List.take_length_add_append,
      List.take_append_of_le_length (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atBatch).1)]
  refine ⟨earlier, batch, later, fifo, source, tail, handlerPublisher, localIndex,
    split, batchEq, atHandler, ?_⟩
  rw [cut, immediate.2, strict, List.flatMap_append, List.flatMap_append,
    List.length_append, List.length_append, queue.sourceRunBlocks_rawBatches,
    IncrementalPublisher.normalizeBatch_atomicObjectValues,
    IncrementalPublisher.normalizeBatch_atomicObjectValues]
  exact (Nat.add_assoc _ _ _).symm

namespace ConformancePlan

/-- A canonical immediate atom retains its actual handler, cache snapshot and object offset.
The batch and FIFO partitions identify the same queue and publication prefix. Forwarded
startup reports have their own batch-end block and are outside this immediate-handler cut. -/
theorem Witness.handlerBoundary {work inputs} {w : Witness} {index event}
    (_started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    (notStartup : ∀ group errors, event ≠ .groupFailure group errors)
    (notTermination : event ≠ .workQueueTermination)
    : ∃ earlier batch later fifo source tail,
      ∃ publisher : IncrementalPublisher,
      ∃ localIndex,
        inputs = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ let current :=
            ((initialQueue work).replayBatches earlier).replayGraphEvents fifo
              (GraphEvent.availableFailures batch)
          ((publisher.normalizeBatch
              (current.handleGraphEvent source
                (GraphEvent.availableFailures batch)).2.1).2.flatMap
              publicationAtoms)[localIndex]?
            = some event
          ∧ ((w.events.take index).flatMap normalizedObjectValues).length
            = (((initialQueue work).rawBatches earlier).2.flatMap
                WorkQueueEvent.objectValues).length
              + ((((initialQueue work).replayBatches earlier).rawEventReplay fifo
                    (GraphEvent.availableFailures batch)).2.flatMap
                  WorkQueueEvent.objectValues).length
              + ((((publisher.normalizeBatch
                      (current.handleGraphEvent source
                        (GraphEvent.availableFailures batch)).2.1).2.flatMap
                    publicationAtoms).take
                    localIndex).flatMap
                  normalizedObjectValues).length := by
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  let queue := initialQueue work
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have output := (queue.sourceRunBlocks_agrees inputs).2
  rw [← output] at atFull beforeEq
  obtain ⟨earlier, batch, later, fifo, source, tail, handlerPublisher, localIndex, split,
    batchEq, atHandler, count⟩ := queue.sourceRunBlocks_immediateBoundary publisher inputs
    atFull notStartup notTermination
  exact ⟨earlier, batch, later, fifo, source, tail, handlerPublisher, localIndex, split,
    batchEq, atHandler, beforeEq ▸ count⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
