import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceHandlerBoundaries
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

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- One positional split supplies the source handler and object prefix
-----------------------------------------------------------------------------------------

/-- A canonical atom retains its actual source handler and publication count.
Witness: flatten actual handler annotations and split once at the atom's position. The
same split recovers the handler's publisher at that output cut. No independent equal-payload lookup or event-admission premise is used.
-/
theorem Witness.handlerBoundary {work inputs} {w : Witness} {index event}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    : ∃ before source after,
      ∃ publisher : IncrementalPublisher,
      ∃ localIndex,
        inputs.flatten = before ++ source :: after
        ∧ (initialQueue work).acceptsBatch before = true
        ∧ let current := (initialQueue work).replayGraphEvents before
          ((publisher.normalizeBatch (current.handleGraphEvent source).2).2.flatMap
              publicationAtoms)[localIndex]?
            = some event
          ∧ ((w.events.take index).flatMap normalizedObjectValues).length
            = (((initialQueue work).rawEventReplay before).2.flatMap
                WorkQueueEvent.objectValues).length
              + ((((publisher.normalizeBatch
                      (current.handleGraphEvent source).2).2.flatMap
                    publicationAtoms).take
                    localIndex).flatMap
                  normalizedObjectValues).length := by
  let queue := initialQueue work
  let initialPublisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have batches : queue.batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have exactHistory : w.events
      = (queue.sourceOutputBlocks initialPublisher inputs.flatten).2.2.flatMap Prod.snd := by
    rw [(queue.sourceOutputBlocks_agrees initialPublisher inputs.flatten).2.2]
    exact history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  have atAtom := selected
  rw [exactHistory] at atAtom
  obtain ⟨before, source, after, publisher, localIndex, shape, localAt, _, strict, _⟩ :=
    queue.sourceOutputBlocks_atomicHandler initialPublisher inputs.flatten atAtom
  have accepted := queue.batchesStarted_acceptsBatch inputs batches
  rw [shape] at accepted
  refine ⟨before, source, after, publisher, localIndex, shape,
    State.acceptsBatch_prefix accepted, localAt, ?_⟩
  rw [exactHistory, strict, List.flatMap_append, List.length_append,
    initialPublisher.normalizeBatch_atomicObjectValues]

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
