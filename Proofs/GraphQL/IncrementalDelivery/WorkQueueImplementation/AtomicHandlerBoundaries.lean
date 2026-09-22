import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceHandlerBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeFailureSupport

/-! Canonical atomic outputs retain a joint source, publication, and failure boundary. -/

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
-- One positional split supplies both the object prefix and the visible failure inventory
-----------------------------------------------------------------------------------------

/-- A canonical atom retains its actual source handler, publication count, and earlier cuts.
Witness: flatten actual handler annotations and split once at the atom's position. The
same split recovers the handler's publisher and the accepted failures visible at that
output cut. No independent equal-payload lookup or event-admission premise is used.
-/
theorem Witness.handlerBoundary {work inputs} {w : Witness} {index event}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    {streams : FailureCuts}
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
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
                  normalizedObjectValues).length
          ∧ ((initialQueue work).objectFailureContributions before).Subset
              (failedBefore w.failures index) := by
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
  obtain ⟨before, source, after, publisher, localIndex, shape, localAt, _, strict, visible⟩ :=
    queue.sourceOutputBlocks_atomicHandler initialPublisher inputs.flatten atAtom
  have accepted := queue.batchesStarted_acceptsBatch inputs batches
  rw [shape] at accepted
  refine ⟨before, source, after, publisher, localIndex, shape,
    State.acceptsBatch_prefix accepted, localAt, ?_, ?_⟩
  · rw [exactHistory, strict, List.flatMap_append, List.length_append,
      initialPublisher.normalizeBatch_atomicObjectValues]
  · intro occurrence earlier
    have through : occurrence ∈ queue.objectFailureContributions (before ++ [source]) := by
      rw [queue.objectFailureContributions_append]
      exact List.mem_append_right _ earlier
    rw [← visible, List.mem_reverse] at through
    have samePartition := partition
    dsimp only at samePartition
    rw [queue.sourceRunBlocks_objectCuts initialPublisher inputs batches] at samePartition
    exact (failedBefore_partition samePartition index).mem_iff.mpr
      (List.mem_append_right _ through)

/-- A canonical handler's retained caches are supported by failures at that same atom's cut.
Witness: the joint handler boundary above, generated accepted-cache accounting, and
inclusion of its accepted inventory in the original mixed cuts. Internal success-release
operations can preserve this support without selecting a new history or failure witness.
-/
theorem Witness.handlerBoundary_cachedFailures {work inputs} {w : Witness} {index event}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    {streams : FailureCuts}
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streams
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (selected : w.events[index]? = some event)
    : ∃ before source after,
      ∃ publisher : IncrementalPublisher,
      ∃ localIndex,
        inputs.flatten = before ++ source :: after
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
                  normalizedObjectValues).length
          ∧ current.CachedFailuresSupported work (failedBefore w.failures index) := by
  obtain ⟨before, source, after, publisher, localIndex, shape, accepted, emitted, count, visible⟩ :=
    Witness.handlerBoundary started history partition selected
  have prior : ValidGraphEvents work before := valid.prefix ⟨source :: after, shape.symm⟩
  exact ⟨before, source, after, publisher, localIndex, shape, emitted, count,
    (generated.replayGraphEvents_cachedAcceptedFailures prior accepted).weaken visible⟩

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
