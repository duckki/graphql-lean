import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedProducerSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawPublicationClosures
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Item handlers preserve strict ordering for object producers of released object work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An ancestor-supported object producer precedes a child's item-handler value block.
Witness: source readiness derives its earlier settlement and common-ledger storage.
Item integration preserves those entry buffers in every drain prefix. Structural ancestry
retires the supporting owner before the child's exact flush, and carrier health rules out
cancellation; the common ledger must therefore contain the earlier producer value.
-/
theorem ExecutedWork.streamItems_ancestorProducer_beforeValue
    {work before stream items published position group values address owners source
      payload dependencies key parentOwners parentProducer parentPayload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.streamItems stream items])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [.streamItems stream items]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).streamItems
          stream items).2[position]?
        = some (.groupValues group values))
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup source)) payload)
    (contributes : group.key ∈ owners)
    (record : GroupRecordAt work group dependencies) (ancestor : key ∈ dependencies)
    (parentKnown
      : TaskAt work (.executionGroup source) parentOwners parentProducer parentPayload)
    (parentContributes : key ∈ parentOwners)
    : ∃ value,
        (Occurrence.executionGroup source, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).streamItems
                    stream items).2.take
                    position).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayGraphEvents before
  let offset := ((initial.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
  obtain ⟨groups, streams, next⟩ := (queue.handleGraphEvent_publicationPairs
    (.streamItems stream items)).next selected
  have carrier : Execution.WorkQueueEvent.groupSuccess group groups streams
      ∈ (queue.handleGraphEvent (.streamItems stream items)).2 :=
    List.mem_of_getElem? next
  obtain ⟨parentResult, succeeded, emitted | buffered⟩ :=
    generated.successfulCarrier_ancestorProducer_published_or_buffered valid started covered
      carrier known contributes record ancestor parentKnown parentContributes
  · exact ⟨parentResult.value, List.take_subset_take_left _ (Nat.le_add_right ..) emitted⟩
  · obtain ⟨node, lookup, stored, taskOwners, nodeContributes, present⟩ := buffered
    obtain ⟨active, index, atDrain, prefixEq, finalEq⟩ :=
      queue.streamItems_value_boundary stream items selected
    have sourceMatched := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
    obtain ⟨parents, canonical, matching, links, live, tasks, roots, closed⟩ :=
      generated.replayGraphEvents_streamPreparedRetirement before
        (fun _ member => (valid.prefix (List.prefix_append before [_])).eachMatches member)
        sourceMatched
    obtain ⟨_, _, _, healthy, _⟩ :=
      generated.replayGraphEvents_successfulCarrier_retiredHealthy valid
        (State.acceptsBatch_prefix started) carrier
    have ancestorHealthy : ¬GroupRecordInvalidated work
        (initial.objectFailureContributions (before ++ [.streamItems stream items])) key :=
      fun invalid => healthy (.ancestor record ancestor invalid)
    have notCancelled :=
      (generated.replayGraphEvents_cancelledRecordsSupported _ valid).healthy_not_mem
        ancestorHealthy
    have finalState : initial.replayGraphEvents (before ++ [.streamItems stream items])
        = (queue.preparedStreamItems items).drainReadyGroups.1 := by
      rw [State.replayGraphEvents_append]
      exact finalEq
    rw [finalState] at notCancelled
    have prefixes := covered.atPrefixDrainOwners before (.streamItems stream items) []
    have delivered := State.drainReadyGroups_go_ancestorValue_before generated matching links
      canonical live tasks roots closed (prefixes active) atDrain record ancestor lookup
      stored taskOwners nodeContributes present notCancelled
    refine ⟨parentResult.value, ?_⟩
    change (Occurrence.executionGroup source, parentResult.value)
      ∈ published.take (offset +
        (((queue.streamItems stream items).2.take position).flatMap
          WorkQueueEvent.objectValues).length)
    rw [prefixEq, List.take_add]
    apply List.mem_append_right
    rw [List.take_take] at delivered
    exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
