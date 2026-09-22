import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorPublicationBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedProducerSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReleaseAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskPublicationBoundary

/-! Object producers precede child value blocks throughout one successful task handler. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Source readiness and common-ledger conservation discharge internal drain premises
-----------------------------------------------------------------------------------------

/-- An ancestor-supported object producer precedes its child's task-handler value block.
Witness: already-active owners use prior retirement. Otherwise the block belongs to the
later drain; freshness preserves the previously settled producer's exact buffer through
preparation, and carrier health excludes cancellation. The common internal-prefix ledger
then places that value strictly before the child's block, even with same-handler activation.
-/
theorem ExecutedWork.taskSuccess_ancestorProducer_beforeValue
    {work before occurrence result published position group values address owners source
      payload dependencies key parentOwners parentProducer parentPayload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [.taskSuccess occurrence result]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.taskSuccess occurrence result])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [.taskSuccess occurrence result]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskSuccess
          occurrence result).2[position]?
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
                      before).taskSuccess
                    occurrence result).2.take
                    position).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayGraphEvents before
  let offset := ((initial.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
  obtain ⟨groups, streams, next⟩ := (queue.taskSuccess_publicationPairs occurrence result).next
    selected
  have carrier : Execution.WorkQueueEvent.groupSuccess group groups streams
      ∈ (queue.handleGraphEvent (.taskSuccess occurrence result)).2 :=
    List.mem_of_getElem? next
  by_cases active : group.key ∈ queue.rootGroups
  · obtain ⟨value, emitted⟩ := generated.activeAncestorContributor_published_before_handler
      valid started covered carrier active record ancestor parentKnown parentContributes
    exact ⟨value, List.take_subset_take_left _ (Nat.le_add_right ..) emitted⟩
  · obtain ⟨incoming, found, guard, index, atDrain, prefixEq⟩ :=
      queue.taskSuccess_inactiveValue_drain occurrence result selected active
    let prepared :=
      ((queue.putTaskNode { incoming with value := some result.value }).maybeIntegrateWork
        result.work (some occurrence)).1
    let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
    let activated := released.1.startNewWork released.2.2
    obtain ⟨parentResult, succeeded, emitted | buffered⟩ :=
      generated.successfulCarrier_ancestorProducer_published_or_buffered valid started covered
        carrier known contributes record ancestor parentKnown parentContributes
    · exact ⟨parentResult.value, List.take_subset_take_left _ (Nat.le_add_right ..) emitted⟩
    · obtain ⟨node, lookup, stored, taskOwners, nodeContributes, present⟩ := buffered
      have sourceMatched := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
      have freshness := (valid.atPrefix (before := before)
        (event := .taskSuccess occurrence result) ⟨[], by simp⟩).2.1
      have different : occurrence ≠ .executionGroup source := by
        intro same
        apply freshness.2.2.1 occurrence List.mem_cons_self
        rw [same]
        exact GraphEvent.successes_mem_settled
          (List.mem_flatMap.mpr ⟨_, succeeded, List.mem_cons_self⟩)
      have retained := State.putTaskNode_lookup_other lookup
        { incoming with value := some result.value }
        ((State.taskNode?_some found).2 ▸ different)
      have preparedLookup := State.maybeIntegrateWork_lookup_other retained result.work
        (some occurrence) (fun same => different (Option.some.inj same))
      have preparedPresent := State.maybeIntegrateWork_includesKeys
        (queue.putTaskNode { incoming with value := some result.value }) result.work
        (some occurrence) key present
      obtain ⟨_, _, _, healthy, _⟩ :=
        generated.replayGraphEvents_successfulCarrier_retiredHealthy valid
          (State.acceptsBatch_prefix started) carrier
      have ancestorHealthy : ¬GroupRecordInvalidated work
          (initial.objectFailureContributions (before ++ [.taskSuccess occurrence result]))
          key := fun invalid => healthy (.ancestor record ancestor invalid)
      have notCancelled :=
        (generated.replayGraphEvents_cancelledRecordsSupported _ valid).healthy_not_mem
          ancestorHealthy
      have finalState : initial.replayGraphEvents (before ++ [.taskSuccess occurrence result])
          = activated.drainReadyGroups.1 := by
        rw [State.replayGraphEvents_append]
        change (queue.taskSuccess occurrence result).1 = _
        rw [queue.taskSuccess_eq occurrence result incoming found]
        simp only [guard, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rfl
      rw [finalState] at notCancelled
      have prefixes := covered.atPrefixDrainOwners before (.taskSuccess occurrence result) []
      have delivered := generated.taskSuccess_drainAncestorValue_before
        (fun event member => (valid.prefix (List.prefix_append before [_])).eachMatches member)
        sourceMatched record ancestor taskOwners nodeContributes stored prefixes found guard
        preparedLookup preparedPresent atDrain notCancelled
      refine ⟨parentResult.value, ?_⟩
      change (Occurrence.executionGroup source, parentResult.value)
        ∈ published.take (offset +
          (((queue.taskSuccess occurrence result).2.take position).flatMap
            WorkQueueEvent.objectValues).length)
      rw [prefixEq, List.take_add]
      apply List.mem_append_right
      rw [List.take_take] at delivered
      exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
