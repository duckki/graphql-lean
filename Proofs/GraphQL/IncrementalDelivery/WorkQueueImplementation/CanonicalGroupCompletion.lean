import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCompletionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupNoticeFreshness

/-! Announced group completion on the actual canonical conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Publisher normalization preserves exact group-notice and completion inventories
-----------------------------------------------------------------------------------------

/-- Every canonical group notice remains active, pending or has a canonical completion.
Witness: FIFO tracking, exact notice/closure projection through normalization and atomization,
and agreement between actual raw batch replay and the normalized final state.
No abstract admission, failure matching, or terminal premise is required.
-/
theorem groupNoticeRefs_tracked {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (_started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : ∀ ref ∈ (initialQueue work).rootGroups ++ w.events.flatMap groupNoticeRefs,
        ref ∈ ((initialQueue work).runNormalized inputs).1.groupNoticeSupport
        ∨ ref ∈ w.events.flatMap groupClosureRefs := by
  let publisher : IncrementalPublisher :=
    { active := (initialQueue work).initialGroups ++ (initialQueue work).initialStreams }
  have noticeProjection := atomicGroupNotices publisher ((initialQueue work).rawBatches inputs).2
    ((initialQueue work).rawBatches_nonemptyValues inputs valid.nonemptyItems)
  rw [Witness.rawBatches_shape history] at noticeProjection
  have notices : w.events.flatMap groupNoticeRefs =
      ((initialQueue work).rawBatches inputs).2.flatMap rawGroupNoticeRefs := by
    split at noticeProjection <;>
      simpa [List.flatMap_append, groupNoticeRefs] using noticeProjection
  have closureProjection : ((publisher.normalizeBatch
      ((initialQueue work).rawBatches inputs).2).2.flatMap publicationAtoms).flatMap
        groupClosureRefs
      = ((initialQueue work).rawBatches inputs).2.flatMap rawGroupClosureRefs := by
    rw [List.flatMap_assoc]
    simp only [publicationAtoms_groupClosureRefs,
      IncrementalPublisher.normalizeBatch_groupClosureRefs]
  rw [Witness.rawBatches_shape history] at closureProjection
  have closures : w.events.flatMap groupClosureRefs =
      ((initialQueue work).rawBatches inputs).2.flatMap rawGroupClosureRefs := by
    split at closureProjection <;>
      simpa [List.flatMap_append, groupClosureRefs] using closureProjection
  intro ref member
  rw [notices] at member
  rw [State.runNormalized_replayBatches, closures]
  have tracked := generated.rawBatches_groupNoticeCompletion inputs
    (fun _ member => valid.eachMatches member) ref member
  simpa only [State.rawBatches_state] using tracked

-----------------------------------------------------------------------------------------
-- The announced-group branch of terminal node accounting is discharged
-----------------------------------------------------------------------------------------

/-- A generated group announced anywhere in a terminated canonical history has completed.
Witness: generated group/stream role separation identifies its group notice; exact replay
tracking and empty final roots force a real completion. This covers successful and failed
groups, but makes no claim yet about omitted latent nodes or announced streams.
-/
theorem groupNode_terminalCompleted {work inputs node dependencies producer} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : NodeAt work node .group dependencies producer)
    (announced : node.ref ∈ announcedRefs (initialRefs work) w.events)
    : node.ref ∈ completedRefs w.events := by
  have groupNotice := groupNode_announced_group (index := w.events.length)
    generated valid history known (by simpa only [List.take_length] using announced)
  simp only [List.take_length] at groupNotice
  rcases groupNoticeRefs_tracked generated valid started history node.ref groupNotice with
    active | completed
  · have roots := (createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended).1
    have pending := createWorkQueue_terminalPending (Work.fromExecution work) inputs ended
    simp only [State.groupNoticeSupport, State.pendingGroupFailureRefs, roots, pending,
      List.map_nil, List.append_nil, List.not_mem_nil] at active
  · exact groupClosureRefs_subset_completed w.events completed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
