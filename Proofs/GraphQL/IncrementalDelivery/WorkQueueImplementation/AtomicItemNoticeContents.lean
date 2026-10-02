import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticePublicationExclusion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCarrierNoticeContents

/-! Item-carried group notices have actual retained contents on the canonical matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Raw integration boundaries survive batching, normalization, and final-item atomization
-----------------------------------------------------------------------------------------

/-- Every actual item-carried group notice retains only unpublished task memberships.
Witness: recover its source input and exact item-integration boundary through the real
publisher/atomization pipeline. The canonical ledger supplies earlier-publication
exclusion; replay derives task metadata and the reverse ledger bridge gives nonpublication.
No caller supplies a source index, count equation, retained node, or notice admission.
-/
theorem itemGroupNotice_unpublished
    {work inputs w index owner values groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups)
    : ∃ before stream items after earlier item later,
        inputs.flatten = before ++ .streamItems stream items :: after
        ∧ items = earlier ++ item :: later
        ∧ let current := (initialQueue work).replayGraphEvents before
          let boundary := (current.preparedStreamItems earlier).integrateStreamItem item
          current.rootStreams.contains stream.key = true
          ∧ (∃ dependencies producer, NodeAt work child .group dependencies producer)
          ∧ ∃ node,
              boundary.groupNode? child.key = some node
              ∧ node.group.node = child
              ∧ (node.tasks ≠ [] ∨ node.failure.isSome = true)
              ∧ ∀ occurrence ∈ node.tasks,
                  ¬Published w.matching (w.events.take index) occurrence := by
  obtain ⟨before, stream, items, after, sourceShape, active, notices, count⟩ :=
    Witness.itemNotice_sourceBoundary started history selected (List.mem_append_left _ noticed)
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  rw [sourceShape] at covered
  have source : ValidGraphEvents work (before ++ .streamItems stream items :: after) :=
    sourceShape ▸ valid
  obtain ⟨earlier, item, later, splitItems, located, node, found, same,
      contents, _, unpublished⟩ :=
    generated.streamItems_leadingNotice_unpublished covered source matching objects ready count
      (notices ▸ noticed)
  exact ⟨before, stream, items, after, earlier, item, later, sourceShape, splitItems,
    active, located, node, found, same, contents, unpublished⟩

/-- An item-carried group notice retains unpublished tasks and cut-supported errors together.
Witness: recover the actual handler and its cache support from one atomic boundary.
Invert its leading item carrier, then preserve that support to the exact introducing
item while the common publication ledger excludes its retained task memberships.
-/
theorem itemGroupNotice_contents
    {work inputs w index owner values groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    {streamCuts : FailureCuts}
    (partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streamCuts
            ++ sourceObjectFailureCuts 0
                (queue.eligibleFailureBlocks
                  (queue.sourceRunBlocks publisher inputs).2.2)))
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child := by
  obtain ⟨before, event, after, publisher, localIndex, sourceShape, emitted, count, cached⟩ :=
    Witness.handlerBoundary_cachedFailures generated valid started history partition selected
  obtain ⟨normalizedIndex, normalizedValues, normalizedAt, atomicCount, _⟩ :=
    publicationAtoms_noticeCarrier_prefix _ emitted (List.mem_append_left _ noticed)
  obtain ⟨rawIndex, rawValues, rawAt, rawCount, _⟩ :=
    publisher.normalizeBatch_streamCarrier_prefix _ normalizedAt
  obtain ⟨stream, items, rfl⟩ :=
    ((initialQueue work).replayGraphEvents before).handleGraphEvent_streamValues_source event rawAt
  obtain ⟨_, zero, groupEq⟩ :=
    ((initialQueue work).replayGraphEvents before).streamItems_noticeGroups stream items rawAt
  have objectCount
      : ((w.events.take index).flatMap normalizedObjectValues).length
        = (((initialQueue work).rawEventReplay before).2.flatMap
            WorkQueueEvent.objectValues).length := by
    simpa only [atomicCount, rawCount, zero, List.take_zero, List.flatMap_nil,
      List.length_nil, Nat.add_zero]
      using count
  obtain ⟨published, batches, matching, _⟩ := ledger
  have covered := batches.flatten (by rwa [← inputsStarted_eq_batchesStarted])
  rw [sourceShape] at covered
  have source : ValidGraphEvents work (before ++ .streamItems stream items :: after) :=
    sourceShape ▸ valid
  obtain ⟨earlier, item, later, splitItems, located, node, found, same,
    contents, _, unpublished⟩ :=
    generated.streamItems_leadingNotice_unpublished covered source matching objects ready
      objectCount (groupEq ▸ noticed)
  have prior := source.prefix (List.prefix_append before (.streamItems stream items :: after))
  obtain ⟨eventMatching, _, _⟩ := source.atPrefix (show
    (before ++ [GraphEvent.streamItems stream items]).IsPrefix
      (before ++ GraphEvent.streamItems stream items :: after) from ⟨after, by simp⟩)
  obtain ⟨sound, registered⟩ := State.replay_noticeTaskProvenance
    (createWorkQueue_groupMembershipSound _) (createWorkQueue_fromSpec_registeredTasksMatch work)
    before (fun _ member => prior.eachMatches member)
  have included : earlier.Subset items := by
    rw [splitItems]
    exact List.subset_append_left _ _
  obtain ⟨preparedSound, preparedRegistered⟩ :=
    State.preparedStreamItems_noticeTaskProvenance sound registered eventMatching earlier included
  obtain ⟨boundarySound, boundaryRegistered⟩ :=
    State.integrateStreamItem_noticeTaskProvenance (item := item)
      preparedSound preparedRegistered eventMatching (by simp [splitItems])
  have sourceReady := (createWorkQueue_replayGraphEvents_producerOrder prior).1.mono
    (show before.Subset inputs.flatten from sourceShape ▸ List.subset_append_left _ _)
  have input : GraphEvent.streamItems stream items ∈ inputs.flatten := by
    rw [sourceShape]
    exact List.mem_append_right _ List.mem_cons_self
  exact ⟨
    located,
    _,
    node,
    found,
    same,
    contents,
    boundarySound,
    boundaryRegistered,
    (cached.preparedStreamItems earlier).integrateStreamItem item,
    (sourceReady.preparedStreamItems eventMatching input earlier
      included).integrateStreamItem
      eventMatching input (by simp [splitItems]),
    unpublished
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
