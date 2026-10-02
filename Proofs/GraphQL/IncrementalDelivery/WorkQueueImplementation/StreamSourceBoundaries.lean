import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureCutAlignment
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceItemPrefixes

/-! Stream atoms retain their actual source handler and its earlier object-failure ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A stream action identifies its own handler, even after normalization and atomization
-----------------------------------------------------------------------------------------

/-- An atomic stream action emitted by one handler is the input's own stream action.
Witness: atomization preserves the action, normalization preserves raw actions, and the
handler emits only a subsequence of its input's singleton action. No source law is needed.
-/
theorem State.handleGraphEvent_atomicStreamAction (queue : State)
    (publisher : IncrementalPublisher) (source : GraphEvent)
    {event : Execution.WorkQueueEvent} {action : StreamAction}
    (member
      : event
        ∈ (publisher.normalizeBatch (queue.handleGraphEvent source).2).2.flatMap
            publicationAtoms)
    (reference : streamAction event = some action)
    : source.streamAction = some action := by
  obtain ⟨original, emitted, atom⟩ := List.mem_flatMap.mp member
  have same := publicationAtoms_streamAction_mem
    (List.mem_filterMap.mpr ⟨event, atom, reference⟩)
  have normalized := List.mem_filterMap.mpr ⟨original, emitted, same⟩
  rw [publisher.normalizeBatch_streamActions] at normalized
  have sourceAction := (queue.handleGraphEvent_streamActions source).subset normalized
  simpa only [Option.mem_toList] using sourceAction

/-- A handler block's atomic stream action keeps the matching source label.
Witness: induction through real handler blocks; silent predecessors remain in the list.
-/
theorem State.sourceOutputBlocks_streamAction (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    {block : SourceOutputBlock}
    (member : block ∈ (queue.sourceOutputBlocks publisher received).2.2)
    {event : Execution.WorkQueueEvent} {action : StreamAction} (atom : event ∈ block.2)
    (reference : streamAction event = some action)
    : ∃ source, block.1 = some source ∧ source.streamAction = some action := by
  induction received generalizing queue publisher with
  | nil => cases member
  | cons source rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst block
        exact ⟨source, rfl,
          queue.handleGraphEvent_atomicStreamAction publisher source atom reference⟩
      · exact ih _ _ later

/-- Batch termination cannot provide a stream-action block or obscure its source label.
Witness: actual batch annotations either retain handler blocks or add only termination.
-/
theorem State.sourceBatchBlocks_streamAction (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    {block : SourceOutputBlock}
    (member : block ∈ (queue.sourceBatchBlocks publisher received).2.2)
    {event : Execution.WorkQueueEvent} {action : StreamAction} (atom : event ∈ block.2)
    (reference : streamAction event = some action)
    : ∃ source, block.1 = some source ∧ source.streamAction = some action := by
  simp only [State.sourceBatchBlocks] at member
  split at member
  · cases member
  · split at member
    · rcases List.mem_append.mp member with handler | terminal
      · exact queue.sourceOutputBlocks_streamAction publisher received handler atom reference
      · have same := List.mem_singleton.mp terminal
        subst block
        have same := List.mem_singleton.mp atom
        subst event
        cases reference
    · exact queue.sourceOutputBlocks_streamAction publisher received member atom reference

/-- Every stream-action block in the actual multi-batch run retains its own source input.
Witness: the batch projection above followed through unchanged queue and publisher states.
-/
theorem State.sourceRunBlocks_streamAction (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    {block : SourceOutputBlock}
    (member : block ∈ (queue.sourceRunBlocks publisher batches).2.2)
    {event : Execution.WorkQueueEvent} {action : StreamAction} (atom : event ∈ block.2)
    (reference : streamAction event = some action)
    : ∃ source, block.1 = some source ∧ source.streamAction = some action := by
  induction batches generalizing queue publisher with
  | nil => cases member
  | cons batch rest ih =>
      rcases List.mem_append.mp member with first | later
      · exact queue.sourceBatchBlocks_streamAction publisher batch first atom reference
      · exact ih _ _ later

-----------------------------------------------------------------------------------------
-- Stream outputs see earlier failures, not the current handler's successful items
-----------------------------------------------------------------------------------------

/-- Each actual stream atom has an exact pre-handler source prefix and visible object ledger.
Witness: recover its source-labelled block, then use its non-object-failure action to
remove the current handler from object accounting. Start discipline supplies actual input
acceptance. Multi-item atoms share this prefix, so their safety need not be assumed first.
Exact item counts retain every earlier source item before the selected atom.
-/
theorem createWorkQueue_atomicStream_sourcePrefix {work : Execution.Work}
    {batches : List (List GraphEvent)} (started : inputsStarted work batches = true)
    {index : Nat} {event : Execution.WorkQueueEvent} {action : StreamAction}
    (selected
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    (reference : streamAction event = some action)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let blocks := (queue.sourceRunBlocks publisher batches).2.2
      let objects := sourceObjectFailureCuts 0 (queue.eligibleFailureBlocks blocks)
      ∃ before source after,
        batches.flatten = before ++ source :: after
        ∧ source.streamAction = some action
        ∧ (queue.replayGraphEvents before).acceptsGraphEvent source = true
        ∧ (failedBefore objects index).reverse = queue.objectFailureContributions before
        ∧ (before.flatMap GraphEvent.itemPublications).length
          ≤ ((((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                index).flatMap
              normalizedItemValues).length := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨earlier, block, later, localIndex, split, position, atLocal, prior, _⟩ :=
    createWorkQueue_atomicOutput_sourcePrefix started selected
  have member : block ∈ (queue.sourceRunBlocks publisher batches).2.2 := by
    rw [split]
    simp
  obtain ⟨source, label, sameAction⟩ := queue.sourceRunBlocks_streamAction publisher batches
    member (List.mem_of_getElem? atLocal) reference
  have labels := queue.sourceRunBlocks_inputs_of_started publisher
    (by rwa [← inputsStarted_eq_batchesStarted])
  rw [split] at labels
  have sourceSplit : batches.flatten = earlier.filterMap Prod.fst ++ source ::
      later.filterMap Prod.fst := by
    simpa only [List.filterMap_append, List.filterMap_cons, label] using labels.symm
  refine ⟨earlier.filterMap Prod.fst, source, later.filterMap Prod.fst, sourceSplit,
    sameAction, ?_, ?_, ?_⟩
  · apply inputsStarted_eachAccepted work batches started
    simpa only [label, Option.toList_some] using prior
  · rw [split, position]
    have visible := queue.eligibleObjectFailureCuts_visible_before 0 earlier later block
      localIndex (List.getElem?_eq_some_iff.mp atLocal).1
    simp only [Nat.zero_add] at visible
    apply visible
    intro other same
    have equal := Option.some.inj (same.symm.trans label)
    subst other
    cases source <;> simp_all [GraphEvent.streamAction, GraphEvent.objectFailure?]
  · have counted := sourceBlocks_earlierItemCount
      (queue.sourceRunBlocks_itemValues publisher batches
        (by rwa [← inputsStarted_eq_batchesStarted])) split position
    rwa [(queue.sourceRunBlocks_agrees batches).2] at counted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
