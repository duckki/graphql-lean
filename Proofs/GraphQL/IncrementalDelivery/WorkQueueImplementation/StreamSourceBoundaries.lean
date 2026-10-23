import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceHandlerBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceItemPrefixes

/-! Stream atoms retain their source label and earlier reporting availability. -/

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
    (available : List (Occurrence × Nat) := [])
    (member
      : event
        ∈ (publisher.normalizeBatch
            (queue.handleGraphEvent source available).2.1).2.flatMap
            publicationAtoms)
    (reference : streamAction event = some action)
    : source.streamAction = some action := by
  obtain ⟨original, emitted, atom⟩ := List.mem_flatMap.mp member
  have same := publicationAtoms_streamAction_mem
    (List.mem_filterMap.mpr ⟨event, atom, reference⟩)
  have normalized := List.mem_filterMap.mpr ⟨original, emitted, same⟩
  rw [publisher.normalizeBatch_streamActions] at normalized
  have sourceAction := (queue.handleGraphEvent_streamActions source available).subset normalized
  simpa only [Option.mem_toList] using sourceAction

/-- A handler block's atomic stream action keeps the matching source label.
Witness: induction through real handler blocks; silent predecessors remain in the list.
-/
theorem State.sourceOutputBlocks_streamAction (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    {block : SourceOutputBlock} (available : List (Occurrence × Nat) := [])
    (member : block ∈ (queue.sourceOutputBlocks publisher received available).2.2)
    {event : Execution.WorkQueueEvent} {action : StreamAction} (atom : event ∈ block.2)
    (reference : streamAction event = some action)
    : ∃ source, block.1 = some source ∧ source.streamAction = some action := by
  induction received generalizing queue publisher with
  | nil => cases member
  | cons source rest ih =>
      rcases List.mem_cons.mp member with same | later
      · subst block
        exact ⟨source, rfl,
          queue.handleGraphEvent_atomicStreamAction publisher source available atom reference⟩
      · exact ih _ _ later

/-- Every stream-action block retains its source; termination has no stream action. -/
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
    · rcases List.mem_append.mp member with ordinary | terminal
      · exact queue.sourceOutputBlocks_streamAction publisher received _ ordinary atom reference
      · cases List.mem_singleton.mp terminal
        cases List.mem_singleton.mp atom
        cases reference
    · exact queue.sourceOutputBlocks_streamAction publisher received _ member atom reference

/-- Stream actions retain their source labels across actual host-batch boundaries. -/
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

/-- Each actual stream atom has an exact source prefix and visible reporting inventory.
Witness: recover its source-labelled block, then use its non-object-failure action to
remove the current stream handler from object availability. Start discipline retains all
source labels. Multi-item atoms share this prefix, independently of causal cut licensing.
Exact item counts retain every earlier source item before the selected atom.
-/
theorem createWorkQueue_atomicStream_sourcePrefix {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
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
      let objects := sourceObjectFailureCuts 0 blocks
      ∃ before source after,
        batches.flatten = before ++ source :: after
        ∧ source.streamAction = some action
        ∧ (∃ earlier batch later fifo tail,
            batches = earlier ++ batch :: later
            ∧ batch = fifo ++ source :: tail
            ∧ before = earlier.flatten ++ fifo)
        ∧ (failedBefore objects index).reverse = GraphEvent.failureSettlements before
        ∧ (before.flatMap GraphEvent.itemPublications).length
          ≤ ((((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                index).flatMap
              normalizedItemValues).length := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have annotated : ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)[index]?
      = some event := by rwa [(queue.sourceRunBlocks_agrees batches).2]
  obtain ⟨earlier, block, later, localIndex, split, position, atLocal⟩ :=
    sourceOutputBlocks_at annotated
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
  · have atBlock : (queue.sourceRunBlocks publisher batches).2.2[earlier.length]?
        = some block := by rw [split]; simp
    obtain ⟨prior, batch, following, fifo, tail, inputEq, batchEq, beforeEq⟩ :=
      queue.sourceRunBlocks_labeledInputCut publisher batches
        (by rwa [← inputsStarted_eq_batchesStarted]) atBlock label
    refine ⟨prior, batch, following, fifo, tail, inputEq, batchEq, ?_⟩
    simpa only [split, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      using beforeEq
  · rw [split, position]
    have visible := sourceObjectFailureCuts_visible 0 earlier later block localIndex
      (List.getElem?_eq_some_iff.mp atLocal).1
    simp only [Nat.zero_add] at visible
    rw [visible, sourceObjectFailureCuts_occurrences,
      GraphEvent.failureSettlements_eq_objectFailures_reverse]
    have nonfailure : source.objectFailure? = none := by
      cases source <;> simp_all [GraphEvent.streamAction, GraphEvent.objectFailure?]
    simp only [label, Option.bind_some, nonfailure, Option.toList_none, List.append_nil]
  · have counted := sourceBlocks_earlierItemCount
      (queue.sourceRunBlocks_itemValues publisher batches (before := []) valid
        (by rwa [← inputsStarted_eq_batchesStarted])) split position
    rwa [(queue.sourceRunBlocks_agrees batches).2] at counted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
