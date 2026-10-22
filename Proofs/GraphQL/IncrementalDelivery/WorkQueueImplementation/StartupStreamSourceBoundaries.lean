import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamSourceBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupOutputCuts

/-! Startup stream actions preserve exact source boundaries and earlier item counts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every actual startup stream atom retains its source, strict source prefix and exact
later object-reporting availability. Queued group controls have no stream action or item; their actual dispatch
labels remain in the source trace.
-/
theorem startup_atomicStream_sourcePrefix {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    {index : Nat} {event : Execution.WorkQueueEvent} {action : StreamAction}
    (selected
      : let initial := State.initialize (Work.fromExecution work) startup
        ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
        = some event)
    (reference : streamAction event = some action)
    : let initial := State.initialize (Work.fromExecution work) startup
      let queue := initial
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
  let initial := State.initialize (Work.fromExecution work) startup
  let queue := initial
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  have annotated :
      ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)[index]?
      = some event := by rwa [(queue.sourceRunBlocks_agrees batches).2]
  obtain ⟨earlier, block, later, localIndex, split, position, atLocal⟩ :=
    sourceOutputBlocks_at annotated
  have member : block ∈ (queue.sourceRunBlocks publisher batches).2.2 := by
    rw [split]
    simp
  obtain ⟨source, label, sameAction⟩ := queue.sourceRunBlocks_streamAction publisher batches member (List.mem_of_getElem? atLocal) reference
  have labels := queue.sourceRunBlocks_inputs_of_started publisher (by rwa [← inputsStartedWithStartup_eq_batchesStarted])
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
      (by rwa [← inputsStartedWithStartup_eq_batchesStarted]) atBlock label
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
        (by rwa [← inputsStartedWithStartup_eq_batchesStarted])) split position
    rwa [(queue.sourceRunBlocks_agrees batches).2] at counted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
