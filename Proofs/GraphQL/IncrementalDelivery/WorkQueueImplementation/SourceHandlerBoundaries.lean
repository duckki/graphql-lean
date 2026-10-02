import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureCutAlignment

/-! Keep exact source-handler boundaries while flattening accepted host batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Flattening preserves individual handler blocks, not just the output concatenation
-----------------------------------------------------------------------------------------

/-- Sequential source annotation composes through the actual queue and publisher states.
Witness: induction through the first source list; even silent handlers retain a block.
-/
theorem State.sourceOutputBlocks_append (queue : State) (publisher : IncrementalPublisher)
    (before after : List GraphEvent)
    : queue.sourceOutputBlocks publisher (before ++ after)
      = let first := queue.sourceOutputBlocks publisher before
        let last := first.1.sourceOutputBlocks first.2.1 after
        (last.1, last.2.1, first.2.2 ++ last.2.2) := by
  induction before generalizing queue publisher with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.cons_append, State.sourceOutputBlocks, ih, List.cons_append]

/-- Started host batches preserve every sequential handler block, then optional termination.
Witness: a later started batch rules out earlier termination. Concatenate the actual
annotated states; the last batch can append only its source-free terminal block.
-/
theorem State.sourceRunBlocks_handlerBlocks (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true)
    : ∃ terminal : Bool,
        (queue.sourceRunBlocks publisher batches).2.2
        = (queue.sourceOutputBlocks publisher batches.flatten).2.2
          ++ if terminal then [(none, [.workQueueTermination])] else [] := by
  induction batches generalizing queue publisher with
  | nil => exact ⟨false, rfl⟩
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have ⟨state, mapper, _⟩ := queue.sourceBatchBlocks_agrees publisher batch
      cases rest with
      | nil =>
          simp only [State.sourceRunBlocks, List.append_nil, List.flatten_cons,
            List.flatten_nil, State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
          split
          · exact ⟨true, rfl⟩
          · exact ⟨false, by simp⟩
      | cons next tail =>
          have openNext := ((queue.handleGraphEvents batch).1.batchesStarted_cons
            next tail later).1
          have raw := queue.handleGraphEvents_nonterminal batch running openNext
          have exactState := (queue.sourceOutputBlocks_agrees publisher batch).1
          have exactPublisher := (queue.sourceOutputBlocks_agrees publisher batch).2.1
          have blocks : (queue.sourceBatchBlocks publisher batch).2.2
              = (queue.sourceOutputBlocks publisher batch).2.2 := by
            unfold State.sourceBatchBlocks
            simp only [running, Bool.false_eq_true, ↓reduceIte]
            split
            · rename_i empty
              have finalState := (queue.sourceBatchBlocks_agrees publisher batch).1
              simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte,
                empty] at finalState
              have contradiction := congrArg State.terminated finalState
              rw [openNext] at contradiction
              cases contradiction
            · rfl
          obtain ⟨terminal, remaining⟩ := ih (queue.sourceBatchBlocks publisher batch).1
            (queue.sourceBatchBlocks publisher batch).2.1 (by rwa [state])
          refine ⟨terminal, ?_⟩
          rw [State.sourceRunBlocks, remaining, blocks]
          rw [state, mapper, raw, ← exactState, ← exactPublisher]
          simp only [List.flatten_cons, State.sourceOutputBlocks_append, List.append_assoc]

-----------------------------------------------------------------------------------------
-- A selected block keeps its actual source label and pre-handler queue
-----------------------------------------------------------------------------------------

/-- Splitting handler annotations recovers that same handler, with every silent predecessor.
Witness: recurse on the block prefix rather than search by payload. The existential
publisher is the actual intermediate publisher; no equality of response values is used.
-/
theorem State.sourceOutputBlocks_handler (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent) {before block after}
    (split : (queue.sourceOutputBlocks publisher received).2.2 = before ++ block :: after)
    : ∃ source,
      ∃ currentPublisher : IncrementalPublisher,
        block.1 = some source
        ∧ block.2
          = (currentPublisher.normalizeBatch
              (((queue.replayGraphEvents (before.filterMap Prod.fst)).handleGraphEvent
                  source).2)).2.flatMap
              publicationAtoms := by
  induction received generalizing queue publisher before with
  | nil => simp [State.sourceOutputBlocks] at split
  | cons source rest ih =>
      cases before with
      | nil =>
          have same := (List.cons.inj split).1
          subst block
          exact ⟨source, publisher, rfl, rfl⟩
      | cons head earlier =>
          obtain ⟨rfl, tailSplit⟩ := List.cons.inj split
          obtain ⟨event, currentPublisher, label, output⟩ := ih _ _ tailSplit
          exact ⟨event, currentPublisher, label, output⟩

/-- A retained block prefix is exactly the annotation of its source-label prefix.
Witness: induction through the actual source handlers, including zero-output blocks.
-/
theorem State.sourceOutputBlocks_prefix (queue : State) (publisher : IncrementalPublisher)
    (received : List GraphEvent) {before : List SourceOutputBlock}
    (initialPart : before.IsPrefix (queue.sourceOutputBlocks publisher received).2.2)
    : (queue.sourceOutputBlocks publisher (before.filterMap Prod.fst)).2.2 = before := by
  induction received generalizing queue publisher before with
  | nil =>
      have empty : before = [] := List.prefix_nil.mp initialPart
      subst before
      rfl
  | cons source rest ih =>
      cases before with
      | nil => rfl
      | cons block earlier =>
          obtain ⟨suffix, shape⟩ := initialPart
          obtain ⟨rfl, tailShape⟩ := List.cons.inj shape
          have tailPrefix : earlier.IsPrefix
              (((queue.handleGraphEvent source).1.sourceOutputBlocks
                (publisher.normalizeBatch (queue.handleGraphEvent source).2).1 rest).2.2) :=
            ⟨suffix, tailShape⟩
          simpa only [List.filterMap_cons, State.sourceOutputBlocks]
            using congrArg
              (fun blocks =>
                (
                  some source,
                  (publisher.normalizeBatch (queue.handleGraphEvent source).2).2.flatMap
                    publicationAtoms
                )
                :: blocks)
              (ih _ _ tailPrefix)

/-- Each annotated atom retains one actual handler and its exact visible failure inventory.
Witness: split by output position, retain all earlier source labels, and recover the
actual handler block. The position and failure equality use that same split, avoiding
independent searches for equal output payloads.
-/
theorem State.sourceOutputBlocks_atomicHandler (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    {index : Nat} {event : Execution.WorkQueueEvent}
    (selected
      : ((queue.sourceOutputBlocks publisher received).2.2.flatMap Prod.snd)[index]?
        = some event)
    : ∃ before source after,
      ∃ currentPublisher : IncrementalPublisher,
      ∃ localIndex,
        received = before ++ source :: after
        ∧ ((currentPublisher.normalizeBatch
              ((queue.replayGraphEvents before).handleGraphEvent source).2).2.flatMap
            publicationAtoms)[localIndex]?
          = some event
        ∧ index
          = ((publisher.normalizeBatch (queue.rawEventReplay before).2).2.flatMap
              publicationAtoms).length
            + localIndex
        ∧ ((queue.sourceOutputBlocks publisher received).2.2.flatMap Prod.snd).take index
          = (publisher.normalizeBatch (queue.rawEventReplay before).2).2.flatMap
              publicationAtoms
            ++ ((currentPublisher.normalizeBatch
                  ((queue.replayGraphEvents before).handleGraphEvent source).2).2.flatMap
                  publicationAtoms).take
                localIndex
        ∧ (failedBefore
            (sourceObjectFailureCuts 0
              (queue.eligibleFailureBlocks
                (queue.sourceOutputBlocks publisher received).2.2))
            index).reverse
          = queue.objectFailureContributions (before ++ [source]) := by
  obtain ⟨earlier, block, later, localIndex, split, position, atLocal⟩ :=
    sourceOutputBlocks_at selected
  obtain ⟨source, currentPublisher, label, output⟩ :=
    queue.sourceOutputBlocks_handler publisher received split
  have labels := queue.sourceOutputBlocks_inputs publisher received
  rw [split] at labels
  have prefixBlocks := queue.sourceOutputBlocks_prefix publisher received
    (before := earlier) ⟨block :: later, split.symm⟩
  have prefixOutput := (queue.sourceOutputBlocks_agrees publisher
    (earlier.filterMap Prod.fst)).2.2
  rw [prefixBlocks] at prefixOutput
  refine ⟨earlier.filterMap Prod.fst, source, later.filterMap Prod.fst,
    currentPublisher, localIndex, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.filterMap_append, List.filterMap_cons, label] using labels.symm
  · rwa [← output]
  · simpa only [prefixOutput] using position
  · rw [split, List.flatMap_append, List.flatMap_cons, position,
      List.take_length_add_append,
      List.take_append_of_le_length (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atLocal).1),
      prefixOutput, output]
  · rw [split, position]
    have visible := queue.eligibleObjectFailureCuts_visible 0 earlier later block localIndex
      (List.getElem?_eq_some_iff.mp atLocal).1
    simpa only [Nat.zero_add, label, Option.toList_some] using visible

/-- Flattening accepted batches preserves the exact selected object-failure cut list.
Witness: retained handler blocks are identical; the optional terminal block contributes
no failure. Equal-cut silent settlements keep their original order and guard decisions.
-/
theorem State.sourceRunBlocks_objectCuts (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true)
    : sourceObjectFailureCuts 0
        (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
      = sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks
            (queue.sourceOutputBlocks publisher batches.flatten).2.2) := by
  obtain ⟨terminal, blocks⟩ := queue.sourceRunBlocks_handlerBlocks publisher batches started
  rw [blocks, queue.eligibleFailureBlocks_append, sourceObjectFailureCuts_append]
  cases terminal <;> simp [State.eligibleFailureBlocks, sourceObjectFailureCuts]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
