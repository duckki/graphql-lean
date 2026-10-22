import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureCutAlignment

/-! Keep source-handler boundaries within one snapshot and retain actual host batch cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Handler blocks compose only under the same cache snapshot
-----------------------------------------------------------------------------------------

/-- Sequential source annotation composes through the actual queue and publisher states.
Witness: induction through the first source list; even silent handlers retain a block.
-/
theorem State.sourceOutputBlocks_append (queue : State) (publisher : IncrementalPublisher)
    (before after : List GraphEvent) (available : List (Occurrence × Nat) := [])
    : queue.sourceOutputBlocks publisher (before ++ after) available
      = let first := queue.sourceOutputBlocks publisher before available
        let last := first.1.sourceOutputBlocks first.2.1 after available
        (last.1, last.2.1, first.2.2 ++ last.2.2) := by
  induction before generalizing queue publisher with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.cons_append, State.sourceOutputBlocks, ih, List.cons_append]

-----------------------------------------------------------------------------------------
-- A selected block keeps its actual source label and pre-handler queue
-----------------------------------------------------------------------------------------

/-- Splitting handler annotations recovers that same handler, with every silent predecessor.
Witness: recurse on the block prefix rather than search by payload. The existential
publisher is the actual intermediate publisher; no equality of response values is used.
-/
theorem State.sourceOutputBlocks_handler (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent) {before block after}
    (available : List (Occurrence × Nat) := [])
    (split
      : (queue.sourceOutputBlocks publisher received available).2.2
        = before ++ block :: after)
    : ∃ source,
      ∃ currentPublisher : IncrementalPublisher,
        block.1 = some source
        ∧ block.2
          = (currentPublisher.normalizeBatch
              (((queue.replayGraphEvents (before.filterMap Prod.fst)
                  available).handleGraphEvent
                  source available).2.1)).2.flatMap
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
    (available : List (Occurrence × Nat) := [])
    (initialPart
      : before.IsPrefix (queue.sourceOutputBlocks publisher received available).2.2)
    : (queue.sourceOutputBlocks publisher (before.filterMap Prod.fst) available).2.2
      = before := by
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
              (((queue.dispatchGraphEvent source available).1.sourceOutputBlocks
                (publisher.normalizeBatch (queue.dispatchGraphEvent source available).2).1
                rest available).2.2) :=
            ⟨suffix, tailShape⟩
          simpa only [List.filterMap_cons, State.sourceOutputBlocks]
            using congrArg
              (fun blocks =>
                (
                  some source,
                  (publisher.normalizeBatch
                    (queue.dispatchGraphEvent source available).2).2.flatMap
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
              ((queue.replayGraphEvents before).handleGraphEvent source).2.1).2.flatMap
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
                  ((queue.replayGraphEvents before).handleGraphEvent
                    source).2.1).2.flatMap
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
    queue.sourceOutputBlocks_handler publisher received [] split
  have labels := queue.sourceOutputBlocks_inputs publisher received
  rw [split] at labels
  have prefixBlocks := queue.sourceOutputBlocks_prefix publisher received
    (before := earlier) [] ⟨block :: later, split.symm⟩
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

/-- An immediate atomic output retains its exact handler under the supplied snapshot.
The same positional split gives both the earlier atomic prefix and the publisher at
this handler. Queued startup notices are outside this immediate-output view.
-/
theorem State.sourceOutputBlocks_atomicImmediate (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    (available : List (Occurrence × Nat))
    {index : Nat} {event : Execution.WorkQueueEvent}
    (selected
      : ((queue.sourceOutputBlocks publisher received available).2.2.flatMap
          Prod.snd)[index]?
        = some event)
    : ∃ before source after,
      ∃ currentPublisher : IncrementalPublisher,
      ∃ localIndex,
        received = before ++ source :: after
        ∧ ((currentPublisher.normalizeBatch
              ((queue.replayGraphEvents before available).handleGraphEvent source
                available).2.1).2.flatMap
            publicationAtoms)[localIndex]?
          = some event
        ∧ index
          = ((publisher.normalizeBatch
                (queue.rawEventReplay before available).2).2.flatMap
              publicationAtoms).length
            + localIndex
        ∧ ((queue.sourceOutputBlocks publisher received available).2.2.flatMap
            Prod.snd).take
            index
          = (publisher.normalizeBatch (queue.rawEventReplay before available).2).2.flatMap
              publicationAtoms
            ++ ((currentPublisher.normalizeBatch
                  ((queue.replayGraphEvents before available).handleGraphEvent source
                    available).2.1).2.flatMap
                  publicationAtoms).take
                localIndex := by
  obtain ⟨earlier, block, later, localIndex, split, position, atLocal⟩ :=
    sourceOutputBlocks_at selected
  obtain ⟨source, currentPublisher, label, output⟩ :=
    queue.sourceOutputBlocks_handler publisher received available split
  have labels := queue.sourceOutputBlocks_inputs publisher received available
  rw [split] at labels
  have prefixBlocks := queue.sourceOutputBlocks_prefix publisher received available
    (before := earlier) ⟨block :: later, split.symm⟩
  have prefixOutput := (queue.sourceOutputBlocks_agrees publisher
    (earlier.filterMap Prod.fst) available).2.2
  rw [prefixBlocks] at prefixOutput
  refine ⟨earlier.filterMap Prod.fst, source, later.filterMap Prod.fst,
    currentPublisher, localIndex, ?_, ?_, ?_, ?_⟩
  · simpa only [List.filterMap_append, List.filterMap_cons, label] using labels.symm
  · rwa [← output]
  · simpa only [prefixOutput] using position
  · rw [split, List.flatMap_append, List.flatMap_cons, position,
      List.take_length_add_append,
      List.take_append_of_le_length (Nat.le_of_lt (List.getElem?_eq_some_iff.mp atLocal).1),
      prefixOutput, output]

/-- Annotated host batches compose through their actual queue and publisher states. -/
theorem State.sourceRunBlocks_append (queue : State) (publisher : IncrementalPublisher)
    (before after : List (List GraphEvent))
    : queue.sourceRunBlocks publisher (before ++ after)
      = let first := queue.sourceRunBlocks publisher before
        let last := first.1.sourceRunBlocks first.2.1 after
        (last.1, last.2.1, first.2.2 ++ last.2.2) := by
  induction before generalizing queue publisher with
  | nil => rfl
  | cons batch rest ih =>
      simp only [List.cons_append, State.sourceRunBlocks, ih, List.append_assoc]

/-- A labeled FIFO block retains its exact source prefix under the same snapshot.
The preceding annotations equal the trace of that source prefix, including silent steps.
-/
theorem State.sourceOutputBlocks_labeledCut (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    (available : List (Occurrence × Nat))
    {index : Nat} {block : SourceOutputBlock} {source : GraphEvent}
    (selected
      : (queue.sourceOutputBlocks publisher received available).2.2[index]? = some block)
    (labeled : block.1 = some source)
    : ∃ before after,
        received = before ++ source :: after
        ∧ (queue.sourceOutputBlocks publisher received available).2.2.take index
          = (queue.sourceOutputBlocks publisher before available).2.2 := by
  induction received generalizing queue publisher index with
  | nil => cases selected
  | cons event rest ih =>
      cases index with
      | zero =>
          have same : (some event, (publisher.normalizeBatch
              (queue.dispatchGraphEvent event available).2).2.flatMap publicationAtoms) = block :=
            Option.some.inj selected
          have identity : event = source := Option.some.inj ((congrArg Prod.fst same).trans labeled)
          exact ⟨[], rest, by simp only [List.nil_append, identity], rfl⟩
      | succ index =>
          obtain ⟨before, after, same, prior⟩ := ih _ _ selected
          refine ⟨event :: before, after, by simp [same], ?_⟩
          simpa only [State.sourceOutputBlocks, List.take_succ_cons]
            using congrArg
              (List.cons
                (
                  some event,
                  (publisher.normalizeBatch
                    (queue.dispatchGraphEvent event available).2).2.flatMap
                    publicationAtoms
                ))
              prior

/-- A labeled batch block belongs to its snapshot-aware immediate handler annotations.
Internal failure reports retain their source controls; termination has no source label. The exact preceding
block prefix, including silent handlers, therefore agrees with the immediate trace.
-/
theorem State.sourceBatchBlocks_labeledPrefix (queue : State)
    (publisher : IncrementalPublisher) (batch : List GraphEvent)
    {index : Nat} {block : SourceOutputBlock} {source : GraphEvent}
    (selected : (queue.sourceBatchBlocks publisher batch).2.2[index]? = some block)
    (labeled : block.1 = some source)
    : let traced :=
        queue.sourceOutputBlocks publisher batch (GraphEvent.availableFailures batch)
      traced.2.2[index]? = some block
      ∧ (queue.sourceBatchBlocks publisher batch).2.2.take index
        = traced.2.2.take index := by
  let traced := queue.sourceOutputBlocks publisher batch (GraphEvent.availableFailures batch)
  have lift (controls : List SourceOutputBlock)
      (silent : ∀ control ∈ controls, control.1 = none)
      (atBlock : (traced.2.2 ++ controls)[index]? = some block)
      : traced.2.2[index]? = some block
        ∧ (traced.2.2 ++ controls).take index = traced.2.2.take index := by
    by_cases inside : index < traced.2.2.length
    · exact ⟨by rwa [List.getElem?_append_left inside] at atBlock,
        List.take_append_of_le_length (Nat.le_of_lt inside)⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at atBlock
      have empty := silent block (List.mem_of_getElem? atBlock)
      rw [labeled] at empty
      cases empty
  cases running : queue.terminated with
  | true => simp [State.sourceBatchBlocks, running] at selected
  | false =>
      have shape : ∃ controls : List SourceOutputBlock,
          (∀ control ∈ controls, control.1 = none)
          ∧ (queue.sourceBatchBlocks publisher batch).2.2 = traced.2.2 ++ controls := by
        simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ite_false]
        split
        · refine ⟨[(none, [.workQueueTermination])], ?_, rfl⟩
          intro control member
          cases List.mem_singleton.mp member
          rfl
        · refine ⟨[], ?_, ?_⟩
          · intro control member; cases member
          · simp only [List.append_nil]; rfl
      obtain ⟨controls, silent, same⟩ := shape
      rw [same] at selected ⊢
      exact lift controls silent selected

/-- A block position retains its actual batch cut, including silent handler blocks.
Unlike atomic indexing, block indexing also locates failures with no immediate output.
The complete earlier block prefix is preserved, including internal failure controls.
-/
theorem State.sourceRunBlocks_blockCut (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    {index : Nat} {block : SourceOutputBlock}
    (selected : (queue.sourceRunBlocks publisher batches).2.2[index]? = some block)
    : ∃ earlier batch later localIndex,
        batches = earlier ++ batch :: later
        ∧ let first := queue.sourceRunBlocks publisher earlier
          let current := first.1.sourceBatchBlocks first.2.1 batch
          current.2.2[localIndex]? = some block
          ∧ (queue.sourceRunBlocks publisher batches).2.2.take index
            = first.2.2 ++ current.2.2.take localIndex := by
  induction batches generalizing queue publisher index with
  | nil => simp [State.sourceRunBlocks] at selected
  | cons batch rest ih =>
      let first := queue.sourceBatchBlocks publisher batch
      have atOutput : (first.2.2
          ++ (first.1.sourceRunBlocks first.2.1 rest).2.2)[index]? = some block := selected
      by_cases inside : index < first.2.2.length
      · refine ⟨[], batch, rest, index, rfl, ?_, ?_⟩
        · rwa [List.getElem?_append_left inside] at atOutput
        · change (first.2.2 ++ _).take index = [] ++ first.2.2.take index
          simpa only [List.nil_append]
            using List.take_append_of_le_length (Nat.le_of_lt inside)
      · have bound : first.2.2.length ≤ index := Nat.le_of_not_gt inside
        rw [List.getElem?_append_right bound] at atOutput
        obtain ⟨earlier, current, later, localIndex, same, localAt, beforeEq⟩ := ih _ _ atOutput
        refine ⟨batch :: earlier, current, later, localIndex, by simp [same], localAt, ?_⟩
        change (first.2.2 ++ _).take index =
          (first.2.2 ++ (first.1.sourceRunBlocks first.2.1 earlier).2.2) ++ _
        have indexEq : index = first.2.2.length + (index - first.2.2.length) := by omega
        rw [indexEq, List.take_length_add_append, beforeEq, List.append_assoc]
        rfl

/-- Every atomic output retains its actual host batch and local atomic position.
The selected batch is replayed with its own full availability snapshot. Its output may
come from an immediate handler, deferred startup forwarding or the terminal marker.
-/
theorem State.sourceRunBlocks_atomicBatch (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    {index : Nat} {event : Execution.WorkQueueEvent}
    (selected
      : ((queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)[index]?
        = some event)
    : ∃ earlier batch later localIndex,
        batches = earlier ++ batch :: later
        ∧ let first := queue.sourceRunBlocks publisher earlier
          let current := queue.replayBatches earlier
          (((current.sourceBatchBlocks first.2.1 batch).2.2.flatMap Prod.snd)[localIndex]?
            = some event)
          ∧ index = (first.2.2.flatMap Prod.snd).length + localIndex := by
  induction batches generalizing queue publisher index with
  | nil => simp [State.sourceRunBlocks] at selected
  | cons batch rest ih =>
      let first := queue.sourceBatchBlocks publisher batch
      have atOutput : (first.2.2.flatMap Prod.snd
          ++ (first.1.sourceRunBlocks first.2.1 rest).2.2.flatMap Prod.snd)[index]?
            = some event := by
        simpa only [State.sourceRunBlocks, List.flatMap_append] using selected
      by_cases inside : index < (first.2.2.flatMap Prod.snd).length
      · refine ⟨[], batch, rest, index, rfl, ?_, by simp [State.sourceRunBlocks]⟩
        rwa [List.getElem?_append_left inside] at atOutput
      · have bound : (first.2.2.flatMap Prod.snd).length ≤ index := Nat.le_of_not_gt inside
        rw [List.getElem?_append_right bound] at atOutput
        obtain ⟨earlier, current, later, localIndex, same, localAt, position⟩ := ih _ _ atOutput
        refine ⟨batch :: earlier, current, later, localIndex, by simp [same], ?_, ?_⟩
        · have states := (queue.sourceBatchBlocks_agrees publisher batch).1
          dsimp only [first] at localAt
          simpa only [State.sourceRunBlocks, State.replayBatches, List.foldl_cons,
            ← states]
            using localAt
        · simp only [State.sourceRunBlocks, List.flatMap_append, List.length_append]
          dsimp only [first] at bound position
          omega

/-- A labeled block retains the exact earlier host batches and current FIFO input prefix.
Silent handlers remain in the source prefix, while unlabeled forwarding blocks do not
introduce inputs. No flattening of runtime state is used. -/
theorem State.sourceRunBlocks_labeledInputCut (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true)
    {index : Nat} {block : SourceOutputBlock} {source : GraphEvent}
    (selected : (queue.sourceRunBlocks publisher batches).2.2[index]? = some block)
    (labeled : block.1 = some source)
    : ∃ earlier batch later fifo tail,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ source :: tail
        ∧ ((queue.sourceRunBlocks publisher batches).2.2.take index).filterMap Prod.fst
          = earlier.flatten ++ fifo := by
  obtain ⟨earlier, batch, later, localIndex, split, atBatch, beforeBlocks⟩ :=
    queue.sourceRunBlocks_blockCut publisher batches selected
  let first := queue.sourceRunBlocks publisher earlier
  have inTrace := first.1.sourceBatchBlocks_labeledPrefix first.2.1 batch atBatch labeled
  obtain ⟨fifo, tail, batchEq, beforeTrace⟩ := first.1.sourceOutputBlocks_labeledCut
    first.2.1 batch (GraphEvent.availableFailures batch) inTrace.1 labeled
  have priorStarted : queue.batchesStarted earlier = true := by
    have all := split ▸ started
    rw [State.batchesStarted_append, Bool.and_eq_true] at all
    exact all.1
  refine ⟨earlier, batch, later, fifo, tail, split, batchEq, ?_⟩
  rw [beforeBlocks, inTrace.2, beforeTrace, List.filterMap_append,
    queue.sourceRunBlocks_inputs_of_started publisher priorStarted,
    State.sourceOutputBlocks_inputs _ _ _ (GraphEvent.availableFailures batch)]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
