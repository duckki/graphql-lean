import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureSource

/-! Proof-only source-handler boundaries in the exact normalized atomic output. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Normalization can be factored at source-handler boundaries without changing output
-----------------------------------------------------------------------------------------

/-- Normalizing concatenated raw output preserves the intermediate publisher state.
Witness: induction over the first batch using the actual eventwise publisher equation.
-/
theorem IncrementalPublisher.normalizeBatch_append (publisher : IncrementalPublisher)
    (before after : List WorkQueueEvent)
    : publisher.normalizeBatch (before ++ after)
      = let first := publisher.normalizeBatch before
        let last := first.1.normalizeBatch after
        (last.1, first.2 ++ last.2) := by
  induction before generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      simp only [List.cons_append, IncrementalPublisher.normalizeBatch_cons,
        ih, List.append_assoc]

/-- One source event and its exact atomic outputs; none labels batch termination only.
Empty handler output is retained so silent source settlements keep their output boundary.
These are proof annotations, not new executable queue state or source assumptions.
-/
abbrev SourceOutputBlock := Option GraphEvent × List Execution.WorkQueueEvent

/-- An indexed atomic output identifies its handler block and local position.
Witness: subtract earlier block lengths, retaining silent blocks in the preceding list.
-/
theorem sourceOutputBlocks_at {blocks : List SourceOutputBlock} {index event}
    (atEvent : (blocks.flatMap Prod.snd)[index]? = some event)
    : ∃ before block after localIndex,
        blocks = before ++ block :: after
        ∧ index = (before.flatMap Prod.snd).length + localIndex
        ∧ block.2[localIndex]? = some event := by
  induction blocks generalizing index with
  | nil => simp at atEvent
  | cons block rest ih =>
      rw [List.flatMap_cons] at atEvent
      by_cases inside : index < block.2.length
      · exact ⟨[], block, rest, index, rfl, by simp, by
          rwa [List.getElem?_append_left inside] at atEvent⟩
      · have after : block.2.length ≤ index := Nat.le_of_not_gt inside
        rw [List.getElem?_append_right after] at atEvent
        obtain ⟨earlier, current, later, localIndex, same, position, atLocal⟩ := ih atEvent
        refine ⟨block :: earlier, current, later, localIndex, ?_, ?_, atLocal⟩
        · simp [same]
        · simp only [List.flatMap_cons, List.length_append]
          omega

/-- Replay the existing handlers and publisher, retaining each handler's atomic segment.
This proof-only view does not choose inputs, change batching, or license any failure cut.
-/
def State.sourceOutputBlocks (queue : State) (publisher : IncrementalPublisher)
    : List GraphEvent → State × IncrementalPublisher × List SourceOutputBlock
  | [] => (queue, publisher, [])
  | event :: rest =>
      let handled := queue.handleGraphEvent event
      let normalized := publisher.normalizeBatch handled.2
      let later := handled.1.sourceOutputBlocks normalized.1 rest
      (
        later.1,
        later.2.1,
        (some event, normalized.2.flatMap publicationAtoms) :: later.2.2
      )

/-- Source-handler annotations preserve both machines and the exact atomic output.
Witness: concatenate normalization through the same raw replay, including empty segments.
-/
theorem State.sourceOutputBlocks_agrees (queue : State) (publisher : IncrementalPublisher)
    (events : List GraphEvent)
    : let traced := queue.sourceOutputBlocks publisher events
      let raw := queue.rawEventReplay events
      let normalized := publisher.normalizeBatch raw.2
      traced.1 = raw.1
      ∧ traced.2.1 = normalized.1
      ∧ traced.2.2.flatMap Prod.snd = normalized.2.flatMap publicationAtoms := by
  induction events generalizing queue publisher with
  | nil => simp [State.sourceOutputBlocks, State.rawEventReplay,
      IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      dsimp only [State.sourceOutputBlocks]
      rw [State.rawEventReplay_cons, IncrementalPublisher.normalizeBatch_append]
      obtain ⟨state, mapper, output⟩ :=
        ih (queue.handleGraphEvent event).1
          (publisher.normalizeBatch (queue.handleGraphEvent event).2).1
      exact ⟨state, mapper, by simp only [List.flatMap_cons, output, List.flatMap_append]⟩

/-- Handler labels retain exactly the received source sequence, including silent handlers.
Witness: each recursive call contributes its source event once before the continuation.
-/
theorem State.sourceOutputBlocks_inputs (queue : State) (publisher : IncrementalPublisher)
    (events : List GraphEvent)
    : ((queue.sourceOutputBlocks publisher events).2.2.filterMap Prod.fst) = events := by
  induction events generalizing queue publisher with
  | nil => rfl
  | cons event rest ih => simp [State.sourceOutputBlocks, ih]

-----------------------------------------------------------------------------------------
-- The real batch wrapper adds only its optional terminal block
-----------------------------------------------------------------------------------------

/-- Retain handler boundaries through the queue's actual batch termination branches.
The terminal block has no source settlement and therefore cannot create a failure label.
-/
def State.sourceBatchBlocks (queue : State) (publisher : IncrementalPublisher)
    (events : List GraphEvent)
    : State × IncrementalPublisher × List SourceOutputBlock :=
  if queue.terminated then
    (queue, publisher, [])
  else
    let traced := queue.sourceOutputBlocks publisher events
    if traced.1.rootGroups.isEmpty && traced.1.rootStreams.isEmpty then
      (
        { traced.1 with terminated := true },
        traced.2.1,
        traced.2.2 ++ [(none, [.workQueueTermination])]
      )
    else
      traced

/-- Batch annotations reproduce the actual queue, publisher, and complete atomic output.
Witness: handler agreement; normalization leaves the optional terminal constructor intact.
-/
theorem State.sourceBatchBlocks_agrees (queue : State) (publisher : IncrementalPublisher)
    (events : List GraphEvent)
    : let traced := queue.sourceBatchBlocks publisher events
      let raw := queue.handleGraphEvents events
      let normalized := publisher.normalizeBatch raw.2
      traced.1 = raw.1
      ∧ traced.2.1 = normalized.1
      ∧ traced.2.2.flatMap Prod.snd = normalized.2.flatMap publicationAtoms := by
  have ⟨state, mapper, output⟩ := queue.sourceOutputBlocks_agrees publisher events
  simp only [State.sourceBatchBlocks, State.handleGraphEvents_eq_rawEventReplay]
  split
  · simp [IncrementalPublisher.normalizeBatch]
  · rw [state]
    split
    · simp only [IncrementalPublisher.normalizeBatch_append]
      simp [IncrementalPublisher.normalizeBatch, IncrementalPublisher.handleWorkQueueEvent,
        publicationAtoms, List.flatMap_append, mapper, output]
    · exact ⟨state, mapper, output⟩

/-- A batch's retained source labels form a subsequence of its supplied events.
Witness: a terminated queue ignores the batch; otherwise every handler is retained exactly.
-/
theorem State.sourceBatchBlocks_inputs (queue : State) (publisher : IncrementalPublisher)
    (events : List GraphEvent)
    : ((queue.sourceBatchBlocks publisher events).2.2.filterMap Prod.fst).Sublist
        events := by
  simp only [State.sourceBatchBlocks]
  split
  · exact List.nil_sublist _
  · split
    · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        List.append_nil, State.sourceOutputBlocks_inputs]
      exact .refl _
    · rw [State.sourceOutputBlocks_inputs]
      exact .refl _

-----------------------------------------------------------------------------------------
-- Source blocks retain the actual multi-batch runner, not a rebatched execution
-----------------------------------------------------------------------------------------

/-- Annotate existing input batches with source-handler boundaries and terminal blocks.
Only the proof view is flattened: queue termination still occurs at the supplied boundaries.
-/
def State.sourceRunBlocks (queue : State) (publisher : IncrementalPublisher)
    : List (List GraphEvent) → State × IncrementalPublisher × List SourceOutputBlock
  | [] => (queue, publisher, [])
  | batch :: rest =>
      let first := queue.sourceBatchBlocks publisher batch
      let later := first.1.sourceRunBlocks first.2.1 rest
      (later.1, later.2.1, first.2.2 ++ later.2.2)

/-- The normalized fold's publisher is the publisher after its actual raw batch.
Witness: the empty-batch branch agrees with normalization of an empty list.
-/
theorem normalizedStep_publisher (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.1
      = (acc.2.1.normalizeBatch (acc.1.handleGraphEvents batch).2).1 := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  simp only [normalizedStep]
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [empty, IncrementalPublisher.normalizeBatch]
  · rfl

/-- Every normalized step appends precisely its actual raw batch's atomic expansion.
Witness: the empty raw batch contributes no atoms, and the other branch appends one batch.
-/
theorem normalizedStep_atoms (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.2.flatten.flatMap publicationAtoms
      = acc.2.2.flatten.flatMap publicationAtoms
        ++ ((acc.2.1.normalizeBatch (acc.1.handleGraphEvents batch).2).2.flatMap
              publicationAtoms) := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  simp only [normalizedStep]
  split
  · rename_i empty
    simp only [List.isEmpty_iff] at empty
    simp [empty, IncrementalPublisher.normalizeBatch]
  · simp

/-- Multi-batch source annotations agree with the actual normalized fold and its accumulator.
Witness: batch agreement and append associativity, without changing any batch boundary.
-/
theorem State.sourceRunBlocks_fold (queue : State) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent)) (outputs : List (List Execution.WorkQueueEvent))
    : let traced := queue.sourceRunBlocks publisher batches
      let actual := batches.foldl normalizedStep (queue, publisher, outputs)
      traced.1 = actual.1
      ∧ traced.2.1 = actual.2.1
      ∧ outputs.flatten.flatMap publicationAtoms ++ traced.2.2.flatMap Prod.snd
        = actual.2.2.flatten.flatMap publicationAtoms := by
  induction batches generalizing queue publisher outputs with
  | nil => simp [State.sourceRunBlocks]
  | cons batch rest ih =>
      obtain ⟨state, mapper, emitted⟩ := queue.sourceBatchBlocks_agrees publisher batch
      let next := normalizedStep (queue, publisher, outputs) batch
      have stateEq : (queue.sourceBatchBlocks publisher batch).1 = next.1 := by
        rw [normalizedStep_queue]
        exact state
      have mapperEq : (queue.sourceBatchBlocks publisher batch).2.1 = next.2.1 := by
        rw [normalizedStep_publisher]
        exact mapper
      dsimp only [State.sourceRunBlocks]
      rw [stateEq, mapperEq]
      obtain ⟨finalState, finalMapper, finalOutput⟩ := ih next.1 next.2.1 next.2.2
      refine ⟨finalState, finalMapper, ?_⟩
      rw [List.flatMap_append, ← List.append_assoc, emitted]
      rw [← normalizedStep_atoms (queue, publisher, outputs) batch]
      exact finalOutput

/-- The block view preserves the public runner's final queue and exact flattened atoms.
Witness: initialize the same publisher and empty output accumulator in the fold theorem.
-/
theorem State.sourceRunBlocks_agrees (queue : State) (batches : List (List GraphEvent))
    : let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      let traced := queue.sourceRunBlocks publisher batches
      traced.1 = (queue.runNormalized batches).1
      ∧ traced.2.2.flatMap Prod.snd
        = (queue.runNormalized batches).2.flatten.flatMap publicationAtoms := by
  obtain ⟨state, _, output⟩ := queue.sourceRunBlocks_fold
    { active := queue.initialGroups ++ queue.initialStreams } batches []
  exact ⟨state, output⟩

/-- Retained handler inputs form a source subsequence across the original input batches.
Witness: concatenate the batch subsequences; terminal blocks carry no source identity.
-/
theorem State.sourceRunBlocks_inputs (queue : State) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent))
    : ((queue.sourceRunBlocks publisher batches).2.2.filterMap Prod.fst).Sublist
        batches.flatten := by
  induction batches generalizing queue publisher with
  | nil => exact .slnil
  | cons batch rest ih =>
      simp only [State.sourceRunBlocks, List.filterMap_append, List.flatten_cons]
      exact (queue.sourceBatchBlocks_inputs publisher batch).append (ih _ _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
