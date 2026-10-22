import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceHandlerBoundaries

/-! Immediate atomic outputs retain their exact FIFO trace inside the actual host batch. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Publisher normalization forwards startup failure controls without changing their shape. -/
theorem IncrementalPublisher.normalizeBatch_startupFailures_atoms
    (publisher : IncrementalPublisher) (failures : List GroupFailureEvent)
    : (publisher.normalizeBatch
        (failures.map
          (fun failure =>
            WorkQueueEvent.groupFailure failure.group failure.errors))).2.flatMap
        publicationAtoms
      = failures.map
          (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors) := by
  induction failures generalizing publisher with
  | nil => rfl
  | cons failure rest ih =>
      simp only [List.map_cons, IncrementalPublisher.normalizeBatch_cons, List.flatMap_cons,
        IncrementalPublisher.handleWorkQueueEvent, publicationAtoms,
        List.singleton_append, ih]

/-- A nonfailure, nonterminal atom lies in the immediate FIFO trace at the same index.
Only the optional terminal marker lies outside the FIFO trace. The strict prefix agrees
as a list, including every preceding internal failure control and ordinary handler atom. -/
theorem State.sourceBatchBlocks_immediatePrefix (queue : State)
    (publisher : IncrementalPublisher) (batch : List GraphEvent) {index output}
    (selected
      : ((queue.sourceBatchBlocks publisher batch).2.2.flatMap Prod.snd)[index]?
        = some output)
    (_notStartup : ∀ group errors, output ≠ .groupFailure group errors)
    (notTermination : output ≠ .workQueueTermination)
    : let atoms :=
        (queue.sourceOutputBlocks publisher batch
          (GraphEvent.availableFailures batch)).2.2.flatMap
          Prod.snd
      atoms[index]? = some output
      ∧ ((queue.sourceBatchBlocks publisher batch).2.2.flatMap Prod.snd).take index
        = atoms.take index := by
  let atoms := (queue.sourceOutputBlocks publisher batch
    (GraphEvent.availableFailures batch)).2.2.flatMap Prod.snd
  have lift (controls : List WorkQueueEvent) (absent : output ∉ controls)
      (same : (queue.sourceBatchBlocks publisher batch).2.2.flatMap Prod.snd = atoms ++ controls)
      : atoms[index]? = some output
        ∧ ((queue.sourceBatchBlocks publisher batch).2.2.flatMap Prod.snd).take index
          = atoms.take index := by
    rw [same] at selected ⊢
    by_cases inside : index < atoms.length
    · exact ⟨(List.getElem?_append_left inside).symm.trans selected,
        List.take_append_of_le_length (Nat.le_of_lt inside)⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt inside)] at selected
      exact False.elim (absent (List.mem_of_getElem? selected))
  cases running : queue.terminated with
  | true => simp [State.sourceBatchBlocks, running] at selected
  | false =>
      have shape : ∃ terminal : Bool,
          (queue.sourceBatchBlocks publisher batch).2.2.flatMap Prod.snd = atoms ++
            (if terminal then [.workQueueTermination] else []) := by
        simp only [State.sourceBatchBlocks, running, Bool.false_eq_true, ↓reduceIte]
        split
        · refine ⟨true, ?_⟩
          simp only [List.flatMap_append, List.flatMap_singleton,
            ↓reduceIte]
          rfl
        · refine ⟨false, ?_⟩
          simp only [Bool.false_eq_true,
            ↓reduceIte, List.append_nil]
          rfl
      obtain ⟨terminal, same⟩ := shape
      apply lift (if terminal then [.workQueueTermination] else [])
      · cases terminal with
        | false => simp
        | true => simpa only [↓reduceIte, List.mem_singleton] using notTermination
      · exact same

/-- Annotation replay has the actual batch-fold state for every publisher. -/
theorem State.sourceRunBlocks_state (queue : State) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent))
    : (queue.sourceRunBlocks publisher batches).1 = queue.replayBatches batches := by
  induction batches generalizing queue publisher with
  | nil => rfl
  | cons batch rest ih =>
      simpa only [State.sourceRunBlocks, State.replayBatches, List.foldl_cons,
        (queue.sourceBatchBlocks_agrees publisher batch).1] using ih
        (queue.sourceBatchBlocks publisher batch).1
        (queue.sourceBatchBlocks publisher batch).2.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
