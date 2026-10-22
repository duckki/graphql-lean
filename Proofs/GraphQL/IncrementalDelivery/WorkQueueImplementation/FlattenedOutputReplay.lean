import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks

/-! Actual raw batch output retains the normalized atomic history without flattening inputs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A batch that remains open is precisely its actual fixed-snapshot dispatch replay.
Pending notices keep their consumed FIFO positions.
-/
theorem State.handleGraphEvents_nonterminal (queue : State) (events : List GraphEvent)
    (running : queue.terminated = false)
    (remains : (queue.handleGraphEvents events).1.terminated = false)
    : queue.handleGraphEvents events
      = queue.rawEventReplay events (GraphEvent.availableFailures events) := by
  rw [State.handleGraphEvents_eq_rawEventReplay] at remains ⊢
  simp only [running, Bool.false_eq_true, ↓reduceIte] at remains ⊢
  split at remains <;> simp_all

/-- Source blocks equal normalization of actual raw batches with every boundary retained.
Witness: compose each batch's queue and publisher agreement through the raw batch fold.
Deferred startup forwarding and termination controls stay in their actual output order.
-/
theorem State.sourceRunBlocks_rawBatches (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    : (queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd
      = (publisher.normalizeBatch (queue.rawBatches batches).2).2.flatMap
          publicationAtoms := by
  induction batches generalizing queue publisher with
  | nil =>
      simp [State.sourceRunBlocks, State.rawBatches, IncrementalPublisher.normalizeBatch]
  | cons batch rest ih =>
      have ⟨state, mapper, output⟩ := queue.sourceBatchBlocks_agrees publisher batch
      rw [State.sourceRunBlocks, List.flatMap_append, ih, State.rawBatches,
        IncrementalPublisher.normalizeBatch_append]
      simp only [List.flatMap_append, state, mapper, output]

/-- Actual normalized output agrees with normalization of the actual raw batch output.
The proof needs no accepted-start premise and does not identify batch-dependent caches
with an empty-snapshot flattened input replay.
-/
theorem createWorkQueue_runNormalized_rawBatches {work : Execution.Work}
    (inputs : List (List GraphEvent))
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
      = (publisher.normalizeBatch (queue.rawBatches inputs).2).2.flatMap
          publicationAtoms := by
  let queue := State.initialize (Work.fromExecution work)
  exact (queue.sourceRunBlocks_agrees inputs).2.symm.trans
    (queue.sourceRunBlocks_rawBatches _ inputs)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
