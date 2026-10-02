import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedClosureLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks

/-! Started input batches preserve the flattened raw replay's normalized atomic prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Only the final batch may add a termination marker
-----------------------------------------------------------------------------------------

/-- A batch that remains open is exactly its raw replay, in both state and output.
Witness: the wrapper's terminal branch contradicts the final flag; its other branch is
the raw replay itself. This uses the implementation's actual batch boundaries.
-/
theorem State.handleGraphEvents_nonterminal (queue : State) (events : List GraphEvent)
    (running : queue.terminated = false)
    (remains : (queue.handleGraphEvents events).1.terminated = false)
    : queue.handleGraphEvents events = queue.rawEventReplay events := by
  rw [State.handleGraphEvents_eq_rawEventReplay] at remains ⊢
  simp only [running, Bool.false_eq_true, ↓reduceIte] at remains ⊢
  split at remains <;> simp_all

/-- Started batch replay has the raw replay's atomic output plus an optional final marker.
Witness: a later started batch excludes intermediate termination. Concatenate the actual
publisher states over earlier raw outputs; only the last wrapper can add a control event.
The result is an output equation, not permission to change the supplied execution batches.
-/
theorem State.sourceRunBlocks_flattened (queue : State) (publisher : IncrementalPublisher)
    (batches : List (List GraphEvent)) (started : queue.batchesStarted batches = true)
    : ∃ terminal : Bool,
        (queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd
        = (publisher.normalizeBatch (queue.rawEventReplay batches.flatten).2).2.flatMap
            publicationAtoms
          ++ if terminal then [.workQueueTermination] else [] := by
  induction batches generalizing queue publisher with
  | nil =>
      exact ⟨
        false,
        by simp [State.sourceRunBlocks, State.rawEventReplay,
          IncrementalPublisher.normalizeBatch]
      ⟩
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have ⟨state, mapper, outputs⟩ := queue.sourceBatchBlocks_agrees publisher batch
      cases rest with
      | nil =>
          simp only [State.sourceRunBlocks, List.append_nil,
            List.flatten_cons, List.flatten_nil, outputs]
          rw [State.handleGraphEvents_eq_rawEventReplay]
          simp only [running, Bool.false_eq_true, ↓reduceIte]
          split
          · exact ⟨true, by simp [IncrementalPublisher.normalizeBatch,
              IncrementalPublisher.handleWorkQueueEvent,
              publicationAtoms]⟩
          · exact ⟨false, by simp⟩
      | cons next tail =>
          have openNext := ((queue.handleGraphEvents batch).1.batchesStarted_cons
            next tail later).1
          have raw := queue.handleGraphEvents_nonterminal batch running openNext
          obtain ⟨terminal, remaining⟩ := ih (queue.sourceBatchBlocks publisher batch).1
            (queue.sourceBatchBlocks publisher batch).2.1 (by rwa [state])
          refine ⟨terminal, ?_⟩
          rw [State.sourceRunBlocks, List.flatMap_append, remaining]
          simp only [outputs,
            state, mapper, raw, List.flatten_cons, State.rawEventReplay_append,
            IncrementalPublisher.normalizeBatch_append, List.flatMap_append,
            List.append_assoc]

/-- Actual normalized output is the flattened raw replay's atomic output, then a marker.
Witness: source-block agreement and the started-batch flattening theorem. The initial
publisher is unchanged, so all owner remapping and announcement choices remain intact.
-/
theorem createWorkQueue_runNormalized_flattened {work : Execution.Work}
    (inputs : List (List GraphEvent)) (started : inputsStarted work inputs = true)
    : let queue := State.initialize (Work.fromExecution work)
      let publisher : IncrementalPublisher :=
        { active := queue.initialGroups ++ queue.initialStreams }
      ∃ terminal : Bool,
        (queue.runNormalized inputs).2.flatten.flatMap publicationAtoms
        = (publisher.normalizeBatch (queue.rawEventReplay inputs.flatten).2).2.flatMap
            publicationAtoms
          ++ if terminal then [.workQueueTermination] else [] := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨terminal, same⟩ := queue.sourceRunBlocks_flattened publisher inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  exact ⟨terminal, (queue.sourceRunBlocks_agrees inputs).2.symm.trans same⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
