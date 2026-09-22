import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FlattenedClosureLedger

/-! Started batches retain value-block order on their one shared publication ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Batch termination adds no task registration or object-label offset
-----------------------------------------------------------------------------------------

/-- Removing the batch wrapper preserves block ordering on the exact raw replay.
Witness: the wrapper only optionally appends a terminal control and changes its flag;
the raw prefix keeps its task registry and each object's occurrence-label slice.
-/
theorem State.handleGraphEvents_blocksFollowRegistrations {queue : State}
    {events published} (running : queue.terminated = false)
    (ordered
      : BlocksFollowRegistrations (queue.handleGraphEvents events).1.tasks published
          (queue.handleGraphEvents events).2)
    : BlocksFollowRegistrations (queue.replayGraphEvents events).tasks published
        (queue.rawEventReplay events).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay] at ordered
  simp only [running, Bool.false_eq_true, ↓reduceIte] at ordered
  rw [← State.rawEventReplay_state]
  split at ordered
  · exact (BlocksFollowRegistrations.append_iff.mp ordered).1
  · exact ordered

/-- Started batches retain every raw block's registration order on the same full ledger.
Witness: strip each wrapper, compose consecutive label slices, and enlarge earlier block
registries along the actual append-only source replay. No new occurrence matching is chosen.
-/
theorem State.BatchClosuresCovered.blocks_flatten {queue : State} {batches published}
    (covered : queue.BatchClosuresCovered batches published)
    (started : queue.batchesStarted batches = true)
    : BlocksFollowRegistrations (queue.replayGraphEvents batches.flatten).tasks published
        (queue.rawEventReplay batches.flatten).2 := by
  induction batches generalizing queue published with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨running, _, later⟩ := queue.batchesStarted_cons batch rest started
      have first := queue.handleGraphEvents_blocksFollowRegistrations running
        (BlocksFollowRegistrations.take_iff.mp covered.2.1)
      cases rest with
      | nil =>
          simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using first
      | cons next tail =>
          have openNext := ((queue.handleGraphEvents batch).1.batchesStarted_cons
            next tail later).1
          have remaining := ih covered.2.2 later
          have counts := congrArg List.length
            (queue.handleGraphEvents_objectValues batch running)
          rw [counts, queue.handleGraphEvents_nonterminalState batch running openNext]
            at remaining
          change BlocksFollowRegistrations
            (queue.replayGraphEvents (batch ++ (next :: tail).flatten)).tasks published
            (queue.rawEventReplay (batch ++ (next :: tail).flatten)).2
          have stateSplit : queue.replayGraphEvents (batch ++ (next :: tail).flatten)
              = (queue.replayGraphEvents batch).replayGraphEvents (next :: tail).flatten := by
            simp only [State.replayGraphEvents, List.foldl_append]
          rw [stateSplit, State.rawEventReplay_append]
          dsimp only
          rw [State.rawEventReplay_state]
          apply BlocksFollowRegistrations.append_iff.mpr
          exact ⟨first.mono (State.replayGraphEvents_tasks_sublist _ _), remaining⟩

-----------------------------------------------------------------------------------------
-- Source validity turns exact registry subsequences into strict producer ordering
-----------------------------------------------------------------------------------------

/-- Each actual raw value block has producer order on its slice of the shared ledger.
Witness: flatten the retained batch certificate and restrict the source-derived final
registry's pairwise producer relation to this exact indexed slice.
-/
theorem createWorkQueue_batch_blockProducerOrder
    {work batches published index group values}
    (covered
      : (State.initialize (Work.fromExecution work)).BatchClosuresCovered batches
          published)
    (started : inputsStarted work batches = true)
    (valid : ValidGraphEvents work batches.flatten)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay
          batches.flatten).2[index]?
        = some (.groupValues group values))
    : ProducerOrder work
        ((List.take values.length
            (published.drop
              (((((State.initialize (Work.fromExecution work)).rawEventReplay
                    batches.flatten).2.take
                  index).flatMap
                  WorkQueueEvent.objectValues).length))).map
          Prod.fst) := by
  have admitted : (State.initialize (Work.fromExecution work)).batchesStarted batches = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  exact (createWorkQueue_replayGraphEvents_producerOrder valid).2.sublist
    ((covered.blocks_flatten admitted).atEvent selected)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
