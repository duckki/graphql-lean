import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

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
    : BlocksFollowRegistrations
        (queue.replayGraphEvents events (GraphEvent.availableFailures events)).tasks
        published
        (queue.rawEventReplay events (GraphEvent.availableFailures events)).2 := by
  rw [State.handleGraphEvents_eq_rawEventReplay] at ordered
  simp only [running, Bool.false_eq_true, ↓reduceIte] at ordered
  rw [← State.rawEventReplay_state _ _ (GraphEvent.availableFailures events)]
  split at ordered
  · exact (BlocksFollowRegistrations.append_iff.mp ordered).1
  · exact ordered

/-- Every actual raw batch block retains order on the one shared publication ledger.
Witness: compose exact batch label slices and extend each earlier registry along actual
batch transitions. Cache snapshots and queued completion controls remain in the replay.
-/
theorem State.BatchClosuresCovered.blocks_rawBatches {queue : State} {batches published}
    (covered : queue.BatchClosuresCovered batches published)
    : BlocksFollowRegistrations (queue.rawBatches batches).1.tasks published
        (queue.rawBatches batches).2 := by
  induction batches generalizing queue published with
  | nil => trivial
  | cons batch rest ih =>
      have first := BlocksFollowRegistrations.take_iff.mp covered.2.1
      have remaining := ih covered.2.2
      apply BlocksFollowRegistrations.append_iff.mpr
      exact ⟨first.mono (State.rawBatches_tasks_sublist _ _), remaining⟩

-----------------------------------------------------------------------------------------
-- Source validity turns exact registry subsequences into strict producer ordering
-----------------------------------------------------------------------------------------

/-- Each actual raw value block has producer order on its slice of the shared ledger.
Witness: retain the actual batch certificate and restrict the source-derived final
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
      : ((State.initialize (Work.fromExecution work)).rawBatches batches).2[index]?
        = some (.groupValues group values))
    : ProducerOrder work
        ((List.take values.length
            (published.drop
              (((((State.initialize (Work.fromExecution work)).rawBatches batches).2.take
                  index).flatMap
                  WorkQueueEvent.objectValues).length))).map
          Prod.fst) := by
  exact (createWorkQueue_rawBatches_producerOrder valid started).sublist
    (covered.blocks_rawBatches.atEvent selected)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
