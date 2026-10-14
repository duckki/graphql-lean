import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReaderLifecycle
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceLifecycleCounts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTermination

/-! Connect constructed acquired-resource histories to the actual initialized response
reader, including abrupt close and the already-finished guard. Native acquisitions and
callback correspondence are still independent, not inferred from a response or catalogue.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Actual response replay has the same constructed resource boundary
-----------------------------------------------------------------------------------------

/-- In initialized replay without abrupt close, termination and reader retirement coincide. -/
theorem State.runNormalized_stopped_eq_terminated (work : Work)
    (inputs : List (List GraphEvent))
    : ((State.initialize work).runNormalized inputs).1.stopped
      = ((State.initialize work).runNormalized inputs).1.queue.terminated := by
  apply State.runNormalized_flagsAligned
  rw [State.initialize_stopped, State.initialize_queue, ReferenceWorkQueue.createWorkQueue_terminated]

/-- The actual response reader's records and stop coverage are derived from the same
constructed FIFO prefix. A finished reader has no queue-owned acquired remainder.
This supplies model coverage, not complete native acquisition or effect quiescence.
-/
theorem ResourcePrefixConstruction.readerSafety {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work) (response : Execution.Response)
    : let cursor := ((ResponseStreamCursor.buildResponse response work).2.run inputs).2.1
      QueueResourcesRepresented cursor.queue.queue
        (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
      ∧ StopCoverage cursor.queue resources
      ∧ (cursor.finished = true → ∀ target, resources target ≠ .owned .queue) := by
  dsimp only
  obtain ⟨valid, started⟩ := built.sourceEvidence
  rw [ResponseStreamCursor.run_buildResponse_queue response work inputs generated valid started,
    ResponseStreamCursor.run_buildResponse_finished response work inputs generated valid started]
  exact ⟨(built.invariants generated).2.1, built.stopCoverage generated,
    fun ended => (built.invariants generated).2.2 ((State.runNormalized_stopped_eq_terminated _ _).trans ended)⟩

-----------------------------------------------------------------------------------------
-- Observe cleanup at the real close guard, never as a late synthetic dispatch
-----------------------------------------------------------------------------------------

/-- The proof observer follows the real response close guard. A finished reader requests
nothing, even if a malformed raw resource inventory still claims queue ownership.
-/
def ResourceState.observeReaderClose (resources : ResourceState)
    (cursor : ResponseStreamCursor)
    : ResourceState × List ResourceAction :=
  if cursor.finished then (resources, []) else resources.observeStop cursor.queue

/-- Close constructs one compatible legal history, including its silent finished branch. -/
theorem ResourceState.observeReaderClose_replay (resources : ResourceState)
    (cursor : ResponseStreamCursor)
    : ResourceReplay resources (resources.observeReaderClose cursor).2
        (resources.observeReaderClose cursor).1 := by
  unfold ResourceState.observeReaderClose
  split
  · exact .nil _
  · exact resources.observeStop_replay _

/-- Every observed close request is licensed by the same actual close's cleanup label.
The response-finished hook is not a cleanup request or an asynchronous settlement.
-/
theorem ResourceState.observeReaderClose_requests (resources : ResourceState)
    (cursor : ResponseStreamCursor) (action : ResourceAction)
    (observed : action ∈ (resources.observeReaderClose cursor).2)
    : ∃ target ∈ cursor.close.2.filterMap HostEffect.cleanupStart?,
        action = .requestCleanup target := by
  unfold ResourceState.observeReaderClose at observed
  split at observed
  · cases observed
  · rename_i running
    have live : cursor.finished = false := Bool.eq_false_iff.mpr running
    obtain ⟨target, requested, same⟩ := resources.requestQueueCleanup_actions _ action observed
    refine ⟨target, ?_, same⟩
    rw [ResponseStreamCursor.close_effects _ live, List.filterMap_append]
    exact List.mem_append_left _ requested

/-- Abruptly closing the actual reader leaves no queue-owned remainder in the same
constructed resource history, whether the reader is live or already finished.
Producer-owned suffixes and pending cleanup settlement remain native obligations.
-/
theorem ResourcePrefixConstruction.readerCloseSafety {work inputs resources actions}
    (built : ResourcePrefixConstruction work inputs resources actions)
    (generated : ReferenceWorkQueue.ExecutedWork work) (response : Execution.Response)
    : let cursor := ((ResponseStreamCursor.buildResponse response work).2.run inputs).2.1
      let observed := resources.observeReaderClose cursor
      ResourceReplay ResourceState.empty (actions ++ observed.2) observed.1
      ∧ ∀ target, observed.1 target ≠ .owned .queue := by
  dsimp only
  let cursor := ((ResponseStreamCursor.buildResponse response work).2.run inputs).2.1
  obtain ⟨_, coverage, finishedSafe⟩ := built.readerSafety generated response
  refine ⟨
    (built.invariants generated).1.append (resources.observeReaderClose_replay cursor),
    ?_
  ⟩
  change ∀ target, (resources.observeReaderClose cursor).1 target ≠ .owned .queue
  cases closed : cursor.finished with
  | true =>
      simpa only [ResourceState.observeReaderClose, closed, ↓reduceIte] using finishedSafe closed
  | false =>
      have running : cursor.queue.stopped = false := by
        obtain ⟨valid, started⟩ := built.sourceEvidence
        have ended := closed
        change ((ResponseStreamCursor.buildResponse response work).2.run inputs).2.1.finished = false at ended
        rw [ResponseStreamCursor.run_buildResponse_finished response work inputs generated valid started] at ended
        rw [ResponseStreamCursor.run_buildResponse_queue response work inputs generated valid started,
          State.runNormalized_stopped_eq_terminated]
        exact ended
      simpa only [ResourceState.observeReaderClose, closed, Bool.false_eq_true,
        ↓reduceIte]
        using resources.observeStop_no_owned cursor.queue running coverage

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
