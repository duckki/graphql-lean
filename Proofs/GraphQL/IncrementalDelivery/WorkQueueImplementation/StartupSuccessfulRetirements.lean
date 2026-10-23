import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulCarrierOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupOutputBlocks

/-! Successful startup carriers retain their exact source cut and permanent retirement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A startup successful carrier comes from its actual batch/FIFO handler. Initial queued
reports are all failures, so they cannot fabricate a success carrier or source position.
-/
theorem State.startup_runNormalized_groupSuccess_origin {work : Execution.Work}
    (startup : InitialStartup) (batches : List (List GraphEvent)) {group groups streams}
    (carrier
      : let initial := State.initialize (Work.fromExecution work) startup
        Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (initial.runNormalized batches).2.flatten)
    : ∃ earlier batch later before event after,
        batches = earlier ++ batch :: later
        ∧ batch = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((((State.initialize (Work.fromExecution work) startup).replayBatches
                earlier).replayGraphEvents
                before (GraphEvent.availableFailures batch)).handleGraphEvent
              event (GraphEvent.availableFailures batch)).2.1 := by
  let initial := State.initialize (Work.fromExecution work) startup
  let publisher : IncrementalPublisher :=
    { active := initial.initialGroups ++ initial.initialStreams }
  apply initial.sourceRunBlocks_groupSuccess_origin publisher batches
  rw [(initial.sourceRunBlocks_withPublisher_agrees publisher batches).2.2]
  exact List.mem_flatMap.mpr ⟨_, carrier, List.mem_cons_self⟩

/-- Actual successful group closure leaves a known, uncancelled retirement that survives
all remaining callbacks in the same cache snapshot and every later supplied host batch.
The initial failure tail changes neither this source cut nor subsequent queue state.
-/
theorem ExecutedWork.startup_runNormalized_successfulGroupRetirements
    {work batches group groups streams} (generated : ExecutedWork work)
    (startup : InitialStartup) (matched : startup.MatchesWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work) startup)).runNormalized
            batches).2.flatten)
    : ∃ dependencies,
        GroupRecordAt work group dependencies
        ∧ UncancelledRetirement
            (((State.initialize (Work.fromExecution work) startup)).runNormalized
              batches).1
            group.ref := by
  obtain ⟨earlier, batch, later, fifo, event, after, splitBatches, within, emitted⟩ :=
    State.startup_runNormalized_groupSuccess_origin startup batches carrier
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let initial := (State.initialize (Work.fromExecution work) startup)
  let boundary := initial.replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have before := generated.startup_uncancelledFrame_atBatchPrefix canonical startup matched
    earlier batch later fifo (splitBatches ▸ valid) (splitBatches ▸ started)
    ⟨event :: after, within.symm⟩
  have batchMatches : ∀ event ∈ batch, event.MatchesWork work := by
    intro event member
    apply valid.eachMatches
    rw [splitBatches, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ member)
  have source := batchMatches event (by
    rw [within]; exact List.mem_append_right _ List.mem_cons_self)
  obtain ⟨dependencies, known, protectedRef⟩ :=
    State.handleGraphEvent_successfulRetirements before.parent before.cancellations generated
      canonical event source available group groups streams emitted
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rw [← splitBatches, ← inputsStartedWithStartup_eq_batchesStarted]
    exact started
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  obtain ⟨running, _, _⟩ := boundary.batchesStarted_cons batch later checked.2
  obtain ⟨terminal, core⟩ := boundary.handleGraphEvents_stateCore batch running
  have dispatched : UncancelledRetirement (current.dispatchGraphEvent event available).1
      group.ref := protectedRef
  have continued := dispatched.replayGraphEvents after available
  have batchEnd : UncancelledRetirement (boundary.handleGraphEvents batch).1 group.ref := by
    rw [core]
    change UncancelledRetirement
      { boundary.replayGraphEvents batch available with terminated := terminal } group.ref
    rw [within, State.replayGraphEvents_append _ _ _ available]
    exact continued.withTerminated terminal
  refine ⟨dependencies, known, ?_⟩
  simpa only [boundary, initial, State.runNormalized_replayBatches, splitBatches,
    State.replayBatches, List.foldl_append, List.foldl_cons]
    using batchEnd.replayBatches later

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
