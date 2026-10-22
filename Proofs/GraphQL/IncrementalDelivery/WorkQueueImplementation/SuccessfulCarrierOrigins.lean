import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchReplay

/-! Successful normalized carriers retain their actual source-handler boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Raw output identifies the source event and exact pre-handler queue
-----------------------------------------------------------------------------------------

/-- Each raw output comes from one actual source handler at a concrete input prefix.
Witness: split the output concatenation during source-list induction; earlier silent
handlers still advance the queue and remain in the recovered source prefix.
-/
theorem State.rawEventReplay_output_origin (queue : State) (received : List GraphEvent)
    (available : List (Occurrence × Nat) := []) {output : WorkQueueEvent}
    (member : output ∈ (queue.rawEventReplay received available).2)
    : ∃ before event after,
        received = before ++ event :: after
        ∧ output
          ∈ ((queue.replayGraphEvents before available).handleGraphEvent event
              available).2.1 := by
  induction received generalizing queue with
  | nil => cases member
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available] at member
      rcases List.mem_append.mp member with current | later
      · exact ⟨[], event, rest, rfl, current⟩
      · obtain ⟨before, source, after, same, emitted⟩ := ih _ later
        exact ⟨event :: before, source, after, by simp [same], emitted⟩

/-- A successful atomic publisher carrier is an unchanged raw carrier.
Witness: invert atomic expansion and publisher normalization at the selected positions.
-/
theorem IncrementalPublisher.normalizeBatch_atomicGroupSuccess_origin
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (publisher.normalizeBatch events).2.flatMap publicationAtoms)
    : Execution.WorkQueueEvent.groupSuccess group groups streams ∈ events := by
  obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp member
  obtain ⟨normalizedIndex, normalizedEvent, _⟩ := publicationAtoms_groupSuccess_prefix _ atEvent
  obtain ⟨rawIndex, rawEvent, _⟩ := publisher.normalizeBatch_groupSuccess events normalizedEvent
  exact List.mem_of_getElem? rawEvent

/-- A successful carrier in an annotated batch comes from an actual source handler.
Witness: annotation agreement and publisher inversion reduce it to raw replay; terminal
bookkeeping cannot emit a successful group carrier.
-/
theorem State.sourceBatchBlocks_startup_groupSuccess_origin (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent)
    {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.sourceBatchBlocks publisher received).2.2.flatMap Prod.snd)
    : ∃ before event after,
        received = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((queue.replayGraphEvents before
                (GraphEvent.availableFailures received)).handleGraphEvent
              event (GraphEvent.availableFailures received)).2.1 := by
  rw [(queue.sourceBatchBlocks_agrees publisher received).2.2] at member
  have raw := publisher.normalizeBatch_atomicGroupSuccess_origin _ member
  have immediate : Execution.WorkQueueEvent.groupSuccess group groups streams
      ∈ (queue.rawEventReplay received (GraphEvent.availableFailures received)).2 := by
    rw [State.handleGraphEvents_eq_rawEventReplay queue received] at raw
    split at raw
    · cases raw
    · dsimp only at raw
      split at raw
      · have preceding := (List.mem_append.mp raw).resolve_right (by simp)
        exact preceding
      · exact raw
  exact queue.rawEventReplay_output_origin received
    (GraphEvent.availableFailures received) immediate

/-- Ordinary batch provenance retains the same direct dispatch origin. -/
theorem State.sourceBatchBlocks_groupSuccess_origin (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent) {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.sourceBatchBlocks publisher received).2.2.flatMap Prod.snd)
    : ∃ before event after,
        received = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((queue.replayGraphEvents before
                (GraphEvent.availableFailures received)).handleGraphEvent
              event (GraphEvent.availableFailures received)).2.1 :=
  queue.sourceBatchBlocks_startup_groupSuccess_origin publisher received member

-----------------------------------------------------------------------------------------
-- A successful carrier retains both its batch boundary and within-batch source prefix
-----------------------------------------------------------------------------------------

/-- A successful carrier has an actual host-batch and fixed-snapshot handler origin.
Witness: split the actual batch trace, then its immediate FIFO outputs. Queue state follows
the preceding batches and the selected batch's full rejection availability.
-/
theorem State.sourceRunBlocks_startup_groupSuccess_origin (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)
    : ∃ earlier batch later before event after,
        batches = earlier ++ batch :: later
        ∧ batch = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ (((queue.replayBatches earlier).replayGraphEvents before
                (GraphEvent.availableFailures batch)).handleGraphEvent
              event (GraphEvent.availableFailures batch)).2.1 := by
  induction batches generalizing queue publisher with
  | nil => cases member
  | cons batch rest ih =>
      simp only [State.sourceRunBlocks, List.flatMap_append] at member
      rcases List.mem_append.mp member with first | later
      · obtain ⟨before, event, after, same, emitted⟩ :=
          queue.sourceBatchBlocks_startup_groupSuccess_origin publisher batch first
        exact ⟨[], batch, rest, before, event, after, rfl, same, emitted⟩
      · obtain ⟨earlier, selected, remaining, before, event, after, same, within, emitted⟩ :=
          ih _ _ later
        refine ⟨batch :: earlier, selected, remaining, before, event, after, ?_, within, ?_⟩
        · simp only [same, List.cons_append]
        · rw [(queue.sourceBatchBlocks_agrees publisher batch).1] at emitted
          exact emitted

/-- Ordinary multi-batch provenance retains the same dispatched-state origin. -/
theorem State.sourceRunBlocks_groupSuccess_origin (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)
    : ∃ earlier batch later before event after,
        batches = earlier ++ batch :: later
        ∧ batch = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ (((queue.replayBatches earlier).replayGraphEvents before
                (GraphEvent.availableFailures batch)).handleGraphEvent
              event (GraphEvent.availableFailures batch)).2.1 :=
  queue.sourceRunBlocks_startup_groupSuccess_origin publisher batches member

/-- A normalized carrier retains its actual batch and within-batch source-handler cut.
The accepted-start parameter remains for callers, but provenance itself needs no source
admission or cache-erasing flattening premise.
-/
theorem createWorkQueue_runNormalized_groupSuccess_origin {work : Execution.Work}
    (batches : List (List GraphEvent)) (_started : inputsStarted work batches = true)
    {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : ∃ earlier batch later before event after,
        batches = earlier ++ batch :: later
        ∧ batch = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((((State.initialize (Work.fromExecution work)).replayBatches
                earlier).replayGraphEvents
                before (GraphEvent.availableFailures batch)).handleGraphEvent
              event (GraphEvent.availableFailures batch)).2.1 := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  apply queue.sourceRunBlocks_groupSuccess_origin publisher batches
  rw [(queue.sourceRunBlocks_agrees batches).2]
  exact List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
