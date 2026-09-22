import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

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
    {output : WorkQueueEvent} (member : output ∈ (queue.rawEventReplay received).2)
    : ∃ before event after,
        received = before ++ event :: after
        ∧ output ∈ ((queue.replayGraphEvents before).handleGraphEvent event).2 := by
  induction received generalizing queue with
  | nil => cases member
  | cons event rest ih =>
      rw [State.rawEventReplay_cons] at member
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
theorem State.sourceBatchBlocks_groupSuccess_origin (queue : State)
    (publisher : IncrementalPublisher) (received : List GraphEvent) {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.sourceBatchBlocks publisher received).2.2.flatMap Prod.snd)
    : ∃ before event after,
        received = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((queue.replayGraphEvents before).handleGraphEvent event).2 := by
  rw [(queue.sourceBatchBlocks_agrees publisher received).2.2] at member
  have raw := publisher.normalizeBatch_atomicGroupSuccess_origin _ member
  rw [State.handleGraphEvents_eq_rawEventReplay] at raw
  split at raw
  · cases raw
  · dsimp only at raw
    split at raw
    · apply queue.rawEventReplay_output_origin received
      exact (List.mem_append.mp raw).resolve_right (by simp)
    · exact queue.rawEventReplay_output_origin received raw

-----------------------------------------------------------------------------------------
-- Accepted batch boundaries preserve exact sequential replay until the final batch
-----------------------------------------------------------------------------------------

/-- Every successful carrier in started batch annotations has a real source boundary.
Witness: split annotated batches; a later accepted batch proves its predecessor stayed
open, so the intervening queue is exactly sequential replay, not just an abstract state.
-/
theorem State.sourceRunBlocks_groupSuccess_origin (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (started : queue.batchesStarted batches = true) {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.sourceRunBlocks publisher batches).2.2.flatMap Prod.snd)
    : ∃ before event after,
        batches.flatten = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((queue.replayGraphEvents before).handleGraphEvent event).2 := by
  induction batches generalizing queue publisher with
  | nil => cases member
  | cons batch rest ih =>
      obtain ⟨running, _, restStarted⟩ := queue.batchesStarted_cons batch rest started
      simp only [State.sourceRunBlocks, List.flatMap_append] at member
      rcases List.mem_append.mp member with first | later
      · obtain ⟨before, event, after, same, emitted⟩ :=
          queue.sourceBatchBlocks_groupSuccess_origin publisher batch first
        exact ⟨before, event, after ++ rest.flatten,
          by simp only [List.flatten_cons, same, List.append_assoc, List.cons_append], emitted⟩
      · have state := (queue.sourceBatchBlocks_agrees publisher batch).1
        have nextStarted : (queue.sourceBatchBlocks publisher batch).1.batchesStarted rest
            = true := by rwa [state]
        obtain ⟨before, event, after, same, emitted⟩ := ih _ _ nextStarted later
        have openNext : (queue.handleGraphEvents batch).1.terminated = false := by
          cases rest with
          | nil => cases later
          | cons next tail =>
              exact ((queue.handleGraphEvents batch).1.batchesStarted_cons next tail restStarted).1
        rw [state, queue.handleGraphEvents_nonterminalState batch running openNext] at emitted
        refine ⟨batch ++ before, event, after, ?_, ?_⟩
        · simp only [List.flatten_cons, same, List.append_assoc]
        · simpa only [State.replayGraphEvents, List.foldl_append] using emitted

/-- A normalized carrier retains the source event that emitted it, across all host batches.
Witness: place its unchanged success atom in the agreeing source-block history, then
recover the exact source prefix and pre-handler queue from accepted batch execution.
-/
theorem createWorkQueue_runNormalized_groupSuccess_origin {work : Execution.Work}
    (batches : List (List GraphEvent)) (started : inputsStarted work batches = true)
    {group groups streams}
    (member
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    : ∃ before event after,
        batches.flatten = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
                before).handleGraphEvent
              event).2 := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
  apply queue.sourceRunBlocks_groupSuccess_origin publisher batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  rw [(queue.sourceRunBlocks_agrees batches).2]
  exact List.mem_flatMap.mpr ⟨_, member, List.mem_cons_self⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
