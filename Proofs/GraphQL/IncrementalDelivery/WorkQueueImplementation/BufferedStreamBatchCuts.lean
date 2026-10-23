import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamSourceFrames

/-! Buffered child-stream conservation retains exact actual batch and FIFO cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Adding already emitted stream notices preserves a conservation certificate. -/
theorem State.BufferedStreamsConserved.mono_notices {queue next first later}
    (conserved : State.BufferedStreamsConserved queue first next)
    (included
      : (first.flatMap rawStreamNoticeRefs).Subset (later.flatMap rawStreamNoticeRefs))
    : queue.BufferedStreamsConserved later next := by
  intro occurrence node value stream found stored attached owner contributes live uncancelled
  exact (conserved occurrence node value stream found stored attached owner contributes live
    uncancelled).imp_left (fun member => included member)

/-- Setting termination preserves the exact producer lookup and buffered links. -/
theorem State.BufferedStreamsConserved.withTerminated {queue next events}
    (conserved : State.BufferedStreamsConserved queue events next) (terminal : Bool)
    : queue.BufferedStreamsConserved events {next with terminated := terminal} := by
  simpa only [State.BufferedStreamsConserved, State.taskNode?] using conserved

/-- Batch-final startup diagnostics and termination add no stream announcements. -/
theorem State.handleGraphEvents_streamNoticeRefs (queue : State) (batch : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.handleGraphEvents batch).2.flatMap rawStreamNoticeRefs
      = (queue.rawEventReplay batch (GraphEvent.availableFailures batch)).2.flatMap
          rawStreamNoticeRefs := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [List.flatMap_append, rawStreamNoticeRefs]

/-- An actual FIFO handler's stream notices are forwarded by its enclosing host batch. -/
theorem State.handler_streamNotices_subset_batch (queue : State)
    {batch fifo event tail} (split : batch = fifo ++ event :: tail)
    (running : queue.terminated = false)
    : (((queue.replayGraphEvents fifo
          (GraphEvent.availableFailures batch)).handleGraphEvent
          event (GraphEvent.availableFailures batch)).2.1.flatMap
        rawStreamNoticeRefs).Subset
        ((queue.handleGraphEvents batch).2.flatMap rawStreamNoticeRefs) := by
  let available := GraphEvent.availableFailures batch
  rw [queue.handleGraphEvents_streamNoticeRefs batch running]
  change List.Subset _ ((queue.rawEventReplay batch available).2.flatMap rawStreamNoticeRefs)
  have equation := queue.rawEventReplay_append fifo (event :: tail) available
  rw [← split] at equation
  rw [equation]
  dsimp only
  rw [State.rawEventReplay_cons _ _ _ available, List.flatMap_append, List.flatMap_append,
    State.rawEventReplay_state _ fifo available]
  exact (List.subset_append_left _ _).trans (List.subset_append_right _ _)

/-- Cancellation markers at an actual FIFO prefix remain at that host batch's endpoint. -/
theorem State.batchPrefix_cancelledGroups_subset (queue : State) {batch fifo tail}
    (split : batch = fifo ++ tail) (running : queue.terminated = false)
    : (queue.replayGraphEvents fifo
        (GraphEvent.availableFailures batch)).cancelledGroups.Subset
        (queue.handleGraphEvents batch).1.cancelledGroups := by
  let available := GraphEvent.availableFailures batch
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore batch running
  rw [same]
  change List.Subset _ (queue.replayGraphEvents batch available).cancelledGroups
  have equation := queue.replayGraphEvents_append fifo tail available
  rw [← split] at equation
  rw [equation]
  exact State.replayGraphEvents_cancelledGroups_subset _ tail available

/-- A valid actual FIFO prefix derives its buffered-stream source and link frame. -/
theorem ExecutedWork.bufferedStreamFrame_atBatchPrefix {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : BufferedStreamSourceFrame
        (((State.initialize (Work.fromExecution work)).replayBatches
            earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch))
        work parents (earlier.flatten ++ fifo) := by
  let initial := State.initialize (Work.fromExecution work)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have before := (initial_bufferedStreamSourceFrame generated canonical).runNormalized
    (before := []) generated canonical earlier validEarlier checked.1
  rw [State.runNormalized_replayBatches] at before
  simp only [List.nil_append] at before
  obtain ⟨_, accepted, _⟩ :=
    (initial.replayBatches earlier).batchesStarted_cons batch later checked.2
  obtain ⟨tail, same⟩ := prefixOfBatch
  have fifoAccepted : State.acceptsBatch.go (fun _ => false)
      (GraphEvent.availableFailures batch) (initial.replayBatches earlier) fifo = true := by
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [State.acceptsBatch, same] using accepted
  have validFifo : ValidGraphEvents work (earlier.flatten ++ fifo) := by
    apply valid.prefix
    refine ⟨tail ++ later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, ← same, List.append_assoc]
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures batch →
        (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, identity⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at identity
    obtain ⟨rfl, rfl⟩ := identity
    apply valid.eachMatches
    simp only [List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  exact before.replayGraphEvents_admitted generated canonical fifo validFifo
    (GraphEvent.availableFailures batch) licensed fifoAccepted

/-- A FIFO suffix and all later actual batches conserve the current buffered child links.
Earlier outputs in the current batch remain available as notice evidence. The endpoint
uses the actual batch termination flag and all later batches' own cache snapshots.
-/
theorem BufferedStreamSourceFrame.batchTail_conserves
    {queue : State} {work parents} {before batch fifo tail : List GraphEvent}
    {later : List (List GraphEvent)}
    (frame : BufferedStreamSourceFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (split : batch = fifo ++ tail)
    (valid : ValidGraphEvents work (before ++ batch ++ later.flatten))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch batch = true)
    (restStarted : (queue.handleGraphEvents batch).1.batchesStarted later = true)
    : (queue.replayGraphEvents fifo
        (GraphEvent.availableFailures batch)).BufferedStreamsConserved
        (queue.rawBatches (batch :: later)).2 (queue.replayBatches (batch :: later)) := by
  let available := GraphEvent.availableFailures batch
  let current := queue.replayGraphEvents fifo available
  have validBatch : ValidGraphEvents work (before ++ fifo ++ tail) := by
    apply valid.prefix
    exact ⟨later.flatten, by simp [split, List.append_assoc]⟩
  have licensed : ∀ occurrence errors, (occurrence, errors) ∈ available →
      (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply valid.eachMatches
    exact List.mem_append_left _ (List.mem_append_right _ received)
  have framesAt (suffix : List GraphEvent) (earlier : suffix.IsPrefix tail) :
      BufferedStreamSourceFrame (current.replayGraphEvents suffix available) work parents
        ((before ++ fifo) ++ suffix) := by
    obtain ⟨rest, joined⟩ := earlier
    have validPrefix : ValidGraphEvents work (before ++ (fifo ++ suffix)) := by
      apply valid.prefix
      exact ⟨rest ++ later.flatten, by simp [split, ← joined, List.append_assoc]⟩
    have checked : State.acceptsBatch.go (fun _ => false) available queue (fifo ++ suffix) = true := by
      apply State.acceptsBatch_go_prefix (after := rest)
      rw [List.append_assoc, joined, ← split]
      exact accepted
    have result := frame.replayGraphEvents_admitted generated canonical (fifo ++ suffix)
      validPrefix available licensed checked
    simpa only [current, State.replayGraphEvents_append, List.append_assoc] using result
  have conserved := BufferedStreamSourceFrame.replayGraphEvents_conserves_of_prefixFrames
    tail validBatch available licensed framesAt
  have afterFrame := framesAt tail (List.prefix_refl _)
  have stateEq : queue.replayGraphEvents batch available
      = current.replayGraphEvents tail available := by
    simp only [current, split, State.replayGraphEvents, List.foldl_append]
  obtain ⟨terminal, batchState⟩ := queue.handleGraphEvents_stateCore batch running
  rw [stateEq] at batchState
  have batchFrame : BufferedStreamSourceFrame (queue.handleGraphEvents batch).1 work parents
      (before ++ batch) := by
    rw [batchState]
    rw [split, ← List.append_assoc]
    exact afterFrame.withTerminated terminal
  have finalBatch : current.BufferedStreamsConserved (current.rawEventReplay tail available).2
      (queue.handleGraphEvents batch).1 := by
    rw [batchState]
    exact conserved.withTerminated terminal
  have rest := batchFrame.rawBatches_conserves generated canonical later valid restStarted
  have cancellation := (queue.handleGraphEvents batch).1.rawBatches_cancelledGroups_subset later
  rw [State.rawBatches_state] at cancellation
  have combined := finalBatch.append rest cancellation
  apply combined.mono_notices
  simp only [State.rawBatches, List.flatMap_append]
  have early : ((current.rawEventReplay tail available).2.flatMap rawStreamNoticeRefs).Subset
      ((queue.handleGraphEvents batch).2.flatMap rawStreamNoticeRefs) := by
    rw [queue.handleGraphEvents_streamNoticeRefs batch running]
    change ((current.rawEventReplay tail available).2.flatMap rawStreamNoticeRefs).Subset
      ((queue.rawEventReplay batch available).2.flatMap rawStreamNoticeRefs)
    have equation := queue.rawEventReplay_append fifo tail available
    rw [← split] at equation
    rw [equation]
    dsimp only
    rw [List.flatMap_append, State.rawEventReplay_state _ fifo available]
    exact List.subset_append_right _ _
  intro ref member
  rcases List.mem_append.mp member with first | next
  · exact List.mem_append_left _ (early first)
  · exact List.mem_append_right _ next

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
