import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorReplay
import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperControl

/-! Exact wire replay through the shared publisher and closed-reader retirement. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

private theorem kernelBatch_termination (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent) (running : queue.terminated = false)
    : WorkQueueEvent.workQueueTermination ∈ (queue.handleGraphEvents batch).2
      ↔ (queue.handleGraphEvents batch).1.terminated = true := by
  rw [ReferenceWorkQueue.State.handleGraphEvents_eq_rawEventReplay]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split
  · simp
  · simp [ReferenceWorkQueue.State.rawEventReplay_noTermination,
      ReferenceWorkQueue.State.rawEventReplay_terminated, running]

private theorem publisherBatch_hasNext (queue : ReferenceWorkQueue.State)
    (publisher : ReferenceWorkQueue.IncrementalPublisher) (batch : List GraphEvent)
    (running : queue.terminated = false)
    : (publisher.handleBatch (queue.handleGraphEvents batch).2).1.hasNext
      = !(queue.handleGraphEvents batch).1.terminated := by
  have terminal :
      (publisher.normalizeBatch (queue.handleGraphEvents batch).2).2.any
          Correctness.isTermination = (queue.handleGraphEvents batch).1.terminated := by
    apply Bool.eq_iff_iff.mpr
    rw [Correctness.any_termination,
      ReferenceWorkQueue.IncrementalPublisher.normalizeBatch_termination_mem,
      kernelBatch_termination queue batch running]
  change ((Execution.mapWorkEventBatch
    (publisher.normalizeBatch (queue.handleGraphEvents batch).2).2).run
      publisher.ids).1.hasNext = _
  rw [Correctness.mapWorkEventBatch_hasNext, terminal]

/-- The reference cursor projects to identical live state or retired closed-reader records. -/
def ResponseStreamCursor.fromReference (cursor : ReferenceWorkQueue.ResponseStreamCursor)
    : ResponseStreamCursor :=
  let next : ResponseStreamCursor :=
    {
      queue := State.fromReference cursor.queue,
      publisher := cursor.publisher,
      finished := cursor.queue.terminated
    }
  if cursor.queue.terminated then next.onWorkQueueFinished else next

/-- Wire ID retirement does not change the projected queue boundary. -/
theorem ResponseStreamCursor.fromReference_queue
    (cursor : ReferenceWorkQueue.ResponseStreamCursor)
    : (ResponseStreamCursor.fromReference cursor).queue
      = State.fromReference cursor.queue := by
  unfold ResponseStreamCursor.fromReference
  split <;> rfl

/-- Initialized response replay finishes exactly at semantic termination. Abrupt close
is a separate transition and is not covered by this reference projection.
-/
theorem ResponseStreamCursor.fromReference_finished
    (cursor : ReferenceWorkQueue.ResponseStreamCursor)
    : (ResponseStreamCursor.fromReference cursor).finished = cursor.queue.terminated := by
  unfold ResponseStreamCursor.fromReference
  split
  · simpa only [ResponseStreamCursor.onWorkQueueFinished]
      using (by assumption : cursor.queue.terminated = true).symm
  · rfl

@[simp]
theorem ResponseStreamCursor.fromReference_terminated
    (cursor : ReferenceWorkQueue.ResponseStreamCursor)
    : (ResponseStreamCursor.fromReference cursor).queue.queue.terminated
      = cursor.queue.terminated := by
  simp only [ResponseStreamCursor.fromReference]
  split <;> simp only [ResponseStreamCursor.onWorkQueueFinished, State.fromReference_terminated]

/-- Final mapping precedes ID retirement; closed cursors and silent batches emit nothing. -/
theorem ResponseStreamCursor.handleBatch_fromReference
    (cursor : ReferenceWorkQueue.ResponseStreamCursor) (batch : List GraphEvent)
    (reducer
      : ((State.fromReference cursor.queue).handleGraphEvents batch).state
          = State.fromReference (cursor.queue.handleGraphEvents batch).1
        ∧ ((State.fromReference cursor.queue).handleGraphEvents batch).workQueueEvents
          = (cursor.queue.handleGraphEvents batch).2)
    : let reference := cursor.step batch
      let alternative := (ResponseStreamCursor.fromReference cursor).handleBatch batch
      alternative.1 = reference.1
      ∧ alternative.2.1 = ResponseStreamCursor.fromReference reference.2 := by
  cases running : cursor.queue.terminated with
  | true =>
      simp [ResponseStreamCursor.fromReference, ResponseStreamCursor.onWorkQueueFinished,
        ResponseStreamCursor.handleBatch, ReferenceWorkQueue.ResponseStreamCursor.step_eq,
        ReferenceWorkQueue.State.handleGraphEvents_after_termination _ _ running, running]
  | false =>
      have projected : ResponseStreamCursor.fromReference cursor =
          { queue := State.fromReference cursor.queue, publisher := cursor.publisher,
            finished := false } := by
        simp [ResponseStreamCursor.fromReference, running]
      obtain ⟨state, events⟩ := reducer
      have flag := publisherBatch_hasNext cursor.queue cursor.publisher batch running
      have terminal := kernelBatch_termination cursor.queue batch running
      rw [projected]
      simp only [ResponseStreamCursor.handleBatch, Bool.false_eq_true, ↓reduceIte, state, events,
        ReferenceWorkQueue.ResponseStreamCursor.step_eq]
      by_cases silent : (cursor.queue.handleGraphEvents batch).2.isEmpty = true
      · have openNext : (cursor.queue.handleGraphEvents batch).1.terminated = false := by
          apply Bool.eq_false_iff.mpr
          intro ended
          have member := terminal.mpr ended
          simp only [List.isEmpty_iff] at silent
          simp [silent] at member
        simp [silent, ResponseStreamCursor.fromReference, openNext]
      · cases ended : (cursor.queue.handleGraphEvents batch).1.terminated with
        | false =>
            simp [silent, flag, ended, ResponseStreamCursor.fromReference]
        | true =>
            simp [silent, flag, ended, ResponseStreamCursor.fromReference,
              ResponseStreamCursor.onWorkQueueFinished]

private abbrev cursorStep
    (acc
      : List Execution.IncrementalStreamUpdateResult
        × ResponseStreamCursor
        × List HostEffect) (batch : List GraphEvent)
    : List Execution.IncrementalStreamUpdateResult
      × ResponseStreamCursor
      × List HostEffect :=
  let next := acc.2.1.handleBatch batch
  (acc.1 ++ next.1.toList, next.2.1, acc.2.2 ++ next.2.2)

private theorem cursorFold_prefix (cursor : ResponseStreamCursor)
    (inputs : List (List GraphEvent))
    (prior : List Execution.IncrementalStreamUpdateResult) (effects : List HostEffect)
    : inputs.foldl cursorStep (prior, cursor, effects)
      = let next := inputs.foldl cursorStep ([], cursor, [])
        (prior ++ next.1, next.2.1, effects ++ next.2.2) := by
  have same := List.foldl_hom
    (fun acc : List Execution.IncrementalStreamUpdateResult × ResponseStreamCursor
      × List HostEffect => (prior ++ acc.1, acc.2.1, effects ++ acc.2.2))
    (g₁ := cursorStep) (g₂ := cursorStep) (l := inputs) (init := ([], cursor, [])) ?_
  · simpa only [List.append_nil] using same
  · rintro ⟨updates, cursor, before⟩ batch
    simp only [cursorStep, List.append_assoc]

theorem ResponseStreamCursor.run_cons (cursor : ResponseStreamCursor)
    (batch : List GraphEvent) (rest : List (List GraphEvent))
    : cursor.run (batch :: rest)
      = let next := cursor.handleBatch batch
        let last := next.2.1.run rest
        (next.1.toList ++ last.1, last.2.1, next.2.2 ++ last.2.2) := by
  change (batch :: rest).foldl cursorStep ([], cursor, []) = _
  rw [List.foldl_cons]
  exact cursorFold_prefix _ _ _ _

/-- Valid started online replay preserves updates and the projected residual reader.
The cursor carries its actual batch-prefix provenance; each supplied batch retains its
own failure-availability snapshot.
-/
theorem ResponseStreamCursor.run_fromReference
    (cursor : ReferenceWorkQueue.ResponseStreamCursor) (inputs : List (List GraphEvent))
    {work : Work} (generated : ReferenceWorkQueue.ExecutedWork work)
    (earlier : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ inputs).flatten)
    (provenance
      : cursor.queue
        = (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)).replayBatches
            earlier)
    (started : ReferenceWorkQueue.inputsStarted work (earlier ++ inputs) = true)
    : ((ResponseStreamCursor.fromReference cursor).run inputs).1 = (cursor.run inputs).1
      ∧ ((ResponseStreamCursor.fromReference cursor).run inputs).2.1
        = ResponseStreamCursor.fromReference (cursor.run inputs).2 := by
  induction inputs generalizing cursor earlier with
  | nil => exact ⟨rfl, rfl⟩
  | cons batch rest ih =>
      have reducer : ((State.fromReference cursor.queue).handleGraphEvents batch).state
            = State.fromReference (cursor.queue.handleGraphEvents batch).1
          ∧ ((State.fromReference cursor.queue).handleGraphEvents batch).workQueueEvents
            = (cursor.queue.handleGraphEvents batch).2 := by
        rw [provenance]
        exact referencePrefix_handleGraphEvents generated earlier batch rest valid started
      have stepQueue : (cursor.step batch).2.queue = (cursor.queue.handleGraphEvents batch).1 := by
        rw [ReferenceWorkQueue.ResponseStreamCursor.step_eq]
        cases reduced : cursor.queue.handleGraphEvents batch with
        | mk queue events =>
            dsimp only
            split <;> rfl
      have validNext : ReferenceWorkQueue.ValidGraphEvents work
          ((earlier ++ [batch]) ++ rest).flatten := by
        simpa only [List.append_assoc, List.singleton_append] using valid
      have provenanceNext : (cursor.step batch).2.queue = (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayBatches (earlier ++ [batch]) := by
        rw [stepQueue, ReferenceWorkQueue.State.replayBatches_append, ← provenance]
        rfl
      have startedNext : ReferenceWorkQueue.inputsStarted work ((earlier ++ [batch]) ++ rest)
          = true := by
        simpa only [List.append_assoc, List.singleton_append] using started
      rw [ResponseStreamCursor.run_cons, ReferenceWorkQueue.ResponseStreamCursor.run_cons]
      obtain ⟨update, next⟩ := ResponseStreamCursor.handleBatch_fromReference cursor batch reducer
      simp only [update, next]
      obtain ⟨updates, final⟩ := ih (cursor.step batch).2 (earlier ++ [batch]) validNext
        provenanceNext startedNext
      exact ⟨congrArg (fun tail => (cursor.step batch).1.toList ++ tail) updates, final⟩

/-- Shared initialization allocates the same initial IDs and starts with a live reader. -/
theorem ResponseStreamCursor.buildResponse_fromReference (response : Execution.Response)
    (work : Work)
    : ResponseStreamCursor.buildResponse response work
      = let reference := ReferenceWorkQueue.ResponseStreamCursor.initialize response work
        (reference.1, ResponseStreamCursor.fromReference reference.2) := by
  simp only [ResponseStreamCursor.buildResponse, State.initialize_queue,
    ReferenceWorkQueue.ResponseStreamCursor.initialize,
    ReferenceWorkQueue.initializeIncrementalResponse]
  simp only [ResponseStreamCursor.fromReference, ReferenceWorkQueue.createWorkQueue_terminated,
    Bool.false_eq_true, ↓reduceIte, State.initialize_fromReference, State.fromReference]

/-- Initial notices and IDs are exactly those of the shared reference publisher. -/
theorem ResponseStreamCursor.buildResponse_initial (response : Execution.Response)
    (work : Work)
    : (ResponseStreamCursor.buildResponse response work).1
      = (ReferenceWorkQueue.ResponseStreamCursor.initialize response work).1 := by
  rw [ResponseStreamCursor.buildResponse_fromReference]

/-- The initialized cursor bridge uses exactly the public generated replay premises. -/
theorem ResponseStreamCursor.run_initialize_fromReference (response : Execution.Response)
    (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : let cursor := (ReferenceWorkQueue.ResponseStreamCursor.initialize response work).2
      ((ResponseStreamCursor.fromReference cursor).run inputs).1 = (cursor.run inputs).1
      ∧ ((ResponseStreamCursor.fromReference cursor).run inputs).2.1
        = ResponseStreamCursor.fromReference (cursor.run inputs).2 := by
  exact ResponseStreamCursor.run_fromReference _ inputs generated []
    (by simpa using valid) rfl (by simpa using started)

/-- Actual initialized readers emit the reference updates for valid started generated inputs. -/
theorem ResponseStreamCursor.run_buildResponse_updates (response : Execution.Response)
    (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((ResponseStreamCursor.buildResponse response work).2.run inputs).1
      = ((ReferenceWorkQueue.ResponseStreamCursor.initialize response work).2.run
          inputs).1 := by
  rw [ResponseStreamCursor.buildResponse_fromReference]
  exact (ResponseStreamCursor.run_initialize_fromReference response work inputs generated valid
    started).1

/-- Terminal record clearing preserves the reference's semantic completion flag. -/
theorem ResponseStreamCursor.run_buildResponse_terminated (response : Execution.Response)
    (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((ResponseStreamCursor.buildResponse response work).2.run
        inputs).2.1.queue.queue.terminated
      = ((ReferenceWorkQueue.ResponseStreamCursor.initialize response work).2.run
          inputs).2.queue.terminated := by
  rw [ResponseStreamCursor.buildResponse_fromReference,
    (ResponseStreamCursor.run_initialize_fromReference response work inputs generated valid
      started).2,
    ResponseStreamCursor.fromReference_terminated]

/-- The actual generated reader and normalized replay have the same full queue state,
including terminal record clearing, under the original valid/started input discipline.
-/
theorem ResponseStreamCursor.run_buildResponse_queue (response : Execution.Response)
    (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((ResponseStreamCursor.buildResponse response work).2.run inputs).2.1.queue
      = ((State.initialize work).runNormalized inputs).1 := by
  rw [ResponseStreamCursor.buildResponse_fromReference,
    (ResponseStreamCursor.run_initialize_fromReference response work inputs generated valid
      started).2,
    ResponseStreamCursor.fromReference_queue]
  have same := (ReferenceWorkQueue.ResponseStreamCursor.run_initialize response work inputs).2
  rw [same, State.runNormalized_initialize work inputs generated valid started]

/-- In actual initialized replay, the finished guard and the queue's semantic flag agree.
This is not an equation for arbitrary manually assembled or abruptly closed cursors.
-/
theorem ResponseStreamCursor.run_buildResponse_finished (response : Execution.Response)
    (work : Work) (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ((ResponseStreamCursor.buildResponse response work).2.run inputs).2.1.finished
      = ((State.initialize work).runNormalized inputs).1.queue.terminated := by
  rw [ResponseStreamCursor.buildResponse_fromReference,
    (ResponseStreamCursor.run_initialize_fromReference response work inputs generated valid
      started).2,
    ResponseStreamCursor.fromReference_finished]
  have same := (ReferenceWorkQueue.ResponseStreamCursor.run_initialize response work inputs).2
  rw [same, State.runNormalized_initialize work inputs generated valid started,
    State.fromReference_terminated]

/-- Actual response replay is identical; host effects and terminal record erasure are separate. -/
theorem replayIncrementalResponse_eq_reference
    (completed : Execution.Completion (List (Name × Execution.ResponseValue)))
    (inputs : List (List GraphEvent))
    (generated : ReferenceWorkQueue.ExecutedWork completed.work)
    (valid : ReferenceWorkQueue.ValidGraphEvents completed.work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted completed.work inputs = true)
    : replayIncrementalResponse completed inputs
      = ReferenceWorkQueue.replayIncrementalResponse completed inputs := by
  rw [ReferenceWorkQueue.replayIncrementalResponse_eq_cursor]
  unfold replayIncrementalResponse
  simp only [ResponseStreamCursor.buildResponse_fromReference]
  obtain ⟨updates, final⟩ := ResponseStreamCursor.run_initialize_fromReference
    (Execution.selectionSetResultToResponse completed.result) completed.work inputs generated valid
    started
  simp only [updates, final, ResponseStreamCursor.fromReference_terminated]

/-- Witness of the exact public response-replay target, including counted errors and notices. -/
theorem responseReplayMatchesReference_holds : responseReplayMatchesReference := by
  intro completed inputs generated valid started
  exact replayIncrementalResponse_eq_reference completed inputs generated valid started

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
