import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BatchCallbackWorkLaws
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackStreamHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackControlHistory

/-! Construct source-law evidence along one actual cached callback history. No queue/output
equivalence is assumed; each batch derives it from task retirement and stream activation.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Original source and enqueue facts at each actual consumed host boundary. -/
def CallbackBatchFrames (work : Work) (queue : ReferenceWorkQueue.State)
    (before : List GraphEvent)
    : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      BatchCallbackFrame work queue before batch
      ∧ CallbackBatchFrames work (queue.handleGraphEvents batch).1 (before ++ batch) rest

/-- Independent task and stream history witnesses combine at the same concrete boundaries. -/
theorem CallbackBatchFrames.of_task_stream {work queue before batches}
    (tasks : TrackedTaskBatches work queue before batches)
    (streams : AvailableStreamBatches queue batches)
    (controls : AvailableControlBatches queue batches)
    : CallbackBatchFrames work queue before batches := by
  induction batches generalizing queue before with
  | nil => trivial
  | cons batch rest ih =>
      exact ⟨⟨tasks.1, tasks.2.1, tasks.2.2.1, streams.1, controls.1⟩,
        ih tasks.2.2.2 streams.2 controls.2⟩

/-- The unchanged interleaved history supplies all per-batch projection premises. -/
theorem CallbackHistory.batchFrames {work buffer}
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) buffer)
    : CallbackBatchFrames work
        (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
        [] buffer.rawBatches :=
  .of_task_stream history.trackedTaskBatches
    (history.streamFrame
      (ReferenceWorkQueue.createWorkQueue_callbackTaskFrame work)).consumed
    (history.controlFrame
      (ReferenceWorkQueue.createWorkQueue_callbackTaskFrame work)).consumed

/-- Buffers enqueued together supply the same per-batch frame without filtering any input. -/
theorem BoundaryBuffers.batchFrames {work queue before batches}
    (buffers : BoundaryBuffers work queue before batches)
    (metadata : queue.CallbackTaskFrame work before)
    (valid : ReferenceWorkQueue.ValidGraphEvents work before)
    : CallbackBatchFrames work queue before batches := by
  induction batches generalizing queue before with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨⟨callbacks, queued, same⟩, later⟩ := buffers
      have laws := queued.work_valid valid
      rw [same] at laws
      have accepted : ∀ event ∈ batch, queue.acceptsGraphEvent event = true := by
        intro event member
        rw [← same] at member
        obtain ⟨callback, present, identity⟩ := List.mem_map.mp member
        exact identity ▸ queued.started callback present
      refine ⟨⟨metadata, laws, ?_, ?_, ?_⟩,
        ih later (metadata.handleGraphEvents batch laws) laws⟩
      · intro event member occurrence identity
        exact taskCallback_tracked metadata (accepted event member) identity
      · intro event member action source
        exact accepted event member
      · intro notice member
        exact accepted (.groupFailure notice) member

/-- Project each batch at its original entry and erase only silent or post-terminal inputs. -/
def projectHistoryAtEntry (queue : ReferenceWorkQueue.State)
    : List (List GraphEvent) → List (List GraphEvent)
  | [] => []
  | batch :: rest =>
      let effective := if queue.terminated then [] else projectBatchAtEntry queue batch
      let later := projectHistoryAtEntry (queue.handleGraphEvents batch).1 rest
      if effective.isEmpty then later else effective :: later

/-- A terminated semantic queue has no projected future input. -/
theorem projectHistoryAtEntry_of_terminated (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (ended : queue.terminated = true)
    : projectHistoryAtEntry queue batches = [] := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      simp only [projectHistoryAtEntry, ended, ↓reduceIte, List.isEmpty_nil,
        queue.handleGraphEvents_after_termination batch ended]
      exact ih

/-- Independently constructed raw/retained work laws at each running projection boundary.
This certificate contains source structure and work legality, never output equivalence.
-/
def CallbackProjectionSource (work : Work) (queue : ReferenceWorkQueue.State)
    (before retained : List GraphEvent)
    : List (List GraphEvent) → Prop
  | [] => ReferenceWorkQueue.ValidGraphEvents work retained
  | batch :: rest =>
      if queue.terminated then
        ReferenceWorkQueue.ValidGraphEvents work retained
      else
        BatchCallbackFrame work queue before batch
        ∧ ReferenceWorkQueue.ValidGraphEvents work
            (retained ++ projectBatchAtEntry queue batch)
        ∧ CallbackProjectionSource work (queue.handleGraphEvents batch).1
            (before ++ batch) (retained ++ projectBatchAtEntry queue batch) rest

/-- Producer support, stream cursors and source metadata construct every retained batch law. -/
theorem CallbackBatchFrames.projectionSource {work queue before batches}
    (frames : CallbackBatchFrames work queue before batches)
    (generated : ReferenceWorkQueue.ExecutedWork work) (retained : List GraphEvent)
    (support : SourceSupport work queue retained)
    (valid : ReferenceWorkQueue.ValidGraphEvents work retained)
    (included : retained.Sublist before)
    (cursors
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    : CallbackProjectionSource work queue before retained batches := by
  induction batches generalizing queue before retained with
  | nil => exact valid
  | cons batch rest ih =>
      cases ended : queue.terminated with
      | true => simpa only [CallbackProjectionSource, ended, ↓reduceIte] using valid
      | false =>
          simp only [CallbackProjectionSource, ended, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨laws, nextSupport, nextCursors⟩ := frames.1.projectBatchAtEntry_source
            generated support valid included cursors
          exact ⟨frames.1, laws, ih frames.2 _ nextSupport laws
            (included.append (projectBatchAtEntry_sublist queue batch)) nextCursors⟩

/-- The same retained source laws hold over the complete projected finite history. -/
theorem CallbackProjectionSource.work_valid {work queue before retained batches}
    (sources : CallbackProjectionSource work queue before retained batches)
    : ReferenceWorkQueue.ValidGraphEvents work
        (retained ++ (projectHistoryAtEntry queue batches).flatten) := by
  induction batches generalizing queue before retained with
  | nil => simpa only [CallbackProjectionSource, projectHistoryAtEntry, List.flatten_nil,
      List.append_nil] using sources
  | cons batch rest ih =>
      cases ended : queue.terminated with
      | true =>
          simpa only [CallbackProjectionSource, ended, ↓reduceIte,
            projectHistoryAtEntry_of_terminated queue (batch :: rest) ended, List.flatten_nil,
            List.append_nil] using sources
      | false =>
          have step : BatchCallbackFrame work queue before batch
              ∧ ReferenceWorkQueue.ValidGraphEvents work
                  (retained ++ projectBatchAtEntry queue batch)
              ∧ CallbackProjectionSource work (queue.handleGraphEvents batch).1 (before ++ batch)
                  (retained ++ projectBatchAtEntry queue batch) rest := by
            simpa only [CallbackProjectionSource, ended, Bool.false_eq_true, ↓reduceIte]
              using sources
          have later := ih step.2.2
          simp only [projectHistoryAtEntry, ended, Bool.false_eq_true, ↓reduceIte]
          cases empty : (projectBatchAtEntry queue batch).isEmpty with
          | true =>
              have nil : projectBatchAtEntry queue batch = [] := List.isEmpty_iff.mp empty
              simpa only [empty, ↓reduceIte, nil, List.append_nil] using later
          | false =>
              simpa only [empty, Bool.false_eq_true, ↓reduceIte, List.flatten_cons,
                List.append_assoc] using later

/-- Enqueue/reduction history derives projected work laws without a semantic-source premise. -/
theorem CallbackHistory.projectionSource {work buffer}
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) buffer)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    : CallbackProjectionSource work
        (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
        [] [] buffer.rawBatches :=
  history.batchFrames.projectionSource generated [] (SourceSupport.initialize work) .nil
    (.refl []) (fun _ => rfl)

/-- Boundary buffers also construct their retained source certificate from original work laws. -/
theorem BoundaryBuffers.projectionSource {work batches}
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) [] batches)
    (generated : ReferenceWorkQueue.ExecutedWork work)
    : CallbackProjectionSource work
        (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
        [] [] batches :=
  (buffers.batchFrames (ReferenceWorkQueue.createWorkQueue_callbackTaskFrame work) .nil)
  |>.projectionSource generated [] (SourceSupport.initialize work) .nil (.refl [])
      (fun _ => rfl)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
