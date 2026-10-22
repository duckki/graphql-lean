import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStreamAdmission
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Work legality and conformance for cached batch-entry callback projection. All source
premises are derived from actual enqueue histories and producer/stream metadata. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

open ReferenceWorkQueue (StreamAction)

/-- Auxiliary stream-root checks under empty-snapshot eventwise replay. Task callbacks
may already be stale; full source projection uses the stronger batch-entry frames.
-/
def ActiveStreamBatches (queue : ReferenceWorkQueue.State) : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∀ prior event after action,
        batch = prior ++ event :: after
        → event.streamAction = some action
        → (queue.replayGraphEvents prior).acceptsGraphEvent event = true)
      ∧ ActiveStreamBatches (queue.handleGraphEvents batch).1 rest

/-- The actual queue boundary after the original batches, including termination flags. -/
def replayBatches (queue : ReferenceWorkQueue.State) (batches : List (List GraphEvent))
    : ReferenceWorkQueue.State :=
  batches.foldl (fun current batch => (current.handleGraphEvents batch).1) queue

/-- A new batch extends stream activation evidence at the same actual queue boundary. -/
theorem ActiveStreamBatches.append (queue : ReferenceWorkQueue.State)
    (before after : List (List GraphEvent))
    (earlier : ActiveStreamBatches queue before)
    (later : ActiveStreamBatches (replayBatches queue before) after)
    : ActiveStreamBatches queue (before ++ after) := by
  induction before generalizing queue with
  | nil => exact later
  | cons batch rest ih => exact ⟨earlier.1, ih _ earlier.2 later⟩

/-- Terminal queues have no projected future payloads. -/
theorem projectHistory_of_terminated (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (ended : queue.terminated = true)
    : projectHistory queue batches = [] :=
  projectHistoryAtEntry_of_terminated queue batches ended

/-- Source frames derive complete retained work laws independently of output replay. -/
theorem projectHistory_work_valid_of_frames {work queue before retained batches}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (frames : CallbackBatchFrames work queue before batches)
    (support : SourceSupport work queue retained)
    (valid : ReferenceWorkQueue.ValidGraphEvents work retained)
    (included : retained.Sublist before)
    (cursors
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    : ReferenceWorkQueue.ValidGraphEvents work
        (retained ++ (projectHistory queue batches).flatten) :=
  (frames.projectionSource generated retained support valid included cursors).work_valid

/-- Boundary buffers also satisfy the auxiliary eventwise stream-root checks.
Whole-history source correctness uses separately derived batch-entry activation.
-/
theorem BoundaryBuffers.activeStreams {work queue before batches}
    (buffers : BoundaryBuffers work queue before batches)
    (raw : ReferenceWorkQueue.ValidGraphEvents work before)
    : ActiveStreamBatches queue batches := by
  induction batches generalizing queue before with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨⟨callbacks, queued, same⟩, later⟩ := buffers
      refine ⟨?_, ih later ?_⟩
      · intro prior event after action split source
        exact queued.streamAction_accepted raw (same.trans split) source
      · simpa only [same] using queued.work_valid raw

/-- Boundary-buffer source projection retains the existing public work-law target. -/
theorem bufferedWorkProjection_holds : BufferedWorkProjection := by
  intro work batches generated nonempty buffers
  simpa only [List.nil_append] using (buffers.projectionSource generated).work_valid

/-- The projected source itself satisfies all original prefix and start/work laws. -/
theorem projected_source_valid {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) [] batches)
    : (EventSource.ofList
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches)).ValidFor
        work := by
  obtain ⟨valid, started⟩ := projected_sourceLaws_of_workProjection bufferedWorkProjection_holds
    generated nonempty batches buffers
  exact source_valid_of_laws _ valid started

/-- Legally enqueued boundary buffers yield conformance for their actual projected
alternative factory. Queue/publisher replay is exact, but native refinement is separate.
-/
theorem projected_conforms {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) [] batches)
    : (createWorkQueueForSchedule work
        (EventSource.ofList
          (projectHistory
            (ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work))
            batches))).Conforms
        work :=
  projected_conforms_of_workProjection bufferedWorkProjection_holds generated nonempty
    batches buffers

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
