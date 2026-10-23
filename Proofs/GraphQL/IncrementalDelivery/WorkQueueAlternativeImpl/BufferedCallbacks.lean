import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackProjectionHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StaleCallbacks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Callback projection retains whole-batch cached availability for initially eligible
inputs. Only task callbacks retired before batch entry are filtered from semantic input.
Receipt and native ownership observations remain attached to the original host history.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Semantic callbacks retain their original batch-entry eligibility boundary. -/
abbrev projectBatch := projectBatchAtEntry

/-- Silent batches and post-terminal callbacks do not manufacture semantic source inputs. -/
abbrev projectHistory := projectHistoryAtEntry

/-- Distinct internal control identities let every retained callback pass batch admission. -/
theorem projectBatch_accepts (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    (distinct : (batch.flatMap (fun event => event.identities.2)).Nodup)
    : queue.acceptsBatch (projectBatch queue batch) = true :=
  projectBatchAtEntry_accepts queue batch distinct

/-- Semantic projection never invents, duplicates or reorders an input. -/
theorem projectBatch_sublist (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : (projectBatch queue batch).Sublist batch :=
  projectBatchAtEntry_sublist queue batch

/-- Source-derived retirement and independently proved retained work laws yield exact replay. -/
theorem projectBatch_handleGraphEvents (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent) {work before retained}
    (frame : BatchCallbackFrame work queue before batch)
    (valid
      : ReferenceWorkQueue.ValidGraphEvents work (retained ++ projectBatch queue batch))
    : queue.handleGraphEvents (projectBatch queue batch)
      = queue.handleGraphEvents batch :=
  frame.projectBatchAtEntry_exact valid

/-- The native boundary-buffer projection uses the same initial queue eligibility. -/
def projectAlternativeBatch (state : State) (batch : List GraphEvent) : List GraphEvent :=
  projectBatch state.queue batch

/-- A buffer whose callbacks all had permission at this boundary is unchanged. This local
native equality does not claim an arbitrary raw callback history is a legal source.
-/
theorem projectBatch_alternative (state : State) (batch : List GraphEvent)
    (accepted : ∀ event ∈ batch, state.queue.acceptsGraphEvent event = true)
    : let raw := state.handleGraphEvents batch
      let effective := state.handleGraphEvents (projectAlternativeBatch state batch)
      effective.state = raw.state ∧ effective.workQueueEvents = raw.workQueueEvents := by
  have same : projectAlternativeBatch state batch = batch := List.filter_eq_self.mpr accepted
  simp only [same, and_self]

/-- Derived source evidence constructs source admission without a raw executable-start premise. -/
theorem projectHistory_started (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (boundary : Boundary queue) {work before retained}
    (sources : CallbackProjectionSource work queue before retained batches)
    : startedFrom queue (projectHistory queue batches) = true :=
  sources.started boundary

/-- The same publisher and ordered outputs replay the original cached host batches. -/
theorem projectHistory_runWithPublisher (queue : ReferenceWorkQueue.State)
    (publisher : ReferenceWorkQueue.IncrementalPublisher)
    (batches : List (List GraphEvent)) (boundary : Boundary queue) {work before retained}
    (sources : CallbackProjectionSource work queue before retained batches)
    : queue.runWithPublisher publisher (projectHistory queue batches)
      = queue.runWithPublisher publisher batches :=
  sources.runWithPublisher publisher boundary

/-- Normalized replay retains queue state as well as every published batch. -/
theorem projectHistory_runNormalized (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (boundary : Boundary queue) {work before retained}
    (sources : CallbackProjectionSource work queue before retained batches)
    : queue.runNormalized (projectHistory queue batches) = queue.runNormalized batches :=
  sources.runNormalized boundary

/-- Source-start discipline follows from a constructed projection certificate. -/
theorem projected_inputsStarted {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (batches : List (List GraphEvent))
    (sources
      : CallbackProjectionSource work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) [] [] batches)
    : ReferenceWorkQueue.inputsStarted work
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) batches)
      = true := by
  rw [inputsStarted_eq]
  exact sources.started (initialized_boundary generated nonempty)

/-- Work-law projection is distinct from membership projection. Work legality alone
is insufficient: premature items of a held stream can be ignored, then the stream
can activate with a shifted raw cursor. Enqueue-time eligibility excludes that case.
This target concerns BoundaryBuffers, not arbitrary raw work-valid histories or all
interleaved native callbacks. Its witness lives in BufferedWorkProjection; it is neither
an axiom nor a public source premise.
-/
def BufferedWorkProjection : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → work.size ≠ 0
    → BoundaryBuffers work
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)) [] batches
    → ReferenceWorkQueue.ValidGraphEvents work
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches).flatten

/-- Composition edge using the separate work-law witness, not just exact queue replay.
No desired output accounting or wire property is assumed to obtain source discipline.
-/
theorem projected_sourceLaws_of_workProjection (projection : BufferedWorkProjection)
    {work : Work} (generated : ReferenceWorkQueue.ExecutedWork work)
    (nonempty : work.size ≠ 0) (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          [] batches)
    : let inputs :=
        projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches
      ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true :=
  ⟨
    projection work batches generated nonempty buffers,
    projected_inputsStarted generated nonempty batches
      (buffers.projectionSource generated)
  ⟩

/-- Conformance composition using a separate work-law witness. That witness alone does
not certify native enqueue/receipt correspondence or full interleaved callback histories.
-/
theorem projected_conforms_of_workProjection (projection : BufferedWorkProjection)
    {work : Work} (generated : ReferenceWorkQueue.ExecutedWork work)
    (nonempty : work.size ≠ 0) (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          [] batches)
    : let inputs :=
        projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches
      (createWorkQueueForSchedule work (EventSource.ofList inputs)).Conforms work := by
  obtain ⟨matching, started⟩ := projected_sourceLaws_of_workProjection projection
    generated nonempty batches buffers
  exact createWorkQueueForScheduleConforms_holds _ _ generated
    ((Execution.Work.isEmpty_eq_false work).mpr nonempty)
    (source_valid_of_laws _ matching started)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
