import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackTaskHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ControlEligibility

/-! Batch-entry filtering retains every already available task callback, including one
retired by an earlier input in this same batch. Only older retired callbacks are removed.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open WorkQueueSemantics (Occurrence)

/-- Preserve the host batch's original eligibility boundary when projecting callbacks. -/
def projectBatchAtEntry (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : List GraphEvent :=
  batch.filter queue.acceptsGraphEvent

/-- This projection never reorders or invents an input. -/
theorem projectBatchAtEntry_sublist (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    : (projectBatchAtEntry queue batch).Sublist batch :=
  List.filter_sublist

/-- Fresh closure identities retain current-head permission for internal controls. -/
theorem projectBatchAtEntry_accepts (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    (unique : (batch.flatMap (fun event => event.identities.2)).Nodup)
    : queue.acceptsBatch (projectBatchAtEntry queue batch) = true := by
  apply queue.acceptsBatch_of_entry
  · intro event member
    exact (List.mem_filter.mp member).2
  · have included : ((projectBatchAtEntry queue batch).flatMap
          (fun event => event.identities.2)).Sublist
          (batch.flatMap (fun event => event.identities.2)) := by
      clear unique
      induction batch with
      | nil => exact .refl _
      | cons event rest ih =>
          simp only [projectBatchAtEntry, List.filter_cons, List.flatMap_cons] at ih ⊢
          split
          · exact (List.Sublist.refl _).append ih
          · exact ih.trans (List.sublist_append_right _ _)
    exact unique.sublist included

/-- Callbacks formed together at one queue boundary all survive batch-entry projection. -/
theorem Enqueued.projectBatchAtEntry_eq {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    : projectBatchAtEntry queue (callbacks.map BufferedCallback.event)
      = callbacks.map BufferedCallback.event := by
  apply List.filter_eq_self.mpr
  intro event member
  obtain ⟨callback, present, same⟩ := List.mem_map.mp member
  exact same ▸ queued.started callback present

/-- Independent callback/source facts at one actual batch entry. Stream actions are still
active; task callbacks retain their earlier started disposition and permanent descriptor.
-/
structure BatchCallbackFrame (work : Work) (queue : ReferenceWorkQueue.State)
    (before : List GraphEvent) (batch : List GraphEvent)
    : Prop where
  metadata : queue.CallbackTaskFrame work before
  valid : ReferenceWorkQueue.ValidGraphEvents work (before ++ batch)
  tasks : TrackedTaskBatch queue batch
  streams
    : ∀ event ∈ batch,
        ∀ action, event.streamAction = some action → queue.acceptsGraphEvent event = true

  controls
    : ∀ notice,
        .groupFailure notice ∈ batch
        → queue.acceptsGraphEvent (.groupFailure notice) = true

private def retiredCallbacks (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : List Occurrence :=
  batch.filterMap
    (fun event => if queue.acceptsGraphEvent event then none else event.taskCallback?)

private theorem BatchCallbackFrame.retired {work queue before batch}
    (frame : BatchCallbackFrame work queue before batch)
    : ∀ occurrence ∈ retiredCallbacks queue batch,
        queue.RetiredTask occurrence
        ∧ occurrence ∈ queue.tasks.map ReferenceWorkQueue.Task.occurrence := by
  intro occurrence member
  obtain ⟨event, present, selected⟩ := List.mem_filterMap.mp member
  split at selected
  · cases selected
  · rename_i absent
    exact frame.tasks.retired_of_ineligible present selected (Bool.eq_false_iff.mpr absent)

private theorem BatchCallbackFrame.dropped {work queue before batch}
    (frame : BatchCallbackFrame work queue before batch) (event : GraphEvent)
    (member : event ∈ batch) (stale : queue.acceptsGraphEvent event = false)
    : ∃ occurrence ∈ retiredCallbacks queue batch,
        event.taskCallback? = some occurrence := by
  have kind : ∃ occurrence, event.taskCallback? = some occurrence := by
    cases event with
    | taskSuccess occurrence result | taskFailure occurrence errors =>
        exact ⟨occurrence, rfl⟩
    | groupFailure notice =>
        have accepted := frame.controls notice member
        rw [stale] at accepted
        contradiction
    | streamItems stream items | streamSuccess stream | streamFailure stream errors =>
        have accepted := frame.streams _ member _ rfl
        rw [stale] at accepted
        contradiction
  obtain ⟨occurrence, identity⟩ := kind
  refine ⟨occurrence, List.mem_filterMap.mpr ⟨event, member, ?_⟩, identity⟩
  simpa only [stale, Bool.false_eq_true, ↓reduceIte] using identity

/-- Source-derived task retirement licenses exact batch projection. Retained work laws
are supplied separately by producer/FIFO reasoning, without an output-equivalence premise.
-/
theorem BatchCallbackFrame.projectBatchAtEntry_exact
    {work queue before batch retainedBefore}
    (frame : BatchCallbackFrame work queue before batch)
    (retained
      : ReferenceWorkQueue.ValidGraphEvents work
          (retainedBefore ++ projectBatchAtEntry queue batch))
    : queue.handleGraphEvents (projectBatchAtEntry queue batch)
      = queue.handleGraphEvents batch := by
  apply queue.handleGraphEvents_filterRetired batch queue.acceptsGraphEvent
    (retiredCallbacks queue batch) frame.metadata.keys
    (fun occurrence member => (frame.retired occurrence member).1) frame.dropped
  · intro occurrence member event present task incoming
    exact frame.metadata.registered_not_child (frame.retired occurrence member).2 batch frame.valid
      present incoming
  · exact frame.valid
  · exact retained

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
