import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackTaskHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ControlEligibility
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Pending internal controls keep their actual queued-head permission across reduction. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Internal controls in a consumed batch were eligible at that batch's entry. -/
def AvailableControlBatches (queue : ReferenceWorkQueue.State)
    : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∀ notice,
        .groupFailure notice ∈ batch
        → queue.acceptsGraphEvent (.groupFailure notice) = true)
      ∧ AvailableControlBatches (queue.handleGraphEvents batch).1 rest

theorem AvailableControlBatches.append (queue : ReferenceWorkQueue.State)
    (before after : List (List GraphEvent))
    (earlier : AvailableControlBatches queue before)
    (later : AvailableControlBatches (queue.replayBatches before) after)
    : AvailableControlBatches queue (before ++ after) := by
  induction before generalizing queue with
  | nil => exact later
  | cons batch rest ih => exact ⟨earlier.1, ih _ earlier.2 later⟩

/-- Enqueued and consumed controls share the same current-head interpretation. -/
structure CallbackBuffer.ControlFrame (initial : ReferenceWorkQueue.State)
    (buffer : CallbackBuffer)
    : Prop where
  pending
    : ∀ notice,
        .groupFailure notice ∈ buffer.pending.map BufferedCallback.event
        → buffer.queue.acceptsGraphEvent (.groupFailure notice) = true
  consumed : AvailableControlBatches initial buffer.rawBatches

theorem CallbackBuffer.ControlFrame.enqueue {initial buffer}
    (frame : CallbackBuffer.ControlFrame initial buffer) (callback : BufferedCallback)
    (accepted : buffer.queue.acceptsGraphEvent callback.event = true)
    : CallbackBuffer.ControlFrame initial (buffer.enqueue callback) := by
  refine ⟨?_, frame.consumed⟩
  intro notice member
  change .groupFailure notice ∈ (buffer.pending ++ [callback]).map BufferedCallback.event
    at member
  rw [List.map_append, List.map_singleton] at member
  rcases List.mem_append.mp member with old | latest
  · exact frame.pending notice old
  · exact List.mem_singleton.mp latest ▸ accepted

/-- Original source freshness prevents a consumed prefix from stealing a pending head. -/
theorem CallbackBuffer.ControlFrame.reduce {work initial buffer}
    (frame : CallbackBuffer.ControlFrame initial buffer)
    (tasks : CallbackBuffer.TaskFrame work initial buffer)
    (front rest : List BufferedCallback) (fifo : buffer.pending = front ++ rest)
    : CallbackBuffer.ControlFrame initial (buffer.reduce front rest) := by
  let batch := front.map BufferedCallback.event
  have active : ∀ notice, .groupFailure notice ∈ batch
      → buffer.queue.acceptsGraphEvent (.groupFailure notice) = true := by
    intro notice member
    apply frame.pending notice
    rw [fifo, List.map_append]
    exact List.mem_append_left _ member
  refine ⟨?_, ?_⟩
  · intro notice member
    change .groupFailure notice ∈ rest.map BufferedCallback.event at member
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have laws := tasks.valid.atPrefix
      (before := buffer.rawBatches.flatten ++ (batch ++ earlier))
      (event := .groupFailure notice)
      ⟨later, by
        rw [fifo, List.map_append, split]
        simp only [batch, List.append_assoc, List.singleton_append]⟩
    apply buffer.queue.handleGraphEvents_preserves_control batch notice
    · apply frame.pending notice
      rw [fifo, List.map_append]
      exact List.mem_append_right _ member
    · intro closed
      exact laws.2.1.2.2.2 notice.group.ref (List.mem_singleton_self _)
        (by
          simp only [List.flatMap_append]
          exact List.mem_append_right _ (List.mem_append_left _ closed))
  · have raw : (buffer.reduce front rest).rawBatches = buffer.rawBatches ++ [batch] := by
      simp only [CallbackBuffer.reduce, CallbackBuffer.rawBatches, List.map_append,
        List.map_singleton]
      rfl
    rw [raw]
    apply AvailableControlBatches.append initial buffer.rawBatches [batch] frame.consumed
    rw [← tasks.current]
    exact ⟨active, True.intro⟩

/-- The unchanged enqueue/reduction relation derives control permission at every boundary. -/
theorem CallbackHistory.controlFrame {work initial buffer}
    (history : CallbackHistory work initial buffer)
    (metadata : initial.CallbackTaskFrame work [])
    : CallbackBuffer.ControlFrame initial buffer := by
  induction history with
  | initial => exact ⟨by simp, True.intro⟩
  | enqueue history callback running started receiptFresh matching fresh ready ih =>
      exact ih.enqueue callback started
  | reduce history front rest fifo ih =>
      exact ih.reduce (history.taskFrame metadata) front rest fifo

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
