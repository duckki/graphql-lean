import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStreamRoots
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackTaskHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationReplay

/-! Enqueue-time stream permission survives pending FIFO reductions. Stream activation is
proved at each batch entry, independently of task retirement and callback projection.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open ReferenceWorkQueue (StreamAction)

/-- Every stream action in each consumed batch is active at that batch's initial boundary. -/
def AvailableStreamBatches (queue : ReferenceWorkQueue.State)
    : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∀ event ∈ batch,
        ∀ action, event.streamAction = some action → queue.acceptsGraphEvent event = true)
      ∧ AvailableStreamBatches (queue.handleGraphEvents batch).1 rest

/-- Entry-time stream activation composes across actual batch boundaries. -/
theorem AvailableStreamBatches.append (queue : ReferenceWorkQueue.State)
    (before after : List (List GraphEvent))
    (earlier : AvailableStreamBatches queue before)
    (later : AvailableStreamBatches (queue.replayBatches before) after)
    : AvailableStreamBatches queue (before ++ after) := by
  induction before generalizing queue with
  | nil => exact later
  | cons batch rest ih => exact ⟨earlier.1, ih _ earlier.2 later⟩

/-- Pending streams remain active, and consumed batches carry entry-time activation. -/
structure CallbackBuffer.StreamFrame (initial : ReferenceWorkQueue.State)
    (buffer : CallbackBuffer)
    : Prop where
  pending
    : ∀ event ∈ buffer.pending.map BufferedCallback.event,
        ∀ action,
          event.streamAction = some action → buffer.queue.acceptsGraphEvent event = true
  consumed : AvailableStreamBatches initial buffer.rawBatches

/-- Current enqueue permission supplies the new pending stream's activation. -/
theorem CallbackBuffer.StreamFrame.enqueue {initial buffer}
    (frame : CallbackBuffer.StreamFrame initial buffer) (callback : BufferedCallback)
    (accepted : buffer.queue.acceptsGraphEvent callback.event = true)
    : CallbackBuffer.StreamFrame initial (buffer.enqueue callback) := by
  refine ⟨?_, frame.consumed⟩
  intro event member action source
  change event ∈ (buffer.pending ++ [callback]).map BufferedCallback.event at member
  rw [List.map_append, List.map_singleton] at member
  rcases List.mem_append.mp member with old | latest
  · exact frame.pending event old action source
  · have same := List.mem_singleton.mp latest
    exact same ▸ accepted

private theorem unclosed_of_sublist {before events : List GraphEvent} {key : Nat}
    (unclosed : key ∉ before.flatMap (fun prior => prior.identities.2))
    (included : events.Sublist before)
    : key ∉ events.flatMap (fun prior => prior.identities.2) := by
  intro closed
  obtain ⟨event, member, same⟩ := List.mem_flatMap.mp closed
  exact unclosed (List.mem_flatMap.mpr ⟨event, included.subset member, same⟩)

/-- Freshness/readiness prohibit a stream closure before any pending action on that stream. -/
theorem CallbackBuffer.StreamFrame.reduce {work initial buffer}
    (frame : CallbackBuffer.StreamFrame initial buffer)
    (tasks : CallbackBuffer.TaskFrame work initial buffer)
    (front rest : List BufferedCallback) (fifo : buffer.pending = front ++ rest)
    : CallbackBuffer.StreamFrame initial (buffer.reduce front rest) := by
  let batch := front.map BufferedCallback.event
  have frontMember : ∀ event ∈ batch, event ∈ buffer.pending.map BufferedCallback.event := by
    intro event member
    rw [fifo, List.map_append]
    exact List.mem_append_left _ member
  have active : ∀ event ∈ batch, ∀ action, event.streamAction = some action
      → buffer.queue.acceptsGraphEvent event = true :=
    fun event member action source => frame.pending event (frontMember event member) action source
  refine ⟨?_, ?_⟩
  · intro event member action source
    change event ∈ rest.map BufferedCallback.event at member
    obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp member
    have laws := tasks.valid.atPrefix
      (before := buffer.rawBatches.flatten ++ (batch ++ earlier)) (event := event)
      ⟨later, by
        rw [fifo, List.map_append, split]
        simp only [batch, List.append_assoc, List.singleton_append]⟩
    have previous := frame.pending event
      (by rw [fifo, List.map_append]; exact List.mem_append_right _ member) action source
    apply (streamAction_accepts_iff _ _ _ source).mpr
    apply rootStream_survives_batch buffer.queue batch action.1
      ((streamAction_accepts_iff _ _ _ source).mp previous)
    apply unclosed_of_sublist (streamAction_unclosed laws.2.1 laws.2.2 source)
    exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  · have raw : (buffer.reduce front rest).rawBatches = buffer.rawBatches ++ [batch] := by
      simp only [CallbackBuffer.reduce, CallbackBuffer.rawBatches, List.map_append,
        List.map_singleton]
      rfl
    rw [raw]
    apply AvailableStreamBatches.append initial buffer.rawBatches [batch] frame.consumed
    rw [← tasks.current]
    exact ⟨active, True.intro⟩

/-- Derive stream activation from the original interleaved history, without restricting
batch width or requiring every pending callback to be reduced together.
-/
theorem CallbackHistory.streamFrame {work initial buffer}
    (history : CallbackHistory work initial buffer)
    (metadata : initial.CallbackTaskFrame work [])
    : CallbackBuffer.StreamFrame initial buffer := by
  induction history with
  | initial => exact ⟨by simp, True.intro⟩
  | enqueue history callback running started receiptFresh matching fresh ready ih =>
      exact ih.enqueue callback started
  | reduce history front rest fifo ih =>
      exact ih.reduce (history.taskFrame metadata) front rest fifo

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
