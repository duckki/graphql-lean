import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackTaskFrames

/-! Actual enqueue permission derives task tracking at every consumed batch boundary.
The history relation is unchanged: callbacks may remain pending across arbitrarily many
FIFO reductions and may be consumed after losing their last owner.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open WorkQueueSemantics (Occurrence)

/-- Every task callback in a raw batch was started earlier and remains registered. -/
def TrackedTaskBatch (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : Prop :=
  ∀ event ∈ batch,
    ∀ occurrence,
      event.taskCallback? = some occurrence
      → queue.StartedTaskDisposition occurrence
        ∧ occurrence ∈ queue.tasks.map ReferenceWorkQueue.Task.occurrence

/-- Structural metadata and tracked task callbacks at each actual host batch boundary. -/
def TrackedTaskBatches (work : Work) (queue : ReferenceWorkQueue.State)
    (before : List GraphEvent)
    : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      queue.CallbackTaskFrame work before
      ∧ ReferenceWorkQueue.ValidGraphEvents work (before ++ batch)
      ∧ TrackedTaskBatch queue batch
      ∧ TrackedTaskBatches work (queue.handleGraphEvents batch).1 (before ++ batch) rest

/-- Successive actual batch boundaries compose the same structural tracking history. -/
theorem TrackedTaskBatches.append {work queue before}
    (earlier later : List (List GraphEvent))
    (first : TrackedTaskBatches work queue before earlier)
    (last
      : TrackedTaskBatches work (queue.replayBatches earlier) (before ++ earlier.flatten)
          later)
    : TrackedTaskBatches work queue before (earlier ++ later) := by
  induction earlier generalizing queue before with
  | nil => simpa only [ReferenceWorkQueue.State.replayBatches, List.foldl_nil,
      List.flatten_nil, List.append_nil, List.nil_append] using last
  | cons batch rest ih =>
      refine ⟨first.1, first.2.1, first.2.2.1, ?_⟩
      apply ih first.2.2.2
      simpa only [ReferenceWorkQueue.State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc] using last

/-- The task-only history invariant uses existing graph metadata and original source laws. -/
structure CallbackBuffer.TaskFrame (work : Work) (initial : ReferenceWorkQueue.State)
    (buffer : CallbackBuffer)
    : Prop where
  current : buffer.queue = initial.replayBatches buffer.rawBatches
  valid
    : ReferenceWorkQueue.ValidGraphEvents work
        (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event)
  metadata : buffer.queue.CallbackTaskFrame work buffer.rawBatches.flatten
  pending : TrackedTaskBatch buffer.queue (buffer.pending.map BufferedCallback.event)
  consumed : TrackedTaskBatches work initial [] buffer.rawBatches

/-- A newly enqueued task has a real computation node, not merely historical permission. -/
theorem taskCallback_tracked {work queue before event occurrence}
    (frame : ReferenceWorkQueue.State.CallbackTaskFrame queue work before)
    (accepted : queue.acceptsGraphEvent event = true)
    (callback : event.taskCallback? = some occurrence)
    : queue.StartedTaskDisposition occurrence
      ∧ occurrence ∈ queue.tasks.map ReferenceWorkQueue.Task.occurrence := by
  have present : (queue.taskNode? occurrence).isSome = true := by
    cases event <;> simp only [ReferenceWorkQueue.GraphEvent.taskCallback?, Option.some.injEq,
      reduceCtorEq] at callback
    all_goals subst occurrence; exact accepted
  cases found : queue.taskNode? occurrence with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at present
  | some node =>
      refine ⟨.inl ⟨node, found⟩, ?_⟩
      exact List.mem_map.mpr ⟨node.task, frame.started node (List.mem_of_find?_eq_some found),
        (ReferenceWorkQueue.State.taskNode?_some found).2⟩

/-- Enqueue preserves tracking and extends the one fixed work-valid pending suffix. -/
theorem CallbackBuffer.TaskFrame.enqueue {work initial buffer}
    (frame : CallbackBuffer.TaskFrame work initial buffer) (callback : BufferedCallback)
    (accepted : buffer.queue.acceptsGraphEvent callback.event = true)
    (matching : callback.event.MatchesWork work)
    (fresh
      : callback.event.Fresh
          (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event))
    (ready
      : callback.event.Ready work
          (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event))
    : CallbackBuffer.TaskFrame work initial (buffer.enqueue callback) := by
  refine ⟨frame.current, ?_, frame.metadata, ?_, frame.consumed⟩
  · simpa only [CallbackBuffer.enqueue, CallbackBuffer.rawBatches, List.map_append,
      List.map_singleton, ← List.append_assoc]
      using ReferenceWorkQueue.ValidGraphEvents.append frame.valid matching fresh ready
  · intro event member occurrence identity
    change event ∈ (buffer.pending ++ [callback]).map BufferedCallback.event at member
    rw [List.map_append, List.map_singleton] at member
    rcases List.mem_append.mp member with prior | latest
    · exact frame.pending event prior occurrence identity
    · have same := List.mem_singleton.mp latest
      subst event
      exact taskCallback_tracked frame.metadata accepted identity

/-- FIFO reduction derives the next metadata frame and preserves every pending task's
started disposition; it does not require the consumed callbacks to remain eligible.
-/
theorem CallbackBuffer.TaskFrame.reduce {work initial buffer}
    (frame : CallbackBuffer.TaskFrame work initial buffer)
    (front rest : List BufferedCallback) (fifo : buffer.pending = front ++ rest)
    : CallbackBuffer.TaskFrame work initial (buffer.reduce front rest) := by
  let batch := front.map BufferedCallback.event
  have valid : ReferenceWorkQueue.ValidGraphEvents work (buffer.rawBatches.flatten ++ batch) := by
    apply frame.valid.prefix
    refine ⟨rest.map BufferedCallback.event, ?_⟩
    rw [fifo, List.map_append, List.append_assoc]
  have tracked : TrackedTaskBatch buffer.queue batch := by
    intro event member occurrence identity
    apply frame.pending event _ occurrence identity
    rw [fifo, List.map_append]
    exact List.mem_append_left _ member
  have metadata := frame.metadata.handleGraphEvents batch valid
  have raw : (buffer.reduce front rest).rawBatches = buffer.rawBatches ++ [batch] := by
    simp only [CallbackBuffer.reduce, CallbackBuffer.rawBatches, List.map_append,
      List.map_singleton]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [raw, ReferenceWorkQueue.State.replayBatches, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    change (buffer.queue.handleGraphEvents batch).1
      = ((initial.replayBatches buffer.rawBatches).handleGraphEvents batch).1
    rw [← frame.current]
  · rw [raw, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    simpa only [CallbackBuffer.reduce, fifo, List.map_append, List.append_assoc] using frame.valid
  · rw [raw, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact metadata
  · intro event member occurrence identity
    obtain ⟨disposition, registered⟩ := frame.pending event
      (by rw [fifo, List.map_append]; exact List.mem_append_right _ member) occurrence identity
    exact frame.metadata.startedTask_afterBatch disposition registered batch valid
  · rw [raw]
    apply TrackedTaskBatches.append _ _ frame.consumed
    rw [← frame.current]
    simpa only [TrackedTaskBatches, List.nil_append]
      using And.intro frame.metadata (And.intro valid (And.intro tracked True.intro))

/-- Derive every consumed task boundary from the original interleaved callback history. -/
theorem CallbackHistory.taskFrame {work initial buffer}
    (history : CallbackHistory work initial buffer)
    (metadata : initial.CallbackTaskFrame work [])
    : CallbackBuffer.TaskFrame work initial buffer := by
  induction history with
  | initial => exact ⟨rfl, .nil, metadata, by simp [TrackedTaskBatch], True.intro⟩
  | enqueue history callback running started receiptFresh matching fresh ready ih =>
      exact ih.enqueue callback started matching fresh ready
  | reduce history front rest fifo ih => exact ih.reduce front rest fifo

/-- An enqueued callback whose computation is now missing has globally retired memberships.
Historical enqueue permission is evidence, not a renewed executable acceptance guard.
-/
theorem TrackedTaskBatch.retired_of_ineligible {queue batch event occurrence}
    (tracked : TrackedTaskBatch queue batch) (member : event ∈ batch)
    (identity : event.taskCallback? = some occurrence)
    (stale : queue.acceptsGraphEvent event = false)
    : queue.RetiredTask occurrence
      ∧ occurrence ∈ queue.tasks.map ReferenceWorkQueue.Task.occurrence := by
  obtain ⟨disposition, registered⟩ := tracked event member occurrence identity
  have missing : queue.taskNode? occurrence = none := by
    have notStarted : (queue.taskNode? occurrence).isSome = false := by
      cases event <;> simp only [ReferenceWorkQueue.GraphEvent.taskCallback?, Option.some.injEq,
        reduceCtorEq] at identity
      all_goals subst occurrence; exact stale
    cases found : queue.taskNode? occurrence with
    | none => rfl
    | some node => simp only [found, Option.isSome_some, Bool.true_eq_false] at notStarted
  exact ⟨disposition.retired missing, registered⟩

/-- Actual interleaved enqueue histories derive task tracking at all consumed boundaries. -/
theorem CallbackHistory.trackedTaskBatches {work buffer}
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) buffer)
    : TrackedTaskBatches work
        (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
        [] buffer.rawBatches :=
  (history.taskFrame (ReferenceWorkQueue.createWorkQueue_callbackTaskFrame work)).consumed

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
