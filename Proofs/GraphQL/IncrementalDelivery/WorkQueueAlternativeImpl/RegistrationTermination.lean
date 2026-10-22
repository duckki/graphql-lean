import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationHostEffects
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationDispatch
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationShape

/-! Literal lifecycle-flag preservation, independent of generated replay equivalence.
Abrupt cancel remains distinct from semantic termination; only initialized batch replay
maintains their equality. No source, acquisition or callback assumption is needed here.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Registration, delayed activation and individual inputs cannot terminate work
-----------------------------------------------------------------------------------------

/-- Scope registration changes no semantic termination flag. -/
theorem State.maybeIntegrateWork_terminated (state : State)
    (work : ReferenceWorkQueue.Work) (producer : Option Occurrence := none)
    : (state.maybeIntegrateWork work producer).1.queue.terminated
      = state.queue.terminated := by
  have flag := congrArg ReferenceWorkQueue.State.terminated
    (state.maybeIntegrateWork_registrationCore work producer)
  exact flag.trans (ReferenceWorkQueue.State.maybeIntegrateWork_terminated _ work producer)

/-- Actual per-item integration retains the incoming semantic flag. -/
theorem streamRegistrationStep_terminated (acc : StreamRegistrationAcc)
    (item : ReferenceWorkQueue.StreamItem)
    : (streamRegistrationStep acc item).1.queue.terminated = acc.1.queue.terminated := by
  change (({ (acc.1.maybeIntegrateWork item.work).1 with queue :=
    ((acc.1.maybeIntegrateWork item.work).1.queue.pruneEmptyGroups
      (acc.1.maybeIntegrateWork item.work).2.newGroups).1 }).startNewWork _ _ _).1.queue.terminated = _
  rw [State.startNewWork_terminated _ _ _ acc.2.2.2.2.1, ReferenceWorkQueue.State.pruneEmptyGroups_terminated,
    State.maybeIntegrateWork_terminated]

/-- An actual receipt terminates only at the enclosing batch boundary, not an item. -/
theorem State.streamItems_terminated (state : State) (stream : Execution.DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    : (state.streamItems stream items).1.queue.terminated = state.queue.terminated := by
  unfold State.streamItems
  split
  · rfl
  · rw [State.drainReadyGroups_terminated]
    exact ReferenceWorkQueue.fold_projection (fun acc : StreamRegistrationAcc => acc.1.queue.terminated)
      streamRegistrationStep streamRegistrationStep_terminated _ _

/-- Actual object registration, owner settlement and draining retain the semantic flag. -/
theorem State.taskSuccess_terminated (state : State) (occurrence : Occurrence)
    (result : ReferenceWorkQueue.TaskResult)
    : (state.taskSuccess occurrence result).1.queue.terminated
      = state.queue.terminated := by
  have step (acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork)
      (group : Execution.DeliveryNode)
      : (ReferenceWorkQueue.successGroupStep acc group).1.terminated = acc.1.terminated := by
    obtain ⟨queue, events, roots⟩ := acc
    dsimp only [ReferenceWorkQueue.successGroupStep]
    split
    · rfl
    · split
      · exact ReferenceWorkQueue.State.finishGroupSuccess_terminated _ _
      · rfl
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found]
      dsimp only
      rw [State.drainReadyGroups_terminated, State.startNewWork_terminated,
        ReferenceWorkQueue.fold_projection
          (fun acc : ReferenceWorkQueue.State × List WorkQueueEvent × ReferenceWorkQueue.NewWork => acc.1.terminated)
          ReferenceWorkQueue.successGroupStep step,
        State.maybeIntegrateWork_terminated _ result.work (some occurrence)]
      rfl

/-- All five actual handlers preserve semantic termination, even on malformed raw input. -/
theorem State.handleGraphEvent_terminated (state : State) (event : GraphEvent)
    : (state.handleGraphEvent event).1.queue.terminated = state.queue.terminated := by
  cases event with
  | taskSuccess occurrence result => exact state.taskSuccess_terminated occurrence result
  | streamItems stream items => exact state.streamItems_terminated stream items
  | taskFailure occurrence errors =>
      exact state.taskFailure_terminated occurrence errors
  | streamSuccess stream =>
      simp only [State.handleGraphEvent]
      exact state.queue.handleGraphEvent_terminated (.streamSuccess stream)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent]
      exact state.queue.handleGraphEvent_terminated (.streamFailure stream errors)

-----------------------------------------------------------------------------------------
-- Only batch completion aligns semantic termination and reader retirement
-----------------------------------------------------------------------------------------

/-- A batch preserves aligned flags; explicit cancellation outside replay is not covered. -/
theorem State.handleGraphEvents_flagsAligned (state : State) (batch : List GraphEvent)
    (aligned : state.stopped = state.queue.terminated)
    : (state.handleGraphEvents batch).state.stopped
      = (state.handleGraphEvents batch).state.queue.terminated := by
  have loop (events : List GraphEvent) (acc : GraphBatchResult)
      (same : acc.state.stopped = acc.state.queue.terminated)
      : (events.foldl GraphBatchResult.handleGraphEvent acc).state.stopped
        = (events.foldl GraphBatchResult.handleGraphEvent acc).state.queue.terminated := by
    induction events generalizing acc with
    | nil => exact same
    | cons event rest ih =>
        apply ih
        change (acc.state.handleGraphEvent event).1.stopped
          = (acc.state.handleGraphEvent event).1.queue.terminated
        rw [State.handleGraphEvent_stopped, State.handleGraphEvent_terminated]
        exact same
  unfold State.handleGraphEvents
  split
  · exact aligned
  · dsimp only
    split
    · rw [State.cancel_stopped, State.cancel_terminated]
    · exact loop batch { state } aligned

/-- Actual normalization retains aligned flags for every finite input sequence. -/
theorem State.runNormalized_flagsAligned (state : State) (inputs : List (List GraphEvent))
    (aligned : state.stopped = state.queue.terminated)
    : (state.runNormalized inputs).1.stopped
      = (state.runNormalized inputs).1.queue.terminated := by
  let step (acc : State × ReferenceWorkQueue.IncrementalPublisher × List (List WorkQueueEvent))
      (batch : List GraphEvent) :=
    let next := acc.1.handleGraphEvents batch
    if next.workQueueEvents.isEmpty then (next.state, acc.2.1, acc.2.2)
    else
      let mapped := acc.2.1.normalizeBatch next.workQueueEvents
      (next.state, mapped.1, acc.2.2 ++ [mapped.2])
  have loop (more : List (List GraphEvent)) (acc)
      (same : acc.1.stopped = acc.1.queue.terminated)
      : (more.foldl step acc).1.stopped = (more.foldl step acc).1.queue.terminated := by
    induction more generalizing acc with
    | nil => exact same
    | cons batch rest ih =>
        apply ih
        unfold step
        dsimp only
        split <;> exact State.handleGraphEvents_flagsAligned _ batch same
  exact loop inputs
    (state, { active := state.queue.initialGroups ++ state.queue.initialStreams }, [])
    aligned

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
