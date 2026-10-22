import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection

/-! The actual live dispatch bridge over valid accepted generated source prefixes. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- An uninterrupted state is its exact shared kernel with the running guard. -/
theorem State.eq_queue_of_running (state : State) (running : state.stopped = false)
    : state = { queue := state.queue } := by
  cases state with
  | mk queue stopped =>
      change stopped = false at running
      subst stopped
      rfl

-----------------------------------------------------------------------------------------
-- The reader guard is invariant during a single live graph dispatch
-----------------------------------------------------------------------------------------

/-- Successful task registration/settlement never retires or reopens the graph reader. -/
theorem State.taskSuccess_stopped (state : State)
    (occurrence : WorkQueueSemantics.Occurrence) (result : ReferenceWorkQueue.TaskResult)
    : (state.taskSuccess occurrence result).1.stopped = state.stopped := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskSuccess, found]
  | some node =>
      rw [state.taskSuccess_eq occurrence result node found]
      dsimp only
      rw [State.drainReadyGroups_stopped, State.startNewWork_stopped]
      exact State.maybeIntegrateWork_stopped
        { state with queue := state.queue.putTaskNode { node with value := some result.value } }
        result.work (some occurrence)

/-- A stream receipt's actual item fold preserves the reader guard, including ignored input. -/
theorem State.streamItems_stopped (state : State) (stream : Execution.DeliveryNode)
    (items : List ReferenceWorkQueue.StreamItem)
    : (state.streamItems stream items).1.stopped = state.stopped := by
  have loop (items : List ReferenceWorkQueue.StreamItem) (acc : StreamRegistrationAcc)
      : (items.foldl streamRegistrationStep acc).1.stopped = acc.1.stopped := by
    induction items generalizing acc with
    | nil => rfl
    | cons item rest ih => rw [List.foldl_cons, ih, streamRegistrationStep_stopped]
  unfold State.streamItems
  split
  · rfl
  · rw [State.drainReadyGroups_stopped]
    change (items.foldl streamRegistrationStep (state, [], [], [], [], [])).1.stopped = state.stopped
    exact loop items (state, [], [], [], [], [])

/-- Single graph dispatch only changes queue accounting and its inline observations. -/
theorem State.handleGraphEvent_stopped (state : State) (event : GraphEvent)
    : (state.handleGraphEvent event).1.stopped = state.stopped := by
  cases event with
  | taskSuccess occurrence result => exact state.taskSuccess_stopped occurrence result
  | streamItems stream items => exact state.streamItems_stopped stream items
  | taskFailure occurrence errors => exact state.taskFailure_stopped occurrence errors
  | streamSuccess | streamFailure => rfl

-----------------------------------------------------------------------------------------
-- The source contract supplies every live-handler bridge premise
-----------------------------------------------------------------------------------------

/-- Actual graph dispatch equals the reference accounting/events at every valid accepted prefix.
Witness: task success uses the derived all-owner debt, stream receipts use generated phase
frames, and the other handlers are shared literally. Inline host effects remain distinct.
-/
theorem referencePrefix_handleGraphEvent {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (event : GraphEvent)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (events ++ [event]))
    (accepted
      : (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
          events
        = true)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let alternative := ({ queue } : State).handleGraphEvent event
      (alternative.1.queue, alternative.2.1) = queue.handleGraphEvent event := by
  cases event with
  | taskSuccess occurrence result =>
      exact referencePrefix_taskSuccess generated events occurrence result valid accepted
  | streamItems stream items =>
      obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
      exact referencePrefix_streamItems generated events (fun event member => prior.eachMatches member)
        prior accepted stream items matched
  | taskFailure occurrence errors =>
      obtain ⟨prior, _, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
      obtain ⟨parents, forest⟩ := referencePrefix_removalForest generated events
        (fun _ member => prior.eachMatches member)
      exact State.taskFailure_projection
        (generated.replayGraphEvents_taskOwnerFrame events prior accepted) forest occurrence errors
  | streamSuccess | streamFailure => rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
