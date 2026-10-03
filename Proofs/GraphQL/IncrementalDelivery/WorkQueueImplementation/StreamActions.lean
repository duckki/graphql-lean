import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferenceAtoms

/-! The stream-reference/closure projection of output is an ordered source subsequence. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A proof-only stream action contains its ref and whether this action closes the stream.
Items use false; successful and failed closure use true. Payloads and notices are omitted.
-/
abbrev StreamAction := Nat × Bool

/-- Source stream actions; task settlements do not reference or close streams. -/
def GraphEvent.streamAction : GraphEvent → Option StreamAction
  | .streamItems stream _ => some (stream.ref, false)
  | .streamSuccess stream | .streamFailure stream _ => some (stream.ref, true)
  | _ => none

/-- Raw stream actions; group events and queue termination have no stream action. -/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.streamAction
    : WorkQueueEvent → Option StreamAction
  | .streamValues stream _ _ _ => some (stream.ref, false)
  | .streamSuccess stream | .streamFailure stream _ => some (stream.ref, true)
  | _ => none

/-- Normalized stream actions, before expanding a multi-item publication into atoms. -/
def streamAction : Execution.WorkQueueEvent → Option StreamAction
  | .streamValues stream _ _ _ => some (stream.ref, false)
  | .streamSuccess stream | .streamFailure stream _ => some (stream.ref, true)
  | _ => none

-----------------------------------------------------------------------------------------
-- Raw replay may ignore an input, but cannot introduce or reorder stream actions
-----------------------------------------------------------------------------------------

/-- Raw stream actions have exactly the previously defined stream-reference refs.
Witness: each value/closure contributes one ref; all other events contribute neither.
-/
theorem rawStreamActions_refs (events : List WorkQueueEvent)
    : (events.filterMap WorkQueueEvent.streamAction).map Prod.fst
      = events.flatMap rawStreamReferenceRefs := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [List.filterMap_cons, WorkQueueEvent.streamAction,
        rawStreamReferenceRefs, ih]

/-- Recursive draining has no stream action: it emits only group values and group closures.
Witness: the action-ref projection agrees with the drain's empty stream-reference list.
-/
theorem State.drainReadyGroups_streamActions (queue : State)
    : queue.drainReadyGroups.2.filterMap WorkQueueEvent.streamAction = [] := by
  apply List.map_eq_nil_iff.mp
  rw [rawStreamActions_refs, State.drainReadyGroups_streamReferences]

/-- A handler emits at most its input's one stream action, with the same ref and closure flag.
Witness: task handlers emit no stream references; guarded stream handlers copy one action
or ignore the input. No start or payload premise is needed for this projection.
-/
theorem State.handleGraphEvent_streamActions (queue : State) (event : GraphEvent)
    : ((queue.handleGraphEvent event).2.filterMap WorkQueueEvent.streamAction).Sublist
        event.streamAction.toList := by
  cases event with
  | taskSuccess occurrence result =>
      have empty : (queue.taskSuccess occurrence result).2.filterMap
          WorkQueueEvent.streamAction = [] := by
        apply List.map_eq_nil_iff.mp
        rw [rawStreamActions_refs, queue.taskSuccess_streamReferences]
      rw [State.handleGraphEvent, empty]
      exact List.nil_sublist _
  | taskFailure occurrence errors =>
      have empty : (queue.taskFailure occurrence errors).2.filterMap
          WorkQueueEvent.streamAction = [] := by
        apply List.map_eq_nil_iff.mp
        rw [rawStreamActions_refs, queue.taskFailure_streamReferences]
      rw [State.handleGraphEvent, empty]
      exact List.nil_sublist _
  | streamItems stream items =>
      simp only [State.handleGraphEvent, State.streamItems]
      split <;> simp [WorkQueueEvent.streamAction, GraphEvent.streamAction,
        State.drainReadyGroups_streamActions]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.streamAction, GraphEvent.streamAction]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.streamAction, GraphEvent.streamAction]

/-- Raw eventwise replay preserves stream actions as an ordered source subsequence.
Witness: concatenate each handler's optional action in the actual replay order.
-/
theorem State.rawEventReplay_streamActions (queue : State) (events : List GraphEvent)
    : ((queue.rawEventReplay events).2.filterMap WorkQueueEvent.streamAction).Sublist
        (events.filterMap GraphEvent.streamAction) := by
  induction events generalizing queue with
  | nil => exact .refl _
  | cons event rest ih =>
      rw [State.rawEventReplay_cons, List.filterMap_append]
      have combined := (queue.handleGraphEvent_streamActions event).append
        (ih (queue.handleGraphEvent event).1)
      cases event <;> simpa [List.filterMap_cons, GraphEvent.streamAction] using combined

/-- The batch wrapper can suppress stream actions but cannot create or reorder them.
Witness: terminated batches are ignored; appending termination adds no stream action.
-/
theorem State.handleGraphEvents_streamActions (queue : State) (events : List GraphEvent)
    : ((queue.handleGraphEvents events).2.filterMap WorkQueueEvent.streamAction).Sublist
        (events.filterMap GraphEvent.streamAction) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact List.nil_sublist _
  · dsimp only
    split
    · simpa [List.filterMap_append, List.filterMap_cons, WorkQueueEvent.streamAction]
        using queue.rawEventReplay_streamActions events
    · exact queue.rawEventReplay_streamActions events

-----------------------------------------------------------------------------------------
-- Publisher normalization preserves the raw action projection exactly
-----------------------------------------------------------------------------------------

/-- Normalizing one raw event preserves its stream action exactly.
Witness: only group values expand, and their atoms have no stream action.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamAction
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.filterMap streamAction
      = event.streamAction.toList := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, streamAction,
    WorkQueueEvent.streamAction, List.filterMap_map]

/-- Normalizing a raw batch retains exactly its ordered stream actions.
Witness: append the preserved action at each step of the publisher's real fold.
-/
theorem IncrementalPublisher.normalizeBatch_streamActions
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.filterMap streamAction
      = events.filterMap WorkQueueEvent.streamAction := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons, List.filterMap_append,
        publisher.handleWorkQueueEvent_streamAction, ih]
      cases event <;> simp [List.filterMap_cons, WorkQueueEvent.streamAction]

/-- A normalized runner step appends precisely its raw batch's stream-action projection.
Witness: empty batches append nothing, and nonempty batches preserve their actions.
-/
theorem normalizedStep_streamActions (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.2.flatten.filterMap streamAction
      = acc.2.2.flatten.filterMap streamAction
        ++ (acc.1.handleGraphEvents batch).2.filterMap WorkQueueEvent.streamAction := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  dsimp only [normalizedStep]
  split
  · rename_i empty
    rw [List.isEmpty_iff.mp empty]
    simp
  · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.filterMap_append, IncrementalPublisher.normalizeBatch_streamActions]

/-- Actual normalized stream actions form a subsequence of the source's stream actions.
Witness: real batching, handler guards, termination, and publisher normalization preserve
source order. This holds without generated-work, valid-input, or start assumptions.
-/
theorem createWorkQueue_runNormalized_streamActions (work : Work)
    (batches : List (List GraphEvent))
    : (((State.initialize work).runNormalized batches).2.flatten.filterMap
        streamAction).Sublist
        (batches.flatten.filterMap GraphEvent.streamAction) := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      : ((more.foldl normalizedStep acc).2.2.flatten.filterMap streamAction).Sublist
          (acc.2.2.flatten.filterMap streamAction
            ++ more.flatten.filterMap GraphEvent.streamAction) := by
    induction more generalizing acc with
    | nil => simp
    | cons batch rest ih =>
        rw [List.foldl_cons]
        have later := ih (normalizedStep acc batch)
        rw [normalizedStep_streamActions] at later
        have included := ((List.Sublist.refl (acc.2.2.flatten.filterMap streamAction)).append
          (acc.1.handleGraphEvents_streamActions batch)).append
          (.refl (rest.flatten.filterMap GraphEvent.streamAction))
        simpa [List.flatten_cons, List.filterMap_append, List.append_assoc]
          using later.trans included
  exact loop batches
    (
      State.initialize work,
      {
        active :=
          (State.initialize work).initialGroups ++ (State.initialize work).initialStreams
      },
      []
    )

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
