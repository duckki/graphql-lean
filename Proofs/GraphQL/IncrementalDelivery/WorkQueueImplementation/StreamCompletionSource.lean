import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions

/-! Every emitted stream completion retains its exact source settlement and error count. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Retain a source stream completion, including whether it succeeds or its failure count.
Task settlements and item arrivals are omitted by this proof-only projection.
-/
def GraphEvent.streamCompletion : GraphEvent → Option GraphEvent
  | .streamSuccess stream => some (.streamSuccess stream)
  | .streamFailure stream errors => some (.streamFailure stream errors)
  | _ => none

/-- Recover the source-shaped stream completion from a raw queue event. -/
def _root_.GraphQL.IncrementalDelivery.Execution.WorkQueueEvent.streamCompletion
    : WorkQueueEvent → Option GraphEvent
  | .streamSuccess stream => some (.streamSuccess stream)
  | .streamFailure stream errors => some (.streamFailure stream errors)
  | _ => none

/-- Recover the source-shaped stream completion from a normalized work event. -/
def streamCompletion : Execution.WorkQueueEvent → Option GraphEvent
  | .streamSuccess stream => some (.streamSuccess stream)
  | .streamFailure stream errors => some (.streamFailure stream errors)
  | _ => none

-----------------------------------------------------------------------------------------
-- Guarded handlers and batching preserve an exact source-completion subsequence
-----------------------------------------------------------------------------------------

/-- Without raw stream references there can be no raw stream completion.
Witness: every retained completion has a reference ref in its original event.
-/
theorem no_streamCompletions_of_no_references {events : List WorkQueueEvent}
    (empty : events.flatMap rawStreamReferenceRefs = [])
    : events.filterMap WorkQueueEvent.streamCompletion = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro event member
  have references : rawStreamReferenceRefs event = [] :=
    List.flatMap_eq_nil_iff.mp empty event member
  cases event <;> simp_all [rawStreamReferenceRefs, WorkQueueEvent.streamCompletion]

/-- A release-time drain emits no stream completion, even when it releases failed groups.
Witness: its group-only output has no stream reference from which to recover a completion.
-/
theorem State.drainReadyGroups_streamCompletions (queue : State)
    : queue.drainReadyGroups.2.filterMap WorkQueueEvent.streamCompletion = [] :=
  no_streamCompletions_of_no_references queue.drainReadyGroups_streamReferences

/-- Each handler emits only its own exact stream completion, or none.
Witness: task handlers have no stream references; guarded stream closures copy their
node and error count, while item arrival emits no completion.
-/
theorem State.handleGraphEvent_streamCompletions (queue : State) (event : GraphEvent)
    : ((queue.handleGraphEvent event).2.filterMap WorkQueueEvent.streamCompletion).Sublist
        event.streamCompletion.toList := by
  cases event with
  | taskSuccess occurrence result =>
      rw [State.handleGraphEvent, no_streamCompletions_of_no_references
        (queue.taskSuccess_streamReferences occurrence result)]
      exact List.nil_sublist _
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, no_streamCompletions_of_no_references
        (queue.taskFailure_streamReferences occurrence errors)]
      exact List.nil_sublist _
  | streamItems stream items =>
      simp only [State.handleGraphEvent, State.streamItems]
      split <;> simp [WorkQueueEvent.streamCompletion, GraphEvent.streamCompletion,
        List.filterMap_cons, State.drainReadyGroups_streamCompletions]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [WorkQueueEvent.streamCompletion, GraphEvent.streamCompletion]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [WorkQueueEvent.streamCompletion, GraphEvent.streamCompletion]

/-- Eventwise replay retains a subsequence of exact source stream completions.
Witness: append the corresponding per-handler subsequences in execution order.
-/
theorem State.rawEventReplay_streamCompletions (queue : State) (events : List GraphEvent)
    : ((queue.rawEventReplay events).2.filterMap WorkQueueEvent.streamCompletion).Sublist
        (events.filterMap GraphEvent.streamCompletion) := by
  induction events generalizing queue with
  | nil => exact .refl _
  | cons event rest ih =>
      rw [State.rawEventReplay_cons, List.filterMap_append]
      have combined := (queue.handleGraphEvent_streamCompletions event).append
        (ih (queue.handleGraphEvent event).1)
      cases event <;> simpa [List.filterMap_cons, GraphEvent.streamCompletion] using combined

/-- The batch wrapper creates no stream completion independently of the source.
Witness: ignored batches are empty, and queue termination adds no stream completion.
-/
theorem State.handleGraphEvents_streamCompletions (queue : State)
    (events : List GraphEvent)
    : ((queue.handleGraphEvents events).2.filterMap
        WorkQueueEvent.streamCompletion).Sublist
        (events.filterMap GraphEvent.streamCompletion) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact List.nil_sublist _
  · dsimp only
    split
    · simpa [List.filterMap_append, List.filterMap_cons, WorkQueueEvent.streamCompletion]
        using queue.rawEventReplay_streamCompletions events
    · exact queue.rawEventReplay_streamCompletions events

-----------------------------------------------------------------------------------------
-- Normalization and atomic expansion preserve the completion constructor and descriptor
-----------------------------------------------------------------------------------------

/-- The publisher copies every stream completion's descriptor, outcome kind, and error count.
Witness: successful/failed closures remain singletons; other constructors contribute none.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_streamCompletion
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : (publisher.handleWorkQueueEvent event).2.filterMap streamCompletion
      = event.streamCompletion.toList := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent, streamCompletion,
    WorkQueueEvent.streamCompletion, List.filterMap_map, List.filterMap_cons, Function.comp_def]

/-- Batch normalization preserves the exact stream-completion sequence.
Witness: compose one-event preservation through the publisher's actual fold.
-/
theorem IncrementalPublisher.normalizeBatch_streamCompletions
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : (publisher.normalizeBatch events).2.filterMap streamCompletion
      = events.filterMap WorkQueueEvent.streamCompletion := by
  induction events generalizing publisher with
  | nil => rfl
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons, List.filterMap_append,
        publisher.handleWorkQueueEvent_streamCompletion, ih]
      cases event <;> simp [List.filterMap_cons, WorkQueueEvent.streamCompletion]

/-- Each normalized runner step appends exactly its raw stream completions.
Witness: empty output is omitted; nonempty output retains its completion projection.
-/
theorem normalizedStep_streamCompletions (acc : NormalizedAcc) (batch : List GraphEvent)
    : (normalizedStep acc batch).2.2.flatten.filterMap streamCompletion
      = acc.2.2.flatten.filterMap streamCompletion
        ++ (acc.1.handleGraphEvents batch).2.filterMap
            WorkQueueEvent.streamCompletion := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  dsimp only [normalizedStep]
  split
  · rename_i empty
    rw [List.isEmpty_iff.mp empty]
    simp
  · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.filterMap_append, IncrementalPublisher.normalizeBatch_streamCompletions]

/-- Actual normalized stream completions retain their original source settlement in order.
Witness: real handler/batch subsequences and publisher preservation. No source-validity,
generated-work, or start assumption is used by this structural correspondence.
-/
theorem createWorkQueue_runNormalized_streamCompletions (work : Work)
    (batches : List (List GraphEvent))
    : (((State.initialize work).runNormalized batches).2.flatten.filterMap
        streamCompletion).Sublist
        (batches.flatten.filterMap GraphEvent.streamCompletion) := by
  have loop (more : List (List GraphEvent)) (acc : NormalizedAcc)
      : ((more.foldl normalizedStep acc).2.2.flatten.filterMap streamCompletion).Sublist
          (acc.2.2.flatten.filterMap streamCompletion
            ++ more.flatten.filterMap GraphEvent.streamCompletion) := by
    induction more generalizing acc with
    | nil => simp
    | cons batch rest ih =>
        rw [List.foldl_cons]
        have later := ih (normalizedStep acc batch)
        rw [normalizedStep_streamCompletions] at later
        have included := ((List.Sublist.refl (acc.2.2.flatten.filterMap streamCompletion)).append
          (acc.1.handleGraphEvents_streamCompletions batch)).append
          (.refl (rest.flatten.filterMap GraphEvent.streamCompletion))
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

/-- Value atomization leaves the exact stream-completion projection unchanged.
Witness: splitting values produces no closure and each control constructor stays put.
-/
theorem publicationAtoms_streamCompletions (event : Execution.WorkQueueEvent)
    : (publicationAtoms event).filterMap streamCompletion
      = (streamCompletion event).toList := by
  cases event with
  | groupValues =>
      simp [publicationAtoms, List.filterMap_map, streamCompletion, Function.comp_def]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => rfl
      | case2 => rfl
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, List.filterMap_cons,
            streamCompletion]
            using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      rfl

/-- Each actual atomic completion has its exact successful/failed source settlement.
Witness: atomization preserves the completion projection, which is a source subsequence.
-/
theorem createWorkQueue_runNormalized_streamCompletion_source (work : Work)
    (batches : List (List GraphEvent)) {event completion}
    (emitted
      : event
        ∈ ((State.initialize work).runNormalized batches).2.flatten.flatMap
            publicationAtoms)
    (selected : streamCompletion event = some completion)
    : completion ∈ batches.flatten := by
  obtain ⟨original, member, within⟩ := List.mem_flatMap.mp emitted
  have inAtoms := List.mem_filterMap.mpr ⟨event, within, selected⟩
  rw [publicationAtoms_streamCompletions] at inAtoms
  have originalSelected : streamCompletion original = some completion := by
    simpa using inAtoms
  have inSource := (createWorkQueue_runNormalized_streamCompletions work batches).subset
    (List.mem_filterMap.mpr ⟨original, member, originalSelected⟩)
  obtain ⟨source, member, same⟩ := List.mem_filterMap.mp inSource
  cases source <;> simp_all [GraphEvent.streamCompletion]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
