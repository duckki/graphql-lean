import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GraphEffectProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay

/-! Ineligible callbacks at an empty cache snapshot preserve the semantic queue.
Their item receipts retain their own inline acknowledgements.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Losing live membership makes every shared handler a literal no-op. -/
theorem stale_handleGraphEvent (queue : ReferenceWorkQueue.State) (event : GraphEvent)
    (stale : queue.acceptsGraphEvent event = false)
    : queue.handleGraphEvent event = (queue, [], []) := by
  cases event with
  | taskSuccess task result =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, ReferenceWorkQueue.State.taskSuccess,
        absent]
  | taskFailure task errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, ReferenceWorkQueue.State.taskFailure,
        absent]
  | streamItems stream items =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.streamItems,
        stale, Bool.not_false, ↓reduceIte]
  | streamSuccess stream =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.streamSuccess,
        stale, Bool.false_eq_true, ↓reduceIte]
  | streamFailure stream errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
        ReferenceWorkQueue.State.streamFailure,
        stale, Bool.false_eq_true, ↓reduceIte]
  | groupFailure notice =>
      cases pending : queue.groupFailureEvents with
      | nil =>
          simp [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures, ReferenceWorkQueue.State.groupFailure, pending]
      | cons first rest =>
          simp only [ReferenceWorkQueue.State.acceptsGraphEvent, pending, List.head?_cons,
            Option.any_some] at stale
          simp [ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures, ReferenceWorkQueue.State.groupFailure,
            pending, stale]

/-- An ignored item batch is still a distinct consumed receipt; other stale inputs have
no inline effect in this abstraction. Producer-owned suffix disposal is separate evidence.
-/
def staleEffects : GraphEvent → List HostEffect
  | .streamItems stream _ => [.acknowledge stream.ref]
  | _ => []

/-- Removing a semantic no-op must not remove its receipt acknowledgement. -/
theorem stale_graphEffects (queue : ReferenceWorkQueue.State) (event : GraphEvent)
    (stale : queue.acceptsGraphEvent event = false)
    : graphEffects queue event = staleEffects event := by
  cases event with
  | taskSuccess task result =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp [graphEffects, staleEffects, absent]
  | taskFailure task errors => rfl
  | groupFailure notice => rfl
  | streamItems stream items =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [graphEffects, staleEffects, stale, Bool.false_eq_true, ↓reduceIte,
        List.nil_append]
  | streamSuccess stream => rfl
  | streamFailure stream errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [graphEffects, staleEffects, stale, Bool.false_eq_true, ↓reduceIte]

/-- The actual handler, including inline registration effects, ignores an ineligible producer. -/
theorem stale_alternativeHandleGraphEvent (state : State)
    (event : GraphEvent) (stale : state.queue.acceptsGraphEvent event = false)
    : state.handleGraphEvent event = (state, [], staleEffects event, []) := by
  cases event with
  | taskSuccess task result =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : state.queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, State.taskSuccess, absent, staleEffects]
  | streamItems stream items =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, State.streamItems, stale, Bool.not_false,
        ↓reduceIte, staleEffects]
  | taskFailure task errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : state.queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, State.taskFailure, absent, staleEffects, List.flatMap_nil]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, staleEffects,
        stale_handleGraphEvent state.queue (.streamSuccess stream) stale]
  | streamFailure stream errors =>
      have absent : state.queue.rootStreams.contains stream.ref = false := stale
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, staleEffects, absent, Bool.false_eq_true, ↓reduceIte,
        stale_handleGraphEvent state.queue (.streamFailure stream errors) stale]
  | groupFailure notice =>
      simp only [State.handleGraphEvent, ReferenceWorkQueue.State.cacheTaskFailures,
        List.foldl_nil, staleEffects,
        stale_handleGraphEvent state.queue (.groupFailure notice) stale]

/-- Full dispatch is a semantic no-op plus exactly the stale receipt's inline effects.
Neither registration nor failure cleanup can be invented by the ignored payload.
-/
theorem stale_dispatch (before : GraphBatchResult) (event : GraphEvent)
    (stale : before.state.queue.acceptsGraphEvent event = false)
    : before.handleGraphEvent event
      = { before with effects := before.effects ++ staleEffects event } := by
  simp only [GraphBatchResult.handleGraphEvent,
    stale_alternativeHandleGraphEvent before.state event stale,
    ReferenceWorkQueue.State.enqueueGroupFailures, List.append_nil]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
