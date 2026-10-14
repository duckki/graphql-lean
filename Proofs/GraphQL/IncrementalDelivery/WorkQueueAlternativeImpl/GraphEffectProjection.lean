import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationHostEffects

/-! Proof-only handoff/receipt labels for reuse by native ghost models.

This projection deliberately omits rejected-task cleanup. It is not an executable observer,
not the entire inline trace, and does not justify moving cleanup after acknowledgement.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- Erased handoff/receipt/source-failure labels; actual registration cleanup is separate.
The projection witnesses below connect the first two views to the current inline handlers.
-/
def graphEffects (queue : ReferenceWorkQueue.State) : GraphEvent → List HostEffect
  | .taskSuccess occurrence _ =>
      match queue.taskNode? occurrence with
      | none => []
      | some task =>
          if queue.taskHasHealthyOwner task.task then [.adopt occurrence] else []
  | .streamItems stream items =>
      (if queue.rootStreams.contains stream.ref then
          items.map (fun item => .adopt item.occurrence)
        else
          [])
      ++ [.acknowledge stream.ref]
  | .streamFailure stream _ =>
      if queue.rootStreams.contains stream.ref then [.cancelSource stream.ref] else []
  | _ => []

private theorem adoptionLabels_producers (items : List ReferenceWorkQueue.StreamItem)
    : (items.map (fun item => HostEffect.adopt item.occurrence)).filterMap
        HostEffect.adoptedProducer?
      = items.map (·.occurrence) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simpa only [List.map_cons, List.filterMap_cons, HostEffect.adoptedProducer?]
        using congrArg (List.cons item.occurrence) ih

private theorem adoptionLabels_acknowledgements
    (items : List ReferenceWorkQueue.StreamItem)
    : (items.map (fun item => HostEffect.adopt item.occurrence)).filterMap
        HostEffect.acknowledgedStream?
      = [] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simpa only [List.map_cons, List.filterMap_cons, HostEffect.acknowledgedStream?] using ih

/-- The ghost model's producer-label view is exactly the actual ordered handoff projection. -/
theorem graphEffects_adoptedProducers (state : State) (event : GraphEvent)
    : (graphEffects state.queue event).filterMap HostEffect.adoptedProducer?
      = (state.handleGraphEvent event).2.2.filterMap HostEffect.adoptedProducer? := by
  cases event with
  | taskSuccess occurrence result =>
      rw [show (state.handleGraphEvent (.taskSuccess occurrence result)).2.2
        = (state.taskSuccess occurrence result).2.2 from rfl,
        State.taskSuccess_adoptedProducers]
      simp only [graphEffects]
      cases found : state.queue.taskNode? occurrence with
      | none => rfl
      | some node =>
          dsimp only
          split <;> rfl
  | streamItems stream items =>
      rw [show (state.handleGraphEvent (.streamItems stream items)).2.2
        = (state.streamItems stream items).2.2 from rfl,
        State.streamItems_adoptedProducers]
      simp only [graphEffects]
      cases active : state.queue.rootStreams.contains stream.ref <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.filterMap_append,
          adoptionLabels_producers, List.filterMap_cons, HostEffect.adoptedProducer?,
          List.filterMap_nil, List.append_nil]
  | taskFailure occurrence errors =>
      obtain ⟨targets, same⟩ := state.taskFailure_cleanupEffects occurrence errors
      change [] = (state.taskFailure occurrence errors).2.2.filterMap HostEffect.adoptedProducer?
      rw [same, cleanupEffects_adoptedProducers]
  | streamSuccess => rfl
  | streamFailure stream errors =>
      simp only [graphEffects, State.handleGraphEvent]

/-- Receipt labels retain exactly the actual acknowledgement identities, including ignored input. -/
theorem graphEffects_acknowledgedStreams (state : State) (event : GraphEvent)
    : (graphEffects state.queue event).filterMap HostEffect.acknowledgedStream?
      = (state.handleGraphEvent event).2.2.filterMap HostEffect.acknowledgedStream? := by
  cases event with
  | taskSuccess occurrence result =>
      rw [show (state.handleGraphEvent (.taskSuccess occurrence result)).2.2
        = (state.taskSuccess occurrence result).2.2 from rfl,
        State.taskSuccess_acknowledgedStreams]
      simp only [graphEffects]
      split
      · rfl
      · split <;> rfl
  | streamItems stream items =>
      rw [show (state.handleGraphEvent (.streamItems stream items)).2.2
        = (state.streamItems stream items).2.2 from rfl,
        State.streamItems_acknowledges_once]
      simp only [graphEffects]
      cases active : state.queue.rootStreams.contains stream.ref <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.filterMap_append,
          adoptionLabels_acknowledgements, List.filterMap_cons, HostEffect.acknowledgedStream?,
          List.filterMap_nil, List.nil_append]
  | taskFailure occurrence errors =>
      obtain ⟨targets, same⟩ := state.taskFailure_cleanupEffects occurrence errors
      change [] = (state.taskFailure occurrence errors).2.2.filterMap HostEffect.acknowledgedStream?
      rw [same, cleanupEffects_acknowledgedStreams]
  | streamSuccess => rfl
  | streamFailure stream errors =>
      simp only [graphEffects, State.handleGraphEvent]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
