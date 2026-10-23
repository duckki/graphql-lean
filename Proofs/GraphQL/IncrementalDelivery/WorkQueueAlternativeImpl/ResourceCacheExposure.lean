import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceHandoff
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationDispatch

/-! Resource observations agree at actual cached source cuts. Intermediate native and
reference queues need agree after exposure, not before every computation slot is exposed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- Handoff and receipt labels depend on live input guards, not rejection-slot contents. -/
theorem graphEffects_eq_of_accepts (first second : ReferenceWorkQueue.State)
    (event : GraphEvent)
    (same : first.acceptsGraphEvent event = second.acceptsGraphEvent event)
    : graphEffects first event = graphEffects second event := by
  cases event with
  | taskSuccess occurrence result =>
      cases left : first.taskNode? occurrence <;> cases right : second.taskNode? occurrence <;>
        simp_all [graphEffects, ReferenceWorkQueue.State.acceptsGraphEvent]
  | streamItems stream items =>
      have roots : first.rootStreams.contains stream.ref
          = second.rootStreams.contains stream.ref := same
      simp only [graphEffects, roots]
  | streamFailure stream errors =>
      have roots : first.rootStreams.contains stream.ref
          = second.rootStreams.contains stream.ref := same
      simp only [graphEffects, roots]
  | taskFailure | groupFailure | streamSuccess => rfl

/-- Equal exposed queues supply the same executable guard for any callback. -/
theorem acceptsGraphEvent_of_cache_eq (first second : ReferenceWorkQueue.State)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (event : GraphEvent)
    : first.acceptsGraphEvent event = second.acceptsGraphEvent event := by
  have exposed := congrArg
    (fun queue : ReferenceWorkQueue.State => queue.acceptsGraphEvent event) same
  rw [first.cacheTaskFailures_acceptsGraphEvent available event,
    second.cacheTaskFailures_acceptsGraphEvent available event] at exposed
  exact exposed

/-- Common batch exposure aligns ghost handoffs even when raw rejection slots differ. -/
theorem graphEffects_of_cache_eq (first second : ReferenceWorkQueue.State)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same : first.cacheTaskFailures available = second.cacheTaskFailures available)
    (event : GraphEvent)
    : graphEffects first event = graphEffects second event :=
  graphEffects_eq_of_accepts first second event
    (acceptsGraphEvent_of_cache_eq first second available same event)

namespace NativeRefinement

/-- Task completion identities are unconditional; stream completion uses the same live guard. -/
theorem normalCompletionTarget?_eq_of_accepts (first second : ReferenceWorkQueue.State)
    (event : GraphEvent)
    (same : first.acceptsGraphEvent event = second.acceptsGraphEvent event)
    : normalCompletionTarget? first event = normalCompletionTarget? second event := by
  cases event with
  | streamSuccess stream =>
      have roots : first.rootStreams.contains stream.ref
          = second.rootStreams.contains stream.ref := same
      simp only [normalCompletionTarget?, roots]
  | taskSuccess | taskFailure | groupFailure | streamItems | streamFailure => rfl

/-- The actual resource observer, including ordered cleanup actions, respects cache exposure.
This uses concrete dispatch equality and label guards, without a desired resource endpoint law.
-/
theorem ResourceState.observeDispatch_of_cache_eq (resources : ResourceState)
    (inventories : ProducerInventories) (first second : State)
    (firstRunning : first.stopped = false) (secondRunning : second.stopped = false)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    (same
      : first.queue.cacheTaskFailures available
        = second.queue.cacheTaskFailures available)
    (event : GraphEvent)
    : resources.observeDispatch inventories first event available
      = resources.observeDispatch inventories second event available := by
  have normal := normalCompletionTarget?_eq_of_accepts first.queue second.queue event
    (acceptsGraphEvent_of_cache_eq first.queue second.queue available same event)
  have labels := graphEffects_of_cache_eq first.queue second.queue available same event
  have handled := State.handleGraphEvent_of_cache_eq first second firstRunning secondRunning
    available same event
  have effects : (({ state := first } : GraphBatchResult).handleGraphEvent event available).effects
      = (({ state := second } : GraphBatchResult).handleGraphEvent event available).effects := by
    simp only [GraphBatchResult.handleGraphEvent, handled]
  simp only [ResourceState.observeDispatch, ResourceState.observeNormalCompletion, normal,
    labels, effects]

end NativeRefinement
end GraphQL.IncrementalDelivery.AlternativeWorkQueue
