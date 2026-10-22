import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedCallbackDefinitions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions

/-! Already active stream roots survive cached dispatch until their own source closure.
These structural facts do not filter callbacks or choose their notification order.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (StreamAction)

/-- Task cancellation never removes an active stream; only its own closure can do so. -/
theorem rootStream_survives (queue : ReferenceWorkQueue.State) (event : GraphEvent)
    (key : Nat) (active : key ∈ queue.rootStreams) (unclosed : key ∉ event.identities.2)
    (available : List (Occurrence × Nat) := [])
    : key ∈ (queue.handleGraphEvent event available).1.rootStreams := by
  let current := queue.cacheTaskFailures available
  have same := congrArg ReferenceWorkQueue.State.rootStreams
    (queue.cacheTaskFailures_frame available)
  change current.rootStreams = queue.rootStreams at same
  have cached : key ∈ current.rootStreams := same.symm ▸ active
  cases event with
  | taskSuccess occurrence result =>
      exact current.taskSuccess_streamRoots_cover occurrence result available
        (List.mem_append_left _ cached)
  | taskFailure occurrence errors =>
      change key ∈ (current.taskFailure occurrence errors).1.rootStreams
      rw [ReferenceWorkQueue.State.taskFailure_rootStreams]
      exact cached
  | streamItems stream items =>
      exact current.streamItems_streamRoots_cover stream items available
        (List.mem_append_left _ cached)
  | streamSuccess stream =>
      have different : key ≠ stream.ref := by
        simpa only [ReferenceWorkQueue.GraphEvent.identities, List.mem_singleton]
          using unclosed
      change key ∈ (current.streamSuccess stream).1.rootStreams
      simp only [ReferenceWorkQueue.State.streamSuccess]
      split
      · exact List.mem_filter.mpr ⟨cached, by simpa using different⟩
      · exact cached
  | streamFailure stream errors =>
      have different : key ≠ stream.ref := by
        simpa only [ReferenceWorkQueue.GraphEvent.identities, List.mem_singleton]
          using unclosed
      change key ∈ (current.streamFailure stream errors).1.rootStreams
      simp only [ReferenceWorkQueue.State.streamFailure]
      split
      · exact List.mem_filter.mpr ⟨cached, by simpa using different⟩
      · exact cached

  | groupFailure failure =>
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.groupFailure]
      split
      · exact cached
      · split <;> exact cached

/-- A fixed-snapshot FIFO prefix retains every active stream not closed by that prefix. -/
theorem rootStream_survives_replay (queue : ReferenceWorkQueue.State)
    (events : List GraphEvent) (key : Nat) (active : key ∈ queue.rootStreams)
    (unclosed : key ∉ events.flatMap (fun event => event.identities.2))
    (available : List (Occurrence × Nat) := [])
    : key ∈ (queue.replayGraphEvents events available).rootStreams := by
  induction events generalizing queue with
  | nil => exact active
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at unclosed
      exact ih (queue.dispatchGraphEvent event available).1
        (rootStream_survives queue event key active unclosed.1 available) unclosed.2

/-- Terminal flags do not remove active roots; a later pending stream remains active. -/
theorem rootStream_survives_batch (queue : ReferenceWorkQueue.State)
    (events : List GraphEvent) (key : Nat) (active : key ∈ queue.rootStreams)
    (unclosed : key ∉ events.flatMap (fun prior => prior.identities.2))
    : key ∈ (queue.handleGraphEvents events).1.rootStreams := by
  cases ended : queue.terminated with
  | true =>
      simpa only [queue.handleGraphEvents_after_termination events ended] using active
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events ended
      rw [same]
      exact rootStream_survives_replay queue events key active unclosed
        (ReferenceWorkQueue.GraphEvent.availableFailures events)

/-- Freshness/readiness exclude prior closure for every kind of stream callback. -/
theorem streamAction_unclosed {work before event action}
    (fresh : ReferenceWorkQueue.GraphEvent.Fresh before event)
    (ready : ReferenceWorkQueue.GraphEvent.Ready work before event)
    (source : ReferenceWorkQueue.GraphEvent.streamAction event = some action)
    : action.1 ∉ before.flatMap (fun prior => prior.identities.2) := by
  cases event with
  | taskSuccess | taskFailure | groupFailure => cases source
  | streamItems stream items =>
      cases source
      exact ready.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1
  | streamSuccess stream =>
      cases source
      exact fresh.2.2.2 stream.ref List.mem_cons_self
  | streamFailure stream errors =>
      cases source
      exact fresh.2.2.2 stream.ref List.mem_cons_self

/-- Stream membership depends only on its active root, not task registration or flags. -/
theorem streamAction_accepts_iff (queue : ReferenceWorkQueue.State)
    (event : GraphEvent) (action : StreamAction)
    (source : event.streamAction = some action)
    : queue.acceptsGraphEvent event = true ↔ action.1 ∈ queue.rootStreams := by
  cases event with
  | taskSuccess | taskFailure | groupFailure => cases source
  | streamItems stream items | streamSuccess stream | streamFailure stream errors =>
      cases source
      exact List.contains_iff_mem

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
