import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedCallbacks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions

/-! Streams in a legally available boundary buffer cannot become stale before their
own closure. Thus semantic filtering preserves every item and the exact FIFO cursor.+-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

open GraphQL.IncrementalDelivery.WorkQueueSemantics
open ReferenceWorkQueue (StreamAction)

-----------------------------------------------------------------------------------------
-- Only a stream's own closure can remove an already active root
-----------------------------------------------------------------------------------------

/-- Task cancellation never removes an active stream root; other stream closures remove
only their own key. This local fact needs no work, producer, or output-admission premise.
-/
theorem rootStream_survives (queue : ReferenceWorkQueue.State) (event : GraphEvent)
    (key : Nat) (active : key ∈ queue.rootStreams) (unclosed : key ∉ event.identities.2)
    : key ∈ (queue.handleGraphEvent event).1.rootStreams := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_streamRoots_cover occurrence result
        (List.mem_append_left _ active)
  | taskFailure occurrence errors =>
      simpa only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.taskFailure_rootStreams] using active
  | streamItems stream items =>
      exact queue.streamItems_streamRoots_cover stream items (List.mem_append_left _ active)
  | streamSuccess stream =>
      have different : key ≠ stream.ref := by
        simpa only [ReferenceWorkQueue.GraphEvent.identities, List.mem_singleton]
          using unclosed
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.streamSuccess]
      split
      · exact List.mem_filter.mpr ⟨active, by simpa using different⟩
      · exact active
  | streamFailure stream errors =>
      have different : key ≠ stream.ref := by
        simpa only [ReferenceWorkQueue.GraphEvent.identities, List.mem_singleton]
          using unclosed
      simp only [ReferenceWorkQueue.State.handleGraphEvent,
        ReferenceWorkQueue.State.streamFailure]
      split
      · exact List.mem_filter.mpr ⟨active, by simpa using different⟩
      · exact active

/-- Replaying a prefix with no closure of this key retains its boundary-time activation.
This excludes late activation arguments: activation is already present in the premise.
-/
theorem rootStream_survives_replay (queue : ReferenceWorkQueue.State)
    (events : List GraphEvent) (key : Nat) (active : key ∈ queue.rootStreams)
    (unclosed : key ∉ events.flatMap (fun event => event.identities.2))
    : key ∈ (queue.replayGraphEvents events).rootStreams := by
  induction events generalizing queue with
  | nil => exact active
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.mem_append, not_or] at unclosed
      exact ih (queue.handleGraphEvent event).1
        (rootStream_survives queue event key active unclosed.1) unclosed.2

-----------------------------------------------------------------------------------------
-- Enqueue-time permission plus the original source laws retains stream callbacks
-----------------------------------------------------------------------------------------

/-- Every stream action is still accepted at its actual position in this available
buffer. Source readiness excludes items after closure; freshness excludes repeat closure.
The buffer's enqueue-time check supplies activation, not merely producer settlement.
-/
theorem Enqueued.streamAction_accepted {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    (valid : ReferenceWorkQueue.ValidGraphEvents work earlier)
    {before event after action}
    (split : callbacks.map BufferedCallback.event = before ++ event :: after)
    (streamAction : event.streamAction = some action)
    : (queue.replayGraphEvents before).acceptsGraphEvent event = true := by
  have member : event ∈ callbacks.map BufferedCallback.event := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨callback, present, same⟩ := List.mem_map.mp member
  have started := queued.started callback present
  rw [same] at started
  have laws := (queued.work_valid valid).atPrefix
    (before := earlier ++ before) (event := event)
    ⟨after, by rw [split]; simp only [List.append_assoc, List.singleton_append]⟩
  have retaining (key : Nat) (active : key ∈ queue.rootStreams)
      (unclosed : key ∉ (earlier ++ before).flatMap (fun event => event.identities.2))
      : (queue.replayGraphEvents before).rootStreams.contains key = true := by
    apply List.contains_iff_mem.mpr
    apply rootStream_survives_replay queue before key active
    intro closed
    exact unclosed (by rw [List.flatMap_append]; exact List.mem_append_right _ closed)
  cases event with
  | taskSuccess | taskFailure => cases streamAction
  | streamItems stream items =>
      obtain ⟨_, _, _, _, _, _, unclosed, _, _⟩ := laws.2.2
      exact retaining stream.ref (List.contains_iff_mem.mp started) unclosed
  | streamSuccess stream =>
      exact retaining stream.ref (List.contains_iff_mem.mp started)
        (laws.2.1.2.2.2 stream.ref List.mem_cons_self)
  | streamFailure stream errors =>
      exact retaining stream.ref (List.contains_iff_mem.mp started)
        (laws.2.1.2.2.2 stream.ref List.mem_cons_self)

/-- If every source stream action is accepted at its own prefix, filtering preserves
the complete ordered stream-action subsequence, including closure flags.
-/
theorem projectBatch_streamActions (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    (accepted
      : ∀ before event after action,
          batch = before ++ event :: after
          → event.streamAction = some action
          → (queue.replayGraphEvents before).acceptsGraphEvent event = true)
    : (projectBatch queue batch).filterMap ReferenceWorkQueue.GraphEvent.streamAction
      = batch.filterMap ReferenceWorkQueue.GraphEvent.streamAction := by
  induction batch generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      cases live : queue.acceptsGraphEvent event with
      | true =>
          simp only [projectBatch, live, ↓reduceIte, List.filterMap_cons]
          rw [ih _ (by
            intro before current after action split source
            have prior := accepted (event :: before) current after action
              (by simp only [List.cons_append]; rw [split]) source
            exact prior)]
      | false =>
          have ignored := stale_handleGraphEvent queue event live
          have absent : event.streamAction = none := by
            cases source : event.streamAction with
            | none => rfl
            | some action =>
                have retained := accepted [] event rest action rfl source
                simp only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil] at retained
                rw [live] at retained
                cases retained
          simp only [projectBatch, live, Bool.false_eq_true, ↓reduceIte,
            List.filterMap_cons, absent]
          apply ih queue
          intro before current after action split source
          have prior := accepted (event :: before) current after action
            (by simp only [List.cons_append]; rw [split]) source
          simpa only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons,
            ignored]
            using prior

/-- Acceptance of item callbacks preserves full item payloads and their order, not
just source keys. Consequently the source's per-stream received-item cursor is exact.
-/
theorem projectBatch_itemsBefore (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    (accepted
      : ∀ before stream items after,
          batch = before ++ .streamItems stream items :: after
          → (queue.replayGraphEvents before).acceptsGraphEvent (.streamItems stream items)
            = true)
    (key : Nat)
    : ReferenceWorkQueue.GraphEvent.itemsBefore (projectBatch queue batch) key
      = ReferenceWorkQueue.GraphEvent.itemsBefore batch key := by
  induction batch generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      cases live : queue.acceptsGraphEvent event with
      | true =>
          have tail := ih (queue.handleGraphEvent event).1 (by
            intro before stream items after split
            exact accepted (event :: before) stream items after
              (by simp only [List.cons_append]; rw [split]))
          simp only [projectBatch, live, ↓reduceIte]
          change ReferenceWorkQueue.GraphEvent.itemsBefore
            ([event] ++ projectBatch (queue.handleGraphEvent event).1 rest) key
            = ReferenceWorkQueue.GraphEvent.itemsBefore ([event] ++ rest) key
          rw [ReferenceWorkQueue.GraphEvent.itemsBefore_append,
            ReferenceWorkQueue.GraphEvent.itemsBefore_append, tail]
      | false =>
          have ignored := stale_handleGraphEvent queue event live
          have noItems : ReferenceWorkQueue.GraphEvent.itemsBefore [event] key = [] := by
            cases event with
            | taskSuccess | taskFailure | streamSuccess | streamFailure => rfl
            | streamItems stream items =>
                have retained := accepted [] stream items rest rfl
                simp only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil] at retained
                rw [live] at retained
                cases retained
          have tail := ih queue (by
            intro before stream items after split
            have prior := accepted (event :: before) stream items after
              (by simp only [List.cons_append]; rw [split])
            simpa only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons,
              ignored] using prior)
          simp only [projectBatch, live, Bool.false_eq_true, ↓reduceIte]
          rw [show event :: rest = [event] ++ rest from rfl,
            ReferenceWorkQueue.GraphEvent.itemsBefore_append, noItems, List.nil_append]
          exact tail

/-- A boundary buffer loses no stream item when stale task callbacks are erased.
The FIFO offset, errors and child work of every supplied item remain unchanged.
-/
theorem Enqueued.itemsBefore_projectBatch {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    (valid : ReferenceWorkQueue.ValidGraphEvents work earlier) (key : Nat)
    : ReferenceWorkQueue.GraphEvent.itemsBefore
        (projectBatch queue (callbacks.map BufferedCallback.event)) key
      = ReferenceWorkQueue.GraphEvent.itemsBefore (callbacks.map BufferedCallback.event)
          key := by
  apply projectBatch_itemsBefore queue _ _ key
  intro before stream items after split
  exact queued.streamAction_accepted valid split rfl

/-- The same available buffer retains every stream closure as well as its item actions.
This is a semantic source fact, not an exactly-once native acknowledgement theorem.
-/
theorem Enqueued.streamActions_projectBatch {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    (valid : ReferenceWorkQueue.ValidGraphEvents work earlier)
    : (projectBatch queue (callbacks.map BufferedCallback.event)).filterMap
        ReferenceWorkQueue.GraphEvent.streamAction
      = (callbacks.map BufferedCallback.event).filterMap
          ReferenceWorkQueue.GraphEvent.streamAction :=
  projectBatch_streamActions queue _
    (fun _ _ _ _ split source =>
      queued.streamAction_accepted valid split source)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
