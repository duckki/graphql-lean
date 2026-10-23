import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedCallbacks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStreamRoots

/-! Entry-time stream activation retains complete item payloads, FIFO cursors and closures. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open ReferenceWorkQueue (StreamAction)

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
  | taskSuccess | taskFailure | groupFailure => cases streamAction
  | streamItems stream items =>
      obtain ⟨_, _, _, _, _, _, unclosed, _, _⟩ := laws.2.2
      exact retaining stream.ref (List.contains_iff_mem.mp started) unclosed
  | streamSuccess stream =>
      exact retaining stream.ref (List.contains_iff_mem.mp started)
        (laws.2.1.2.2.2 stream.ref List.mem_cons_self)
  | streamFailure stream errors =>
      exact retaining stream.ref (List.contains_iff_mem.mp started)
        (laws.2.1.2.2.2 stream.ref List.mem_cons_self)

/-- Every stream action active at batch entry retains its original input order. -/
theorem projectBatch_streamActions (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    (accepted
      : ∀ event ∈ batch,
          ∀ action,
            event.streamAction = some action → queue.acceptsGraphEvent event = true)
    : (projectBatch queue batch).filterMap ReferenceWorkQueue.GraphEvent.streamAction
      = batch.filterMap ReferenceWorkQueue.GraphEvent.streamAction := by
  induction batch with
  | nil => rfl
  | cons event rest ih =>
      have later := fun current member => accepted current (List.mem_cons_of_mem _ member)
      cases kept : queue.acceptsGraphEvent event with
      | true =>
          simp only [projectBatch, projectBatchAtEntry, List.filter_cons, kept, ↓reduceIte,
            List.filterMap_cons]
          have tail := ih later
          simp only [projectBatch, projectBatchAtEntry] at tail
          rw [tail]
      | false =>
          have absent : event.streamAction = none := by
            cases source : event.streamAction with
            | none => rfl
            | some action =>
                have active := accepted event List.mem_cons_self action source
                rw [kept] at active
                cases active
          simpa only [projectBatch, projectBatchAtEntry, List.filter_cons, kept,
            Bool.false_eq_true, ↓reduceIte, List.filterMap_cons, absent]
            using ih later

/-- Initially active stream-item callbacks preserve their entire values and cursor sequence. -/
theorem projectBatch_itemsBefore (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    (accepted
      : ∀ stream items,
          .streamItems stream items ∈ batch
          → queue.acceptsGraphEvent (.streamItems stream items) = true)
    (key : Nat)
    : ReferenceWorkQueue.GraphEvent.itemsBefore (projectBatch queue batch) key
      = ReferenceWorkQueue.GraphEvent.itemsBefore batch key := by
  induction batch with
  | nil => rfl
  | cons event rest ih =>
      have later := fun stream items member =>
        accepted stream items (List.mem_cons_of_mem _ member)
      cases kept : queue.acceptsGraphEvent event with
      | true =>
          simp only [projectBatch, projectBatchAtEntry, List.filter_cons, kept, ↓reduceIte]
          change ReferenceWorkQueue.GraphEvent.itemsBefore
            ([event] ++ projectBatch queue rest) key
            = ReferenceWorkQueue.GraphEvent.itemsBefore ([event] ++ rest) key
          rw [ReferenceWorkQueue.GraphEvent.itemsBefore_append,
            ReferenceWorkQueue.GraphEvent.itemsBefore_append, ih later]
      | false =>
          have noItems : ReferenceWorkQueue.GraphEvent.itemsBefore [event] key = [] := by
            cases event with
            | taskSuccess | taskFailure | groupFailure | streamSuccess | streamFailure =>
                rfl
            | streamItems stream items =>
                have active := accepted stream items List.mem_cons_self
                rw [kept] at active
                cases active
          simp only [projectBatch, projectBatchAtEntry, List.filter_cons, kept,
            Bool.false_eq_true, ↓reduceIte]
          rw [show event :: rest = [event] ++ rest from rfl,
            ReferenceWorkQueue.GraphEvent.itemsBefore_append, noItems, List.nil_append]
          exact ih later

/-- A buffer formed at one boundary retains all its item payloads. -/
theorem Enqueued.itemsBefore_projectBatch {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    (_valid : ReferenceWorkQueue.ValidGraphEvents work earlier) (key : Nat)
    : ReferenceWorkQueue.GraphEvent.itemsBefore
        (projectBatch queue (callbacks.map BufferedCallback.event)) key
      = ReferenceWorkQueue.GraphEvent.itemsBefore (callbacks.map BufferedCallback.event)
          key := by
  simpa only [projectBatch]
    using congrArg
      (fun events => ReferenceWorkQueue.GraphEvent.itemsBefore events key)
      queued.projectBatchAtEntry_eq

/-- The same available buffer retains every stream closure as well as item actions. -/
theorem Enqueued.streamActions_projectBatch {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    (_valid : ReferenceWorkQueue.ValidGraphEvents work earlier)
    : (projectBatch queue (callbacks.map BufferedCallback.event)).filterMap
        ReferenceWorkQueue.GraphEvent.streamAction
      = (callbacks.map BufferedCallback.event).filterMap
          ReferenceWorkQueue.GraphEvent.streamAction := by
  simpa only [projectBatch]
    using congrArg
      (fun events => events.filterMap ReferenceWorkQueue.GraphEvent.streamAction)
      queued.projectBatchAtEntry_eq

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
