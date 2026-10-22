import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Finite callback buffers formed at actual queue boundaries. Receipt identities are
proof evidence and remain distinct from task and stream identities. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

/-- Frozen outcome plus a request-local callback/receipt identity, distinct from the
task or stream identity inside the event. This is proof evidence, not a runtime ledger.
-/
structure BufferedCallback where
  receipt : Nat
  event : GraphEvent

/-- A FIFO available buffer enqueued at one real queue boundary. Later reduction can
retire its producers. Interleaved enqueue/reduction needs multiple related boundaries;
this finite relation does not assert a complete native callback correspondence.
Matching, freshness and producer/FIFO laws are the original source laws, checked when
the host forms its buffer. No wire lifecycle or output property is assumed.
-/
inductive Enqueued (work : Work) (queue : ReferenceWorkQueue.State)
    (earlier : List GraphEvent)
    : List BufferedCallback → Prop where
  | nil : Enqueued work queue earlier []
  | append {before : List BufferedCallback} (queued : Enqueued work queue earlier before)
    (callback : BufferedCallback) (running : queue.terminated = false)
    (started : queue.acceptsGraphEvent callback.event = true)
    (receiptFresh : callback.receipt ∉ before.map BufferedCallback.receipt)
    (matching : callback.event.MatchesWork work)
    (fresh : callback.event.Fresh (earlier ++ before.map BufferedCallback.event))
    (ready : callback.event.Ready work (earlier ++ before.map BufferedCallback.event))
    : Enqueued work queue earlier (before ++ [callback])

/-- Every callback really had enqueue-time permission, even if reduction later prunes it. -/
theorem Enqueued.started {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    : ∀ callback ∈ callbacks, queue.acceptsGraphEvent callback.event = true := by
  induction queued with
  | nil => simp
  | append prior callback running started receiptFresh matching fresh ready ih =>
      intro selected member
      rcases List.mem_append.mp member with earlier | latest
      · exact ih selected earlier
      · have same := List.mem_singleton.mp latest
        subst selected
        exact started

/-- Callback identities are distinct within this available buffer; stream identity is
not receipt identity. Whole-run once-only acknowledgement additionally needs a related
consumption history, not merely this buffer's identity uniqueness.
-/
theorem Enqueued.receipts_unique {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    : (callbacks.map BufferedCallback.receipt).Nodup := by
  induction queued with
  | nil => simp
  | append prior callback running started receiptFresh matching fresh ready ih =>
      rw [List.map_append, List.nodup_append]
      refine ⟨ih, by simp, ?_⟩
      intro first member second single same
      simp only [List.map_singleton, List.mem_singleton] at single
      exact receiptFresh ((same.trans single) ▸ member)

/-- Frozen payload and FIFO/producer evidence construct raw work legality separately
from sequential live-membership admission, which the raw batch need not satisfy.
-/
theorem Enqueued.work_valid {work queue earlier callbacks}
    (queued : Enqueued work queue earlier callbacks)
    (valid : ReferenceWorkQueue.ValidGraphEvents work earlier)
    : ReferenceWorkQueue.ValidGraphEvents work
        (earlier ++ callbacks.map BufferedCallback.event) := by
  induction queued with
  | nil => simpa only [List.map_nil, List.append_nil] using valid
  | append prior callback running started receiptFresh matching fresh ready ih =>
      simp only [List.map_append, List.map_singleton, ← List.append_assoc]
      exact .append ih matching fresh ready

/-- Retirement is not authority to enqueue another event for a historical producer. -/
theorem cannot_enqueue_retired {work queue earlier before callback}
    (stale : queue.acceptsGraphEvent callback.event = false)
    : ¬Enqueued work queue earlier (before ++ [callback]) := by
  intro queued
  have active := queued.started callback (List.mem_append_right _ (List.mem_singleton_self _))
  rw [stale] at active
  contradiction

/-- Available buffers at successive actual reduction boundaries. Each batch's callbacks
were live at its own boundary, though earlier callbacks in that batch can retire them.
This relation does not cover a callback enqueued before an earlier batch and consumed
later; that requires a finer interleaved enqueue/reduction history. Receipt uniqueness
is still local to each available buffer, not a whole-run acknowledgement claim.
-/
def BoundaryBuffers (work : Work) (queue : ReferenceWorkQueue.State)
    (earlier : List GraphEvent)
    : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∃ callbacks,
        Enqueued work queue earlier callbacks
        ∧ callbacks.map BufferedCallback.event = batch)
      ∧ BoundaryBuffers work (queue.handleGraphEvents batch).1 (earlier ++ batch) rest

/-- Boundary-buffer admission constructs the original raw work laws. It does not
construct sequential membership, since cancellation can invalidate a buffered suffix.
-/
theorem BoundaryBuffers.work_valid {work queue earlier batches}
    (buffers : BoundaryBuffers work queue earlier batches)
    (valid : ReferenceWorkQueue.ValidGraphEvents work earlier)
    : ReferenceWorkQueue.ValidGraphEvents work (earlier ++ batches.flatten) := by
  induction batches generalizing queue earlier with
  | nil => simpa only [List.flatten_nil, List.append_nil] using valid
  | cons batch rest ih =>
      obtain ⟨⟨callbacks, queued, same⟩, later⟩ := buffers
      have current := queued.work_valid valid
      rw [same] at current
      simpa only [List.flatten_cons, List.append_assoc] using ih later current

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
