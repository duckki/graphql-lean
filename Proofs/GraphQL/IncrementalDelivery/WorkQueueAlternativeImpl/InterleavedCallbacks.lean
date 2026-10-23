import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedStreamRoots
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.InterleavedCallbackRecords
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedWorkProjection
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! FIFO enqueue/reduction histories, including callbacks carried across batch boundaries.
The ghost inventory retains callback identity; semantic filtering erases only payloads.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

open ReferenceWorkQueue (StreamAction)

-----------------------------------------------------------------------------------------
-- Stream activation survives earlier reductions, but never a prior own closure
-----------------------------------------------------------------------------------------

private theorem unclosed_of_sublist {before events : List GraphEvent} {key : Nat}
    (unclosed : key ∉ before.flatMap (fun prior => prior.identities.2))
    (included : events.Sublist before)
    : key ∉ events.flatMap (fun prior => prior.identities.2) := by
  intro closed
  obtain ⟨event, member, same⟩ := List.mem_flatMap.mp closed
  exact unclosed (List.mem_flatMap.mpr ⟨event, included.subset member, same⟩)

-----------------------------------------------------------------------------------------
-- Host invariants are constructed, not assumed as semantic-source or output laws
-----------------------------------------------------------------------------------------

/-- The history retains every receipt once and supplies reduction-time stream activation.
Raw work laws come only from the fixed payload/freshness/FIFO checks at enqueue.
-/
structure CallbackBuffer.Invariant (work : Work) (initial : ReferenceWorkQueue.State)
    (buffer : CallbackBuffer)
    : Prop where
  fifo : buffer.batches.flatten ++ buffer.pending = buffer.received
  receipts : (buffer.received.map BufferedCallback.receipt).Nodup
  workValid
    : ReferenceWorkQueue.ValidGraphEvents work
        (buffer.received.map BufferedCallback.event)
  current : buffer.queue = replayBatches initial buffer.rawBatches
  pendingStreams
    : ∀ callback ∈ buffer.pending,
        ∀ action,
          callback.event.streamAction = some action
          → buffer.queue.acceptsGraphEvent callback.event = true
  reducedStreams : ActiveStreamBatches initial buffer.rawBatches

/-- Consumed batches and pending callbacks partition the same enqueue history. -/
theorem CallbackBuffer.Invariant.event_fifo {work initial buffer}
    (valid : CallbackBuffer.Invariant work initial buffer)
    : buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event
      = buffer.received.map BufferedCallback.event := by
  rw [← valid.fifo, List.map_append, List.map_flatten]
  rfl

theorem CallbackBuffer.Invariant.initialize (work : Work)
    (initial : ReferenceWorkQueue.State)
    : CallbackBuffer.Invariant work initial { queue := initial } :=
  ⟨rfl, by simp, .nil, rfl, by simp, trivial⟩

/-- Enqueue preserves the global receipt inventory and licenses only currently live work. -/
theorem CallbackBuffer.Invariant.enqueue {work initial buffer}
    (valid : CallbackBuffer.Invariant work initial buffer) (callback : BufferedCallback)
    (started : buffer.queue.acceptsGraphEvent callback.event = true)
    (receiptFresh : callback.receipt ∉ buffer.received.map BufferedCallback.receipt)
    (matching : callback.event.MatchesWork work)
    (fresh
      : callback.event.Fresh
          (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event))
    (ready
      : callback.event.Ready work
          (buffer.rawBatches.flatten ++ buffer.pending.map BufferedCallback.event))
    : CallbackBuffer.Invariant work initial (buffer.enqueue callback) := by
  refine ⟨?_, ?_, ?_, valid.current, ?_, valid.reducedStreams⟩
  · simpa only [CallbackBuffer.enqueue, List.append_assoc]
      using congrArg (fun callbacks => callbacks ++ [callback]) valid.fifo
  · simp only [CallbackBuffer.enqueue, List.map_append, List.map_singleton,
      List.nodup_append]
    refine ⟨valid.receipts, by simp, ?_⟩
    intro first member second single same
    simp only [List.mem_singleton] at single
    exact receiptFresh ((same.trans single) ▸ member)
  · rw [valid.event_fifo] at fresh ready
    simpa only [CallbackBuffer.enqueue, List.map_append, List.map_singleton]
      using ReferenceWorkQueue.ValidGraphEvents.append valid.workValid matching fresh
        ready
  · intro selected member action source
    rcases List.mem_append.mp member with old | latest
    · exact valid.pendingStreams selected old action source
    · have same := List.mem_singleton.mp latest
      subst selected
      exact started

private theorem pending_laws {work initial buffer front callback after}
    (valid : CallbackBuffer.Invariant work initial buffer)
    (split : buffer.pending = front ++ callback :: after)
    : callback.event.MatchesWork work
      ∧ callback.event.Fresh
          (buffer.rawBatches.flatten ++ front.map BufferedCallback.event)
      ∧ callback.event.Ready work
          (buffer.rawBatches.flatten ++ front.map BufferedCallback.event) := by
  have raw := valid.workValid
  rw [← valid.event_fifo, split, List.map_append, List.map_cons] at raw
  exact raw.atPrefix
    (before := buffer.rawBatches.flatten ++ front.map BufferedCallback.event)
    (event := callback.event)
    ⟨
      after.map BufferedCallback.event,
      by simp only [List.append_assoc,
        List.singleton_append]
    ⟩

/-- Earlier consumption can retire tasks, but pending streams retain their enqueue-time
activation. Full event payloads, source cursors and closure order are not discarded.
-/
theorem CallbackBuffer.Invariant.reduce {work initial buffer}
    (valid : CallbackBuffer.Invariant work initial buffer)
    (front rest : List BufferedCallback) (fifo : buffer.pending = front ++ rest)
    : CallbackBuffer.Invariant work initial (buffer.reduce front rest) := by
  have prefix_member : ∀ callback ∈ front, callback ∈ buffer.pending := by
    intro callback member
    rw [fifo]
    exact List.mem_append_left _ member
  have reduceStreams : ∀ prior event after action,
      front.map BufferedCallback.event = prior ++ event :: after
      → event.streamAction = some action
      → (buffer.queue.replayGraphEvents prior).acceptsGraphEvent event = true := by
    intro prior event after action split source
    have raw := valid.workValid
    rw [← valid.event_fifo, fifo, List.map_append, split] at raw
    have laws := raw.atPrefix
      (before := buffer.rawBatches.flatten ++ prior) (event := event)
      ⟨after ++ rest.map BufferedCallback.event, by simp only [List.append_assoc,
        List.cons_append, List.nil_append]⟩
    have member : event ∈ front.map BufferedCallback.event := by
      rw [split]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨callback, present, same⟩ := List.mem_map.mp member
    have active := valid.pendingStreams callback (prefix_member callback present) action
      (same ▸ source)
    rw [same] at active
    apply (streamAction_accepts_iff _ _ _ source).mpr
    apply rootStream_survives_replay buffer.queue prior action.1
      ((streamAction_accepts_iff _ _ _ source).mp active)
    exact unclosed_of_sublist (streamAction_unclosed laws.2.1 laws.2.2 source)
      (List.sublist_append_right _ _)
  refine ⟨?_, valid.receipts, valid.workValid, ?_, ?_, ?_⟩
  · simpa only [CallbackBuffer.reduce, List.flatten_append, List.flatten_singleton,
      List.append_assoc, fifo] using valid.fifo
  · simp only [CallbackBuffer.reduce, CallbackBuffer.rawBatches, List.map_append,
      List.map_singleton, replayBatches, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rw [valid.current]
    rfl
  · intro callback member action source
    change callback ∈ rest at member
    obtain ⟨prior, after, split⟩ := List.mem_iff_append.mp member
    have laws := pending_laws valid
      (front := front ++ prior) (callback := callback) (after := after)
      (by rw [fifo, split, List.append_assoc])
    have active := valid.pendingStreams callback
      (by rw [fifo]; exact List.mem_append_right _ member) action source
    apply (streamAction_accepts_iff _ _ _ source).mpr
    apply rootStream_survives_batch buffer.queue (front.map BufferedCallback.event)
      action.1 ((streamAction_accepts_iff _ _ _ source).mp active)
    apply unclosed_of_sublist (streamAction_unclosed laws.2.1 laws.2.2 source)
    exact (List.sublist_append_left _ _).trans
      (by rw [List.map_append]; exact List.sublist_append_right _ _)
  · change ActiveStreamBatches initial
      ((buffer.batches ++ [front]).map (List.map BufferedCallback.event))
    rw [List.map_append, List.map_singleton]
    apply ActiveStreamBatches.append initial buffer.rawBatches
      [front.map BufferedCallback.event] valid.reducedStreams
    rw [← valid.current]
    exact ⟨reduceStreams, trivial⟩

/-- All invariants arise from the same interleaved derivation. No desired source/output
law or per-reduction task liveness is assumed of the resulting callback history.
-/
theorem CallbackHistory.invariant {work initial buffer}
    (history : CallbackHistory work initial buffer)
    : CallbackBuffer.Invariant work initial buffer := by
  induction history with
  | initial => exact CallbackBuffer.Invariant.initialize _ _
  | enqueue history callback running started receiptFresh matching fresh ready ih =>
      exact ih.enqueue callback started receiptFresh matching fresh ready
  | reduce history front rest fifo ih => exact ih.reduce front rest fifo

-----------------------------------------------------------------------------------------
-- One constructed semantic source and exact replay for the actual reduction batches
-----------------------------------------------------------------------------------------

/-- Consumed payloads form a work-valid prefix of the one enqueue history. -/
theorem CallbackHistory.work_valid {work initial buffer}
    (history : CallbackHistory work initial buffer)
    : ReferenceWorkQueue.ValidGraphEvents work buffer.rawBatches.flatten := by
  have valid := history.invariant
  have raw := valid.workValid
  rw [← valid.event_fifo] at raw
  exact raw.prefix ⟨buffer.pending.map BufferedCallback.event, rfl⟩

/-- Consumed and pending receipt identities partition the same unique enqueue inventory.
This proves once-only FIFO reduction, not native finally acknowledgement or cleanup.
-/
theorem CallbackHistory.receipts_partition {work initial buffer}
    (history : CallbackHistory work initial buffer)
    : (buffer.batches.flatten.map BufferedCallback.receipt
          ++ buffer.pending.map BufferedCallback.receipt)
        = buffer.received.map BufferedCallback.receipt
      ∧ (buffer.batches.flatten.map BufferedCallback.receipt).Nodup
      ∧ (buffer.pending.map BufferedCallback.receipt).Nodup
      ∧ (∀ consumed ∈ buffer.batches.flatten.map BufferedCallback.receipt,
          ∀ pending ∈ buffer.pending.map BufferedCallback.receipt,
            consumed ≠ pending) := by
  have valid := history.invariant
  have partition := congrArg (List.map BufferedCallback.receipt) valid.fifo
  rw [List.map_append] at partition
  have unique := valid.receipts
  rw [← partition, List.nodup_append] at unique
  exact ⟨partition, unique.1, unique.2.1, unique.2.2⟩

/-- The same original reduction batches have exactly the projected normalized replay.
Receipt identities stay in the host history, even when their payloads are filtered out.
-/
theorem CallbackHistory.projected_runNormalized {work buffer}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          buffer)
    : let initial :=
        ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
      initial.runNormalized (projectHistory initial buffer.rawBatches)
      = initial.runNormalized buffer.rawBatches :=
  history.projectedAtEntry_runNormalized generated nonempty

/-- Exact interleaved callback projection keeps the original semantic source contract. -/
theorem CallbackHistory.projected_source_valid {work buffer}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          buffer)
    : (EventSource.ofList
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          buffer.rawBatches)).ValidFor
        work := by
  exact history.projectedAtEntry_source_valid generated nonempty

/-- Conformance for this same history's projected source, not an independent schedule. -/
theorem CallbackHistory.projected_conforms {work buffer}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          buffer)
    : (createWorkQueueForSchedule work
        (EventSource.ofList
          (projectHistory
            (ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work))
            buffer.rawBatches))).Conforms
        work :=
  createWorkQueueForScheduleConforms_holds _ _ generated
    ((Execution.Work.isEmpty_eq_false work).mpr nonempty)
    (history.projected_source_valid generated nonempty)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
