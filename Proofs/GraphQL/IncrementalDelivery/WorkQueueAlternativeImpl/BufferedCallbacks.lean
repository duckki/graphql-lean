import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GraphEffectProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConstructorInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemRootCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance

/-! Remove callbacks whose producers have retired before reduction. This projection
preserves the shared queue's exact batch result, not just reconstructed data. It does
not erase native receipts or claim that arbitrary raw callback histories are legal.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Retired inputs are semantic no-ops, but item receipts still require acknowledgement
-----------------------------------------------------------------------------------------

/-- Losing live membership makes every shared handler a literal no-op. -/
theorem stale_handleGraphEvent (queue : ReferenceWorkQueue.State) (event : GraphEvent)
    (stale : queue.acceptsGraphEvent event = false)
    : queue.handleGraphEvent event = (queue, []) := by
  cases event with
  | taskSuccess task result =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.taskSuccess,
        absent]
  | taskFailure task errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.taskFailure,
        absent]
  | streamItems stream items =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamItems,
        stale, Bool.not_false, ↓reduceIte]
  | streamSuccess stream =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamSuccess,
        stale, Bool.false_eq_true, ↓reduceIte]
  | streamFailure stream errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamFailure,
        stale, Bool.false_eq_true, ↓reduceIte]

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
    : state.handleGraphEvent event = (state, [], staleEffects event) := by
  cases event with
  | taskSuccess task result =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : state.queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp only [State.handleGraphEvent, State.taskSuccess, absent, staleEffects]
  | streamItems stream items =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      simp only [State.handleGraphEvent, State.streamItems, stale, Bool.not_false,
        ↓reduceIte, staleEffects]
  | taskFailure task errors =>
      simp only [ReferenceWorkQueue.State.acceptsGraphEvent] at stale
      have absent : state.queue.taskNode? task = none :=
        Option.isNone_iff_eq_none.mp (Option.isSome_eq_false_iff.mp stale)
      simp only [State.handleGraphEvent, State.taskFailure, absent, staleEffects]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, staleEffects,
        stale_handleGraphEvent state.queue (.streamSuccess stream) stale]
  | streamFailure stream errors =>
      have absent : state.queue.rootStreams.contains stream.ref = false := stale
      simp only [State.handleGraphEvent, staleEffects, absent, Bool.false_eq_true, ↓reduceIte,
        stale_handleGraphEvent state.queue (.streamFailure stream errors) stale]

/-- Full dispatch is a semantic no-op plus exactly the stale receipt's inline effects.
Neither registration nor failure cleanup can be invented by the ignored payload.
-/
theorem stale_dispatch (before : GraphBatchResult) (event : GraphEvent)
    (stale : before.state.queue.acceptsGraphEvent event = false)
    : before.handleGraphEvent event
      = { before with effects := before.effects ++ staleEffects event } := by
  simp only [GraphBatchResult.handleGraphEvent,
    stale_alternativeHandleGraphEvent before.state event stale, List.append_nil]

-----------------------------------------------------------------------------------------
-- Enqueue permission precedes reduction; receipts retain distinct callback identities
-----------------------------------------------------------------------------------------

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

-----------------------------------------------------------------------------------------
-- Effective inputs retain their original order and one batch-end termination boundary
-----------------------------------------------------------------------------------------

/-- Filter against each actual intermediate queue, not the batch's final state.
Already-buffered stale callbacks disappear only from the semantic input projection.
-/
def projectBatch (queue : ReferenceWorkQueue.State) : List GraphEvent → List GraphEvent
  | [] => []
  | event :: rest =>
      if queue.acceptsGraphEvent event then
        event :: projectBatch (queue.handleGraphEvent event).1 rest
      else
        projectBatch queue rest

private abbrev rawStep (acc : ReferenceWorkQueue.State × List WorkQueueEvent)
    (event : GraphEvent)
    : ReferenceWorkQueue.State × List WorkQueueEvent :=
  let next := acc.1.handleGraphEvent event
  (next.1, acc.2 ++ next.2)

/-- The projection changes neither handler state nor ordered raw publications. -/
theorem projectBatch_fold (queue : ReferenceWorkQueue.State)
    (events : List WorkQueueEvent) (batch : List GraphEvent)
    : (projectBatch queue batch).foldl rawStep (queue, events)
      = batch.foldl rawStep (queue, events) := by
  induction batch generalizing queue events with
  | nil => rfl
  | cons event rest ih =>
      simp only [projectBatch]
      split
      · simp only [List.foldl_cons]
        exact ih _ _
      · rename_i absent
        have stale : queue.acceptsGraphEvent event = false := Bool.eq_false_iff.mpr absent
        rw [List.foldl_cons]
        simp only [rawStep, stale_handleGraphEvent queue event stale, List.append_nil]
        exact ih queue events

/-- Every retained event passes the existing sequential membership check. -/
theorem projectBatch_accepts (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : queue.acceptsBatch (projectBatch queue batch) = true := by
  induction batch generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      simp only [projectBatch]
      split
      · rename_i active
        simp only [ReferenceWorkQueue.State.acceptsBatch, active, Bool.true_and]
        exact ih _
      · exact ih queue

/-- Filtering never reorders, duplicates or invents a callback. -/
theorem projectBatch_sublist (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : (projectBatch queue batch).Sublist batch := by
  induction batch generalizing queue with
  | nil => exact .refl _
  | cons event rest ih =>
      simp only [projectBatch]
      split
      · exact .cons_cons _ (ih _)
      · exact .cons _ (ih queue)

/-- Batch-end termination happens once at the original boundary, even when filtering
removes the entire batch. Source admission of an empty projection is a separate question.
-/
theorem projectBatch_handleGraphEvents (queue : ReferenceWorkQueue.State)
    (batch : List GraphEvent)
    : queue.handleGraphEvents (projectBatch queue batch)
      = queue.handleGraphEvents batch := by
  unfold ReferenceWorkQueue.State.handleGraphEvents
  split
  · rfl
  · have same := projectBatch_fold queue [] batch
    change (projectBatch queue batch).foldl
      (fun acc event =>
        let next := acc.1.handleGraphEvent event
        (next.1, acc.2 ++ next.2)) (queue, []) = _ at same
    rw [same]

/-- Filter at the actual alternative handler's sequential states, not an arbitrary reference
catalogue. The reference projection above remains its own algorithm and admission proof.
-/
def projectAlternativeBatch (state : State) : List GraphEvent → List GraphEvent
  | [] => []
  | event :: rest =>
      if state.queue.acceptsGraphEvent event then
        event :: projectAlternativeBatch (state.handleGraphEvent event).1 rest
      else
        projectAlternativeBatch state rest

private abbrev alternativeKernelStep (acc : State × List WorkQueueEvent)
    (event : GraphEvent) :=
  let next := acc.1.handleGraphEvent event
  (next.1, acc.2 ++ next.2.1)

private theorem alternativeFold_kernel (batch : List GraphEvent)
    (result : GraphBatchResult)
    : batch.foldl alternativeKernelStep (result.state, result.workQueueEvents)
      = (
        (batch.foldl GraphBatchResult.handleGraphEvent result).state,
        (batch.foldl GraphBatchResult.handleGraphEvent result).workQueueEvents
      ) := by
  apply List.foldl_hom (fun result : GraphBatchResult => (result.state, result.workQueueEvents))
    (g₁ := GraphBatchResult.handleGraphEvent) (g₂ := alternativeKernelStep)
  intro current event
  rfl

private theorem projectAlternativeBatch_fold (state : State)
    (events : List WorkQueueEvent) (batch : List GraphEvent)
    : (projectAlternativeBatch state batch).foldl alternativeKernelStep (state, events)
      = batch.foldl alternativeKernelStep (state, events) := by
  induction batch generalizing state events with
  | nil => rfl
  | cons event rest ih =>
      simp only [projectAlternativeBatch]
      split
      · rw [List.foldl_cons, List.foldl_cons]
        exact ih _ _
      · rename_i absent
        have stale : state.queue.acceptsGraphEvent event = false := Bool.eq_false_iff.mpr absent
        rw [List.foldl_cons]
        simp only [alternativeKernelStep, stale_alternativeHandleGraphEvent state event stale,
          List.append_nil]
        exact ih state events

/-- Actual-state callback filtering preserves the alternative's complete accounting and raw
publications, including terminal retirement. Effects are deliberately not equated: removed
item receipts still require their own acknowledgement/producer-suffix cleanup evidence.
-/
theorem projectBatch_alternative (state : State) (batch : List GraphEvent)
    : let raw := state.handleGraphEvents batch
      let effective := state.handleGraphEvents (projectAlternativeBatch state batch)
      effective.state = raw.state ∧ effective.workQueueEvents = raw.workQueueEvents := by
  have raw := alternativeFold_kernel batch ({ state } : GraphBatchResult)
  have effective := alternativeFold_kernel (projectAlternativeBatch state batch)
    ({ state } : GraphBatchResult)
  rw [projectAlternativeBatch_fold] at effective
  have folded := effective.symm.trans raw
  have sameState := congrArg Prod.fst folded
  have sameEvents := congrArg Prod.snd folded
  dsimp only at sameState sameEvents
  have same : ((state.handleGraphEvents (projectAlternativeBatch state batch)).state,
        (state.handleGraphEvents (projectAlternativeBatch state batch)).workQueueEvents)
      = ((state.handleGraphEvents batch).state, (state.handleGraphEvents batch).workQueueEvents) := by
    simp only [State.handleGraphEvents]
    split
    · rfl
    · simp only [sameState, sameEvents]
      split
      · rfl
      · exact folded
  exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

-----------------------------------------------------------------------------------------
-- Silent receipts and late callbacks do not manufacture admitted empty batches
-----------------------------------------------------------------------------------------

/-- At a real batch boundary an unfinished queue still has a root. Raw empty-root,
nonterminal states can emit termination on an empty batch and must not be silently erased.
-/
def Boundary (queue : ReferenceWorkQueue.State) : Prop :=
  queue.terminated = true
  ∨ (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) = false

theorem Boundary.after_batch (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    : Boundary (queue.handleGraphEvents batch).1 := by
  unfold ReferenceWorkQueue.State.handleGraphEvents
  by_cases ended : queue.terminated = true
  · simp only [ended, ↓reduceIte]
    exact Or.inl ended
  · simp only [ended, Bool.false_eq_true, ↓reduceIte]
    split
    · exact Or.inl rfl
    · exact Or.inr (Bool.eq_false_iff.mpr (by assumption))

/-- Empty effective batches are erased only at sound boundaries. No terminated source
is reopened; receipt/resource observations remain attached to the raw host history.
-/
def projectHistory (queue : ReferenceWorkQueue.State)
    : List (List GraphEvent) → List (List GraphEvent)
  | [] => []
  | batch :: rest =>
      let effective := if queue.terminated then [] else projectBatch queue batch
      let later := projectHistory (queue.handleGraphEvents batch).1 rest
      if effective.isEmpty then later else effective :: later

private theorem silent_batch (queue : ReferenceWorkQueue.State) (batch : List GraphEvent)
    (boundary : Boundary queue)
    (silent : (if queue.terminated then [] else projectBatch queue batch) = [])
    : queue.handleGraphEvents batch = (queue, []) := by
  cases ended : queue.terminated with
  | true => simp [ReferenceWorkQueue.State.handleGraphEvents, ended]
  | false =>
      have roots : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) = false := by
        rcases boundary with terminated | roots
        · rw [ended] at terminated
          contradiction
        · exact roots
      simp only [ended, Bool.false_eq_true, ↓reduceIte] at silent
      rw [← projectBatch_handleGraphEvents, silent]
      simp only [ReferenceWorkQueue.State.handleGraphEvents, ended, Bool.false_eq_true,
        ↓reduceIte, List.foldl_nil, roots]

/-- The membership/termination half of source admission, starting at an arbitrary queue. -/
def startedFrom (queue : ReferenceWorkQueue.State) : List (List GraphEvent) → Bool
  | [] => true
  | batch :: rest =>
      !queue.terminated
      && !batch.isEmpty
      && queue.acceptsBatch batch
      && startedFrom (queue.handleGraphEvents batch).1 rest

/-- The unchanged public fold is this same sequential source check. -/
theorem inputsStarted_eq (work : Work) (batches : List (List GraphEvent))
    : ReferenceWorkQueue.inputsStarted work batches
      = startedFrom
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches := by
  have fold (queue : ReferenceWorkQueue.State) (valid : Bool)
      : (batches.foldl
          (fun (state, valid) batch =>
            ((state.handleGraphEvents batch).1,
              valid && !state.terminated && !batch.isEmpty && state.acceptsBatch batch))
          (queue, valid)).2
        = (valid && startedFrom queue batches) := by
    induction batches generalizing queue valid with
    | nil => simp [startedFrom]
    | cons batch rest ih =>
        rw [List.foldl_cons, ih]
        simp only [startedFrom, Bool.and_assoc]
  exact (fold _ true).trans (Bool.true_and _)

/-- Filtering and erasing silent batches derive inputsStarted; it is not assumed of
the raw buffered history, which can fail that check after an earlier failure prunes work.
-/
theorem projectHistory_started (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (boundary : Boundary queue)
    : startedFrom queue (projectHistory queue batches) = true := by
  induction batches generalizing queue with
  | nil => rfl
  | cons batch rest ih =>
      simp only [projectHistory]
      cases ended : queue.terminated with
      | true =>
          simp only [↓reduceIte, List.isEmpty_nil]
          have unchanged : (queue.handleGraphEvents batch).1 = queue := by
            simp [ReferenceWorkQueue.State.handleGraphEvents, ended]
          rw [unchanged]
          exact ih queue boundary
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          split
          · rename_i silent
            have empty : projectBatch queue batch = [] := List.isEmpty_iff.mp silent
            have noOp := silent_batch queue batch boundary
              (by simp only [ended, Bool.false_eq_true, ↓reduceIte, empty])
            rw [noOp]
            exact ih queue boundary
          · rename_i nonempty
            simp only [startedFrom, ended, Bool.not_false, Bool.true_and,
              projectBatch_accepts, Bool.and_true, projectBatch_handleGraphEvents]
            have live : (projectBatch queue batch).isEmpty = false :=
              Bool.eq_false_iff.mpr nonempty
            rw [live]
            exact ih _ (Boundary.after_batch _ _)

/-- Same publisher, output order and surviving batch boundaries over a whole history.
This theorem needs no work-generation or input-legality premise, only a sound initial
boundary. It does not claim ignored native receipts disappear from the effect trace.
-/
theorem projectHistory_runWithPublisher (queue : ReferenceWorkQueue.State)
    (publisher : ReferenceWorkQueue.IncrementalPublisher)
    (batches : List (List GraphEvent)) (boundary : Boundary queue)
    : queue.runWithPublisher publisher (projectHistory queue batches)
      = queue.runWithPublisher publisher batches := by
  let step := fun
    (acc : ReferenceWorkQueue.State × ReferenceWorkQueue.IncrementalPublisher
      × List (List WorkQueueEvent)) (batch : List GraphEvent) =>
      let next := acc.1.handleGraphEvents batch
      if next.2.isEmpty then (next.1, acc.2.1, acc.2.2)
      else
        let mapped := acc.2.1.normalizeBatch next.2
        (next.1, mapped.1, acc.2.2 ++ [mapped.2])
  have fold (outputs : List (List WorkQueueEvent))
      : (projectHistory queue batches).foldl step (queue, publisher, outputs)
        = batches.foldl step (queue, publisher, outputs) := by
    induction batches generalizing queue publisher outputs with
    | nil => rfl
    | cons batch rest ih =>
        let effective := if queue.terminated then [] else projectBatch queue batch
        change (if effective.isEmpty then projectHistory (queue.handleGraphEvents batch).1 rest
          else effective :: projectHistory (queue.handleGraphEvents batch).1 rest).foldl step
            (queue, publisher, outputs) = (batch :: rest).foldl step (queue, publisher, outputs)
        have nextBoundary := Boundary.after_batch queue batch
        by_cases silent : effective = []
        · have noOp := silent_batch queue batch boundary silent
          simp only [silent, List.isEmpty_nil, ↓reduceIte,
            noOp, List.foldl_cons]
          have unchanged : step (queue, publisher, outputs) batch =
              (queue, publisher, outputs) := by simp only [step, noOp, List.isEmpty_nil, ↓reduceIte]
          rw [unchanged]
          exact ih queue publisher boundary outputs
        · have live : queue.terminated = false := by
            cases ended : queue.terminated
            · rfl
            · simp [effective, ended] at silent
          have nonempty : effective.isEmpty = false := by
            exact Bool.eq_false_iff.mpr (fun empty => silent (List.isEmpty_iff.mp empty))
          have same : queue.handleGraphEvents effective = queue.handleGraphEvents batch := by
            simp only [effective, live, Bool.false_eq_true, ↓reduceIte]
            exact projectBatch_handleGraphEvents _ _
          have next : step (queue, publisher, outputs) effective
              = step (queue, publisher, outputs) batch := by simp only [step, same]
          simp only [nonempty, Bool.false_eq_true, ↓reduceIte,
            List.foldl_cons, next]
          have component : (step (queue, publisher, outputs) batch).1
              = (queue.handleGraphEvents batch).1 := by simp only [step]; split <;> rfl
          have validNext : Boundary (step (queue, publisher, outputs) batch).1 := by
            rw [component]
            exact nextBoundary
          rw [← component]
          exact ih _ _ validNext _
  exact fold []

theorem projectHistory_runNormalized (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (boundary : Boundary queue)
    : queue.runNormalized (projectHistory queue batches)
      = queue.runNormalized batches := by
  unfold ReferenceWorkQueue.State.runNormalized
  dsimp only
  rw [projectHistory_runWithPublisher queue _ batches boundary]

-----------------------------------------------------------------------------------------
-- Generated initialization and the unchanged semantic source contract
-----------------------------------------------------------------------------------------

/-- Nonempty executed work supplies the boundary condition; callers need not assume
that initial roots exist independently of execution and constructor correctness.
-/
theorem initialized_boundary {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    : Boundary
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)) := by
  let queue := ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
  refine Or.inr (Bool.eq_false_iff.mpr ?_)
  intro empty
  obtain ⟨groupsEmpty, streamsEmpty⟩ := Bool.and_eq_true_iff.mp empty
  have groups : queue.rootGroups = [] := List.isEmpty_iff.mp groupsEmpty
  have streams : queue.rootStreams = [] := List.isEmpty_iff.mp streamsEmpty
  have notices := generated.initialNotices_nonempty nonempty
  have absentGroups : queue.initialGroups = [] := by
    rw [ReferenceWorkQueue.createWorkQueue_rootGroups] at groups
    exact List.map_eq_nil_iff.mp groups
  have absentStreams : queue.initialStreams = [] := by
    cases entries : queue.initialStreams with
    | nil => rfl
    | cons stream rest =>
        have member : stream ∈ queue.initialStreams := by simp only [entries, List.mem_cons, true_or]
        have active := ReferenceWorkQueue.createWorkQueue_initialStreams_active
          (ReferenceWorkQueue.Work.fromExecution work) (List.mem_map_of_mem member)
        change stream.ref ∈ queue.rootStreams at active
        rw [streams] at active
        cases active
  exact notices (by rw [absentGroups, absentStreams]; rfl)

theorem projected_inputsStarted {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (batches : List (List GraphEvent))
    : ReferenceWorkQueue.inputsStarted work
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches)
      = true := by
  rw [inputsStarted_eq]
  exact projectHistory_started _ _ (initialized_boundary generated nonempty)

/-- Work-law projection is distinct from membership projection. Work legality alone
is insufficient: premature items of a held stream can be ignored, then the stream
can activate with a shifted raw cursor. Enqueue-time eligibility excludes that case.
This target concerns BoundaryBuffers, not arbitrary raw work-valid histories or all
interleaved native callbacks. Its witness lives in BufferedWorkProjection; it is neither
an axiom nor a public source premise.
-/
def BufferedWorkProjection : Prop :=
  ∀ (work : Work) (batches : List (List GraphEvent)),
    ReferenceWorkQueue.ExecutedWork work
    → work.size ≠ 0
    → BoundaryBuffers work
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)) [] batches
    → ReferenceWorkQueue.ValidGraphEvents work
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches).flatten

/-- Composition edge using the separate work-law witness, not just exact queue replay.
No desired output accounting or wire property is assumed to obtain source discipline.
-/
theorem projected_sourceLaws_of_workProjection (projection : BufferedWorkProjection)
    {work : Work} (generated : ReferenceWorkQueue.ExecutedWork work)
    (nonempty : work.size ≠ 0) (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          [] batches)
    : let inputs :=
        projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches
      ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
      ∧ ReferenceWorkQueue.inputsStarted work inputs = true :=
  ⟨
    projection work batches generated nonempty buffers,
    projected_inputsStarted generated nonempty batches
  ⟩

private theorem startedFrom_append_left (queue : ReferenceWorkQueue.State)
    (before after : List (List GraphEvent))
    (valid : startedFrom queue (before ++ after) = true)
    : startedFrom queue before = true := by
  induction before generalizing queue with
  | nil => rfl
  | cons batch rest ih =>
      simp only [List.cons_append, startedFrom] at valid ⊢
      obtain ⟨current, later⟩ := Bool.and_eq_true_iff.mp valid
      exact Bool.and_eq_true_iff.mpr ⟨current, ih _ later⟩

/-- A full finite semantic history supplies every prefix of its existing ofList source.
This connects the projection to the actual unchanged ValidFor contract, not a weaker
replacement source predicate. No wire/output property is included in the premise.
-/
theorem source_valid_of_laws {work : Work} (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : (EventSource.ofList inputs).ValidFor work := by
  refine ⟨rfl, List.nil_prefix, ?_, ?_⟩
  · intro before after earlier admitted
    exact earlier.trans admitted
  · intro before admitted
    obtain ⟨after, rfl⟩ := admitted
    refine ⟨valid.prefix ⟨after.flatten, ?_⟩, ?_⟩
    · rw [List.flatten_append]
    · rw [inputsStarted_eq] at started ⊢
      exact startedFrom_append_left _ before after started

/-- Conformance composition using a separate work-law witness. That witness alone does
not certify native enqueue/receipt correspondence or full interleaved callback histories.
-/
theorem projected_conforms_of_workProjection (projection : BufferedWorkProjection)
    {work : Work} (generated : ReferenceWorkQueue.ExecutedWork work)
    (nonempty : work.size ≠ 0) (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          [] batches)
    : let inputs :=
        projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches
      (createWorkQueueForSchedule work (EventSource.ofList inputs)).Conforms work := by
  obtain ⟨matching, started⟩ := projected_sourceLaws_of_workProjection projection
    generated nonempty batches buffers
  exact createWorkQueueForScheduleConforms_holds _ _ generated nonempty
    (source_valid_of_laws _ matching started)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
