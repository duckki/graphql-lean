import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedProducerSupport

/-! Legally enqueued boundary buffers project to the unchanged semantic source contract.
Exact replay, enqueue-time activation, and concrete producer support compose on one run.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks

open ReferenceWorkQueue (StreamAction)

-----------------------------------------------------------------------------------------
-- Reduction-time stream activation, derived separately from enqueue histories
-----------------------------------------------------------------------------------------

/-- Every stream callback is active at its actual eventwise reduction boundary. Tasks
may already be stale. This proof-side relation has no payload or publication premise.
-/
def ActiveStreamBatches (queue : ReferenceWorkQueue.State) : List (List GraphEvent) → Prop
  | [] => True
  | batch :: rest =>
      (∀ prior event after action,
        batch = prior ++ event :: after
        → event.streamAction = some action
        → (queue.replayGraphEvents prior).acceptsGraphEvent event = true)
      ∧ ActiveStreamBatches (queue.handleGraphEvents batch).1 rest

/-- The actual queue boundary after the original batches, including termination flags. -/
def replayBatches (queue : ReferenceWorkQueue.State) (batches : List (List GraphEvent))
    : ReferenceWorkQueue.State :=
  batches.foldl (fun current batch => (current.handleGraphEvents batch).1) queue

/-- A new batch extends stream activation evidence at the same actual queue boundary. -/
theorem ActiveStreamBatches.append (queue : ReferenceWorkQueue.State)
    (before after : List (List GraphEvent))
    (earlier : ActiveStreamBatches queue before)
    (later : ActiveStreamBatches (replayBatches queue before) after)
    : ActiveStreamBatches queue (before ++ after) := by
  induction before generalizing queue with
  | nil => exact later
  | cons batch rest ih => exact ⟨earlier.1, ih _ earlier.2 later⟩

-----------------------------------------------------------------------------------------
-- Eventwise filtering preserves work laws and the concrete registration invariant
-----------------------------------------------------------------------------------------

private theorem projectBatch_work_valid {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (queue : ReferenceWorkQueue.State) (before retained batch : List GraphEvent)
    (support : SourceSupport work queue retained)
    (valid : ReferenceWorkQueue.ValidGraphEvents work retained)
    (raw : ReferenceWorkQueue.ValidGraphEvents work (before ++ batch))
    (included : retained.Sublist before)
    (cursors
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    (streams
      : ∀ prior event after action,
          batch = prior ++ event :: after
          → event.streamAction = some action
          → (queue.replayGraphEvents prior).acceptsGraphEvent event = true)
    : ReferenceWorkQueue.ValidGraphEvents work (retained ++ projectBatch queue batch)
      ∧ SourceSupport work (queue.replayGraphEvents batch)
          (retained ++ projectBatch queue batch)
      ∧ ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore (retained ++ projectBatch queue batch)
            key
          = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ batch) key := by
  induction batch generalizing queue before retained with
  | nil => simpa only [projectBatch, ReferenceWorkQueue.State.replayGraphEvents,
      List.foldl_nil, List.append_nil] using And.intro valid (And.intro support cursors)
  | cons event rest ih =>
      have laws := raw.atPrefix (before := before) (event := event)
        ⟨rest, by simp only [List.append_assoc, List.singleton_append]⟩
      have tailRaw : ReferenceWorkQueue.ValidGraphEvents work ((before ++ [event]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using raw
      have tailStreams : ∀ prior current after action,
          rest = prior ++ current :: after → current.streamAction = some action
          → ((queue.handleGraphEvent event).1.replayGraphEvents prior).acceptsGraphEvent
              current = true := by
        intro prior current after action split source
        exact streams (event :: prior) current after action
          (by simp only [List.cons_append]; rw [split]) source
      cases live : queue.acceptsGraphEvent event with
      | true =>
          have nextValid := ReferenceWorkQueue.ValidGraphEvents.append valid laws.1
            (fresh_of_sublist laws.2.1 included)
            (support.ready generated laws.1 laws.2.2 live included cursors)
          have nextSupport := support.handleGraphEvent generated laws.1
          have nextCursors : ∀ key,
              ReferenceWorkQueue.GraphEvent.itemsBefore (retained ++ [event]) key
                = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ [event]) key := by
            intro key
            rw [ReferenceWorkQueue.GraphEvent.itemsBefore_append,
              ReferenceWorkQueue.GraphEvent.itemsBefore_append, cursors key]
          have next := ih (queue.handleGraphEvent event).1 (before ++ [event])
            (retained ++ [event]) nextSupport nextValid tailRaw
            (included.append (.refl [event])) nextCursors tailStreams
          simpa only [projectBatch, live, ↓reduceIte,
            ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons,
            List.append_assoc, List.singleton_append]
            using next
      | false =>
          have ignored := stale_handleGraphEvent queue event live
          have noAction : event.streamAction = none := by
            cases action : event.streamAction with
            | none => rfl
            | some current =>
                have accepted := streams [] event rest current rfl action
                simp only [ReferenceWorkQueue.State.replayGraphEvents, List.foldl_nil] at accepted
                rw [live] at accepted
                cases accepted
          have noItems (key : Nat)
              : ReferenceWorkQueue.GraphEvent.itemsBefore [event] key = [] := by
            cases event with
            | taskSuccess | taskFailure | streamSuccess | streamFailure => rfl
            | streamItems stream items => cases noAction
          have nextCursors : ∀ key,
              ReferenceWorkQueue.GraphEvent.itemsBefore retained key
                = ReferenceWorkQueue.GraphEvent.itemsBefore (before ++ [event]) key := by
            intro key
            rw [ReferenceWorkQueue.GraphEvent.itemsBefore_append, noItems, List.append_nil]
            exact cursors key
          have next := ih queue (before ++ [event]) retained support valid tailRaw
            (included.trans (List.sublist_append_left _ _)) nextCursors
            (by simpa only [ignored] using tailStreams)
          simpa only [projectBatch, live, Bool.false_eq_true, ↓reduceIte,
            ReferenceWorkQueue.State.replayGraphEvents, List.foldl_cons, ignored,
            List.append_assoc, List.singleton_append]
            using next

-----------------------------------------------------------------------------------------
-- Batch-end flags and silent-batch erasure preserve one retained work-valid history
-----------------------------------------------------------------------------------------

/-- A terminated boundary has no further effective semantic inputs. Raw receipts and
native finally/disposal evidence remain separate; this erases only the source projection.
-/
theorem projectHistory_of_terminated (queue : ReferenceWorkQueue.State)
    (batches : List (List GraphEvent)) (ended : queue.terminated = true)
    : projectHistory queue batches = [] := by
  induction batches with
  | nil => rfl
  | cons batch rest ih =>
      simp only [projectHistory, ended, ↓reduceIte,
        queue.handleGraphEvents_after_termination batch ended, List.isEmpty_nil]
      exact ih

theorem projectHistory_work_valid_of_streams {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (queue : ReferenceWorkQueue.State) (before retained : List GraphEvent)
    (batches : List (List GraphEvent))
    (streams : ActiveStreamBatches queue batches)
    (raw : ReferenceWorkQueue.ValidGraphEvents work (before ++ batches.flatten))
    (valid : ReferenceWorkQueue.ValidGraphEvents work retained)
    (included : retained.Sublist before)
    (cursors
      : ∀ key,
          ReferenceWorkQueue.GraphEvent.itemsBefore retained key
          = ReferenceWorkQueue.GraphEvent.itemsBefore before key)
    (support : SourceSupport work queue retained)
    : ReferenceWorkQueue.ValidGraphEvents work
        (retained ++ (projectHistory queue batches).flatten) := by
  induction batches generalizing queue before retained with
  | nil => simpa only [projectHistory, List.flatten_nil, List.append_nil] using valid
  | cons batch rest ih =>
      cases ended : queue.terminated with
      | true => simpa only [projectHistory_of_terminated queue (batch :: rest) ended,
          List.flatten_nil, List.append_nil] using valid
      | false =>
          have rawBatch := raw.prefix (before := before ++ batch)
            ⟨rest.flatten, by simp only [List.flatten_cons, List.append_assoc]⟩
          have laterRaw : ReferenceWorkQueue.ValidGraphEvents work
              ((before ++ batch) ++ rest.flatten) := by
            simpa only [List.flatten_cons, List.append_assoc] using raw
          have current := projectBatch_work_valid generated queue before retained batch
            support valid rawBatch included cursors streams.1
          obtain ⟨terminal, state⟩ := queue.handleGraphEvents_stateCore batch ended
          have nextSupport : SourceSupport work (queue.handleGraphEvents batch).1
              (retained ++ projectBatch queue batch) := by
            rw [state]
            exact current.2.1.withTerminated terminal
          have next := ih (queue.handleGraphEvents batch).1 (before ++ batch)
            (retained ++ projectBatch queue batch) streams.2 laterRaw current.1
            (included.append (projectBatch_sublist queue batch)) current.2.2 nextSupport
          simp only [projectHistory, ended, Bool.false_eq_true, ↓reduceIte]
          cases empty : (projectBatch queue batch).isEmpty with
          | true =>
              have noEvents : projectBatch queue batch = [] := List.isEmpty_iff.mp empty
              simpa only [empty, ↓reduceIte, noEvents, List.append_nil] using next
          | false =>
              simpa only [empty, Bool.false_eq_true, ↓reduceIte,
                List.flatten_cons, List.append_assoc] using next

/-- Boundary buffers supply activation at every actual reduction position. General
interleaved histories can establish this same relation without a fixed enqueue boundary.
-/
theorem BoundaryBuffers.activeStreams {work queue before batches}
    (buffers : BoundaryBuffers work queue before batches)
    (raw : ReferenceWorkQueue.ValidGraphEvents work before)
    : ActiveStreamBatches queue batches := by
  induction batches generalizing queue before with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨⟨callbacks, queued, same⟩, later⟩ := buffers
      refine ⟨?_, ih later ?_⟩
      · intro prior event after action split source
        exact queued.streamAction_accepted raw (same.trans split) source
      · simpa only [same] using queued.work_valid raw

-----------------------------------------------------------------------------------------
-- Proof witnesses for the unchanged source and queue-conformance interfaces
-----------------------------------------------------------------------------------------

/-- Boundary-buffer admission preserves the original work laws after semantic filtering.
No public definition or source contract is weakened. This does not yet construct native
interleaved callback histories, scheduled execution, or whole-run receipt/resource evidence.
-/
theorem bufferedWorkProjection_holds : BufferedWorkProjection := by
  intro work batches generated _ buffers
  simpa only [List.nil_append] using projectHistory_work_valid_of_streams generated
    (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work))
    [] [] batches (buffers.activeStreams .nil) (buffers.work_valid .nil) .nil (.refl [])
    (fun _ => rfl) (SourceSupport.initialize work)

/-- The projected source itself satisfies all original prefix and start/work laws. -/
theorem projected_source_valid {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) [] batches)
    : (EventSource.ofList
        (projectHistory
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          batches)).ValidFor
        work := by
  obtain ⟨valid, started⟩ := projected_sourceLaws_of_workProjection bufferedWorkProjection_holds
    generated nonempty batches buffers
  exact source_valid_of_laws _ valid started

/-- Legally enqueued boundary buffers yield conformance for their actual projected
alternative factory. Queue/publisher replay is exact, but native refinement is separate.
-/
theorem projected_conforms {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (batches : List (List GraphEvent))
    (buffers
      : BoundaryBuffers work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) [] batches)
    : (createWorkQueueForSchedule work
        (EventSource.ofList
          (projectHistory
            (ReferenceWorkQueue.State.initialize
              (ReferenceWorkQueue.Work.fromExecution work))
            batches))).Conforms
        work :=
  projected_conforms_of_workProjection bufferedWorkProjection_holds generated nonempty
    batches buffers

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
