import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartup
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CallbackProjectionBoundary
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Exact normalized replay and source admission over a whole projected callback history.
All per-batch source evidence is constructed independently from enqueue histories.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

/-- The current effective batch has the original batch's exact queue and output result. -/
theorem CallbackProjectionSource.head_exact {work queue before retained batch rest}
    (sources : CallbackProjectionSource work queue before retained (batch :: rest))
    : queue.handleGraphEvents
        (if queue.terminated then [] else projectBatchAtEntry queue batch)
      = queue.handleGraphEvents batch := by
  cases ended : queue.terminated with
  | true => simp only [↓reduceIte, queue.handleGraphEvents_after_termination _ ended]
  | false =>
      simp only [CallbackProjectionSource, ended, Bool.false_eq_true, ↓reduceIte] at sources ⊢
      exact sources.1.projectBatchAtEntry_exact sources.2.1

/-- The source certificate advances at the actual raw endpoint, including ignored late input. -/
theorem CallbackProjectionSource.tail {work queue before retained batch rest}
    (sources : CallbackProjectionSource work queue before retained (batch :: rest))
    : CallbackProjectionSource work (queue.handleGraphEvents batch).1 (before ++ batch)
        (retained ++ (if queue.terminated then [] else projectBatchAtEntry queue batch))
        rest := by
  cases ended : queue.terminated with
  | true =>
      have valid : ReferenceWorkQueue.ValidGraphEvents work retained := by
        simpa only [CallbackProjectionSource, ended, ↓reduceIte] using sources
      cases rest <;> simpa only [CallbackProjectionSource, ended, ↓reduceIte,
        queue.handleGraphEvents_after_termination batch ended, List.append_nil] using valid
  | false =>
      simp only [CallbackProjectionSource, ended, Bool.false_eq_true, ↓reduceIte] at sources ⊢
      exact sources.2.2

private theorem silent_batch {work queue before retained batch rest}
    (sources : CallbackProjectionSource work queue before retained (batch :: rest))
    (boundary : Boundary queue)
    (silent : (if queue.terminated then [] else projectBatchAtEntry queue batch) = [])
    : queue.handleGraphEvents batch = (queue, []) := by
  cases ended : queue.terminated with
  | true => exact queue.handleGraphEvents_after_termination batch ended
  | false =>
      have roots : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty && queue.groupFailureEvents.isEmpty) = false := by
        rcases boundary with terminated | roots
        · rw [ended] at terminated; contradiction
        · exact roots
      rw [← sources.head_exact, silent]
      simp only [ReferenceWorkQueue.State.handleGraphEvents, ended, Bool.false_eq_true,
        ↓reduceIte, List.foldl_nil, roots]

/-- Construct the unchanged executable source checker for the projected finite history. -/
theorem CallbackProjectionSource.started {work queue before retained batches}
    (sources : CallbackProjectionSource work queue before retained batches)
    (boundary : Boundary queue)
    : startedFrom queue (projectHistoryAtEntry queue batches) = true := by
  induction batches generalizing queue before retained with
  | nil => rfl
  | cons batch rest ih =>
      cases ended : queue.terminated with
      | true => rw [projectHistoryAtEntry_of_terminated queue (batch :: rest) ended]; rfl
      | false =>
          have later := ih sources.tail (Boundary.after_batch queue batch)
          simp only [projectHistoryAtEntry, ended, Bool.false_eq_true, ↓reduceIte]
          cases empty : (projectBatchAtEntry queue batch).isEmpty with
          | true =>
              have nil : projectBatchAtEntry queue batch = [] := List.isEmpty_iff.mp empty
              have noOp := silent_batch sources boundary
                (by simp only [ended, Bool.false_eq_true, ↓reduceIte, nil])
              simp only [↓reduceIte]
              rw [noOp] at later ⊢
              exact later
          | false =>
              simp only [empty, Bool.false_eq_true, ↓reduceIte, startedFrom, ended,
                Bool.not_false, Bool.true_and, Bool.and_true]
              have same := sources.head_exact
              simp only [ended, Bool.false_eq_true, ↓reduceIte] at same
              rw [same]
              apply Bool.and_eq_true_iff.mpr
              refine ⟨?_, later⟩
              have evidence := sources
              simp only [CallbackProjectionSource, ended, Bool.false_eq_true, ↓reduceIte] at evidence
              have unique := evidence.1.valid.identities_nodup.2
              rw [List.flatMap_append] at unique
              exact projectBatchAtEntry_accepts queue batch (List.nodup_append.mp unique).2.1

/-- The actual publisher fold preserves state, output order and surviving batch boundaries. -/
theorem CallbackProjectionSource.runWithPublisher {work queue before retained batches}
    (sources : CallbackProjectionSource work queue before retained batches)
    (publisher : ReferenceWorkQueue.IncrementalPublisher) (boundary : Boundary queue)
    : queue.runWithPublisher publisher (projectHistoryAtEntry queue batches)
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
      : (projectHistoryAtEntry queue batches).foldl step (queue, publisher, outputs)
        = batches.foldl step (queue, publisher, outputs) := by
    induction batches generalizing queue before retained publisher outputs with
    | nil => rfl
    | cons batch rest ih =>
        let effective := if queue.terminated then [] else projectBatchAtEntry queue batch
        change (if effective.isEmpty then
          projectHistoryAtEntry (queue.handleGraphEvents batch).1 rest
          else effective :: projectHistoryAtEntry (queue.handleGraphEvents batch).1 rest).foldl step
            (queue, publisher, outputs) = (batch :: rest).foldl step (queue, publisher, outputs)
        have nextBoundary := Boundary.after_batch queue batch
        have nextSource := sources.tail
        by_cases silent : effective = []
        · have noOp := silent_batch sources boundary silent
          simp only [silent, List.isEmpty_nil, ↓reduceIte, noOp, List.foldl_cons]
          have unchanged : step (queue, publisher, outputs) batch =
              (queue, publisher, outputs) := by simp only [step, noOp, List.isEmpty_nil, ↓reduceIte]
          rw [unchanged]
          rw [noOp] at nextSource
          exact ih nextSource publisher boundary outputs
        · have nonempty : effective.isEmpty = false :=
            Bool.eq_false_iff.mpr (fun empty => silent (List.isEmpty_iff.mp empty))
          have same : queue.handleGraphEvents effective = queue.handleGraphEvents batch :=
            sources.head_exact
          have next : step (queue, publisher, outputs) effective
              = step (queue, publisher, outputs) batch := by simp only [step, same]
          simp only [nonempty, Bool.false_eq_true, ↓reduceIte, List.foldl_cons, next]
          have component : (step (queue, publisher, outputs) batch).1
              = (queue.handleGraphEvents batch).1 := by simp only [step]; split <;> rfl
          have validNext : Boundary (step (queue, publisher, outputs) batch).1 := by
            rw [component]; exact nextBoundary
          rw [← component] at nextSource ⊢
          exact ih nextSource _ validNext _
  exact fold []

/-- Normalize using the same original initial publisher and derived source certificate. -/
theorem CallbackProjectionSource.runNormalized {work queue before retained batches}
    (sources : CallbackProjectionSource work queue before retained batches)
    (boundary : Boundary queue)
    : queue.runNormalized (projectHistoryAtEntry queue batches)
      = queue.runNormalized batches := by
  unfold ReferenceWorkQueue.State.runNormalized
  dsimp only
  rw [sources.runWithPublisher _ boundary]

/-- Actual interleaved callbacks preserve complete normalized queue and publisher replay. -/
theorem CallbackHistory.projectedAtEntry_runNormalized {work buffer}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) buffer)
    : let initial :=
        ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)
      initial.runNormalized (projectHistoryAtEntry initial buffer.rawBatches)
      = initial.runNormalized buffer.rawBatches :=
  (history.projectionSource generated).runNormalized
    (initialized_boundary generated nonempty)

/-- The unchanged interleaved history constructs every law of the original finite source. -/
theorem CallbackHistory.projectedAtEntry_source_valid {work buffer}
    (generated : ReferenceWorkQueue.ExecutedWork work) (nonempty : work.size ≠ 0)
    (history
      : CallbackHistory work
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work)) buffer)
    : (EventSource.ofList
        (projectHistoryAtEntry
          (ReferenceWorkQueue.State.initialize
            (ReferenceWorkQueue.Work.fromExecution work))
          buffer.rawBatches)).ValidFor
        work := by
  have sources := history.projectionSource generated
  apply source_valid_of_laws
  · simpa only [List.nil_append] using sources.work_valid
  · rw [inputsStarted_eq]
    exact sources.started (initialized_boundary generated nonempty)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.BufferedCallbacks
