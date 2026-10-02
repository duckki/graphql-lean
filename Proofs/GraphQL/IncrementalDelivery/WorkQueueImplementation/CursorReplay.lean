import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObservation

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

-----------------------------------------------------------------------------------------
-- Owner selection is independent of wire identity
-----------------------------------------------------------------------------------------

/-- Replacing wire IDs commutes with raw-event normalization. Witness: each handler
inspects only the active owner registry and leaves wire identity untouched.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_with_ids
    (publisher : IncrementalPublisher) (ids : Execution.IDState) (event : WorkQueueEvent)
    : ({ publisher with ids }).handleWorkQueueEvent event
      = let (next, events) := publisher.handleWorkQueueEvent event
        ({ next with ids }, events) := by
  cases event <;> rfl

/-- A whole normalized batch is independent of wire IDs. Witness: the event-wise
identity replacement commutes with the publisher fold.
-/
theorem IncrementalPublisher.normalizeBatch_with_ids
    (publisher : IncrementalPublisher) (ids : Execution.IDState)
    (events : List WorkQueueEvent)
    : ({ publisher with ids }).normalizeBatch events
      = (
        { (publisher.normalizeBatch events).1 with ids },
        (publisher.normalizeBatch events).2
      ) := by
  unfold IncrementalPublisher.normalizeBatch
  apply List.foldl_hom
    (fun (acc : IncrementalPublisher × List Execution.WorkQueueEvent) =>
      (({ acc.1 with ids } : IncrementalPublisher), acc.2)) (init := (publisher, []))
  intro acc event
  rcases acc with ⟨publisher, outputs⟩
  simp only [handleWorkQueueEvent_with_ids]

/-- Shared queue replay is independent of wire IDs. Witness: lift publisher identity
replacement through both silent and productive host batches.
-/
theorem State.runWithPublisher_with_ids (queue : State) (publisher : IncrementalPublisher)
    (ids : Execution.IDState) (inputs : List (List GraphEvent))
    : queue.runWithPublisher { publisher with ids } inputs
      = (
        (queue.runWithPublisher publisher inputs).1,
        { (queue.runWithPublisher publisher inputs).2.1 with ids },
        (queue.runWithPublisher publisher inputs).2.2
      ) := by
  unfold State.runWithPublisher
  apply List.foldl_hom
    (fun (acc : State × IncrementalPublisher × List (List Execution.WorkQueueEvent)) =>
      (acc.1, ({ acc.2.1 with ids } : IncrementalPublisher), acc.2.2))
    (init := (queue, publisher, []))
  intro acc batch
  rcases acc with ⟨queue, publisher, outputs⟩
  cases outcome : queue.handleGraphEvents batch with
  | mk next raw =>
      simp only [outcome]
      split <;> simp only [IncrementalPublisher.normalizeBatch_with_ids]

-----------------------------------------------------------------------------------------
-- Direct cursor output is the canonical response mapping
-----------------------------------------------------------------------------------------

/-- Shared replay preserves prior output when resumed. Witness: appending a fixed
prefix to the output accumulator commutes with every normalized transition.
-/
private theorem normalizedFold_prefix (inputs : List (List GraphEvent))
    (queue : State) (publisher : IncrementalPublisher)
    (prior : List (List Execution.WorkQueueEvent))
    : inputs.foldl normalizedStep (queue, publisher, prior)
      = let next := inputs.foldl normalizedStep (queue, publisher, [])
        (next.1, next.2.1, prior ++ next.2.2) := by
  have h := List.foldl_hom
    (fun (acc : NormalizedAcc) => (acc.1, acc.2.1, prior ++ acc.2.2))
    (g₁ := normalizedStep) (g₂ := normalizedStep) (l := inputs)
    (init := (queue, publisher, [])) ?_
  · simpa only [List.append_nil] using h
  · rintro ⟨queue, publisher, outputs⟩ batch
    unfold normalizedStep
    cases outcome : queue.handleGraphEvents batch with
    | mk next raw =>
        dsimp only
        split
        · rfl
        · cases publisher.normalizeBatch raw
          simp only [List.append_assoc]

/-- Replaying two host prefixes is the same as resuming the shared machine.
Witness: fold concatenation and preservation of the earlier output accumulator.
-/
theorem State.runWithPublisher_append (queue : State) (publisher : IncrementalPublisher)
    (left right : List (List GraphEvent))
    : queue.runWithPublisher publisher (left ++ right)
      = let first := queue.runWithPublisher publisher left
        let last := first.1.runWithPublisher first.2.1 right
        (last.1, last.2.1, first.2.2 ++ last.2.2) := by
  change (left ++ right).foldl normalizedStep (queue, publisher, []) = _
  rw [List.foldl_append]
  exact normalizedFold_prefix right _ _ _

/-- Finite cursor replay composes without changing updates or residual state.
Witness: shared replay composition, identity-independent normalization, and mapM append.
-/
theorem ResponseStreamCursor.run_append (cursor : ResponseStreamCursor)
    (left right : List (List GraphEvent))
    : cursor.run (left ++ right)
      = let first := cursor.run left
        let last := first.2.run right
        (first.1 ++ last.1, last.2) := by
  simp only [run, State.run, State.runWithPublisher_append]
  cases first : cursor.queue.runWithPublisher cursor.publisher left with
  | mk queue rest =>
      rcases rest with ⟨publisher, outputs⟩
      dsimp only
      cases mapped
            : (outputs.mapM Execution.mapWorkEventBatch).run cursor.publisher.ids with
      | mk updates ids =>
          dsimp only
          simp only [State.runWithPublisher_with_ids, List.mapM_append, StateT.run_bind, mapped]
          cases second : ((queue.runWithPublisher publisher right).2.2.mapM
            Execution.mapWorkEventBatch).run ids
          simp [second]
          exact ⟨rfl, rfl, rfl⟩

/-- A single host batch produces exactly the previous online handler's optional update.
Witness: the common replay has either no output or one normalized batch.
-/
theorem ResponseStreamCursor.step_eq (cursor : ResponseStreamCursor)
    (batch : List GraphEvent)
    : cursor.step batch
      = let (queue, events) := cursor.queue.handleGraphEvents batch
        if events.isEmpty then
          (none, { cursor with queue })
        else
          let (update, publisher) := cursor.publisher.handleBatch events
          (some update, ⟨queue, publisher⟩) := by
  unfold step run State.run State.runWithPublisher
  cases outcome : cursor.queue.handleGraphEvents batch with
  | mk queue events =>
      simp only [List.foldl_cons, List.foldl_nil, outcome]
      by_cases empty : events.isEmpty = true
      · simp only [empty, ↓reduceIte]
        rfl
      · cases mapped : (Execution.mapWorkEventBatch (cursor.publisher.normalizeBatch events).2).run
          cursor.publisher.ids
        simp [empty, IncrementalPublisher.handleBatch, mapped]

/-- Empty replay preserves the complete cursor. Witness: both replay folds are empty. -/
@[simp]
theorem ResponseStreamCursor.run_nil (cursor : ResponseStreamCursor)
    : cursor.run [] = ([], cursor) := by
  rfl

/-- The online step retains every output of a singleton replay. Witness: the common
transition emits either no batch or one batch, so head? never discards a second update.
-/
theorem ResponseStreamCursor.run_singleton (cursor : ResponseStreamCursor)
    (batch : List GraphEvent)
    : cursor.run [batch] = ((cursor.step batch).1.toList, (cursor.step batch).2) := by
  rw [step_eq]
  unfold run State.run State.runWithPublisher
  cases outcome : cursor.queue.handleGraphEvents batch with
  | mk queue events =>
      simp only [List.foldl_cons, List.foldl_nil, outcome]
      by_cases empty : events.isEmpty = true
      · simp only [empty, ↓reduceIte]
        rfl
      · cases mapped : (Execution.mapWorkEventBatch (cursor.publisher.normalizeBatch events).2).run
          cursor.publisher.ids
        simp [empty, IncrementalPublisher.handleBatch, mapped]

/-- Finite replay agrees with online step followed by resumed replay. Witness: append
composition and the singleton no-loss result, including silent host batches.
-/
theorem ResponseStreamCursor.run_cons (cursor : ResponseStreamCursor)
    (batch : List GraphEvent) (rest : List (List GraphEvent))
    : cursor.run (batch :: rest)
      = let next := cursor.step batch
        let last := next.2.run rest
        (next.1.toList ++ last.1, last.2) := by
  rw [show batch :: rest = [batch] ++ rest from rfl, run_append, run_singleton]

/-- Starting the executable cursor allocates exactly the spec's initial notices.
Witness: definitional equality through the shared Execution initializer, which uses
getPendingEntry with an empty ID supply.
-/
theorem ResponseStreamCursor.initialize_eq (response : Execution.Response)
    (work : Execution.Work)
    : ResponseStreamCursor.initialize response work
      = let queue := State.initialize (Work.fromExecution work)
        let (pending, ids) :=
          (Execution.getPendingEntry (m := StateM Execution.IDState)
            queue.initialGroups queue.initialStreams Execution.ensureID).run
            {}
        (
          { toResponse := response, pending, hasNext := true },
          ⟨queue, { ids, active := queue.initialGroups ++ queue.initialStreams }⟩
        ) := by
  rfl

/-- Direct finite cursor execution maps exactly the adapter's normalized batches.
Witness: initial notice agreement and identity-independent shared replay. This equality
also identifies the final concrete queue, not merely the emitted wire values.
-/
theorem ResponseStreamCursor.run_initialize (response : Execution.Response)
    (work : Execution.Work) (inputs : List (List GraphEvent))
    : let queue := State.initialize (Work.fromExecution work)
      let (_, ids) :=
        (Execution.getPendingEntry (m := StateM Execution.IDState)
          queue.initialGroups queue.initialStreams Execution.ensureID).run
          {}
      let cursor := (ResponseStreamCursor.initialize response work).2
      (cursor.run inputs).1
        = (((queue.runNormalized inputs).2.mapM Execution.mapWorkEventBatch).run ids).1
      ∧ (cursor.run inputs).2.queue = (queue.runNormalized inputs).1 := by
  rw [initialize_eq]
  dsimp only
  cases allocation
        : (Execution.getPendingEntry (m := StateM Execution.IDState)
            (State.initialize (Work.fromExecution work)).initialGroups
            (State.initialize (Work.fromExecution work)).initialStreams
            Execution.ensureID).run
            {} with
  | mk pending ids =>
      dsimp only
      have independent := (State.initialize (Work.fromExecution work)).runWithPublisher_with_ids
        { active := (State.initialize (Work.fromExecution work)).initialGroups ++
            (State.initialize (Work.fromExecution work)).initialStreams } ids inputs
      simp only [run, State.run, independent, State.runNormalized]
      exact ⟨rfl, rfl⟩

/-- The finite response runner and initialized cursor return identical observations and
termination. Witness: both compose the same initialization and state-retaining response
replay; the equality is definitional for arbitrary supplied inputs.
-/
theorem replayIncrementalResponse_eq_cursor
    (completed : Execution.Completion (List (Name × Execution.ResponseValue)))
    (inputs : List (List GraphEvent))
    : replayIncrementalResponse completed inputs
      = let response := Execution.selectionSetResultToResponse completed.result
        let (initial, cursor) := ResponseStreamCursor.initialize response completed.work
        let (updates, finalCursor) := cursor.run inputs
        (initial, updates, finalCursor.queue.terminated) := by
  rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
