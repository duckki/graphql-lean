import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceObservation

/-! Source observation for the current reference-backed queue. Normalized replay threads
the shared publisher; stopped readers absorb input without completing semantic work.
Initialization and admissible-prefix witnesses are transferred from the reference queue.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Initialization and absorbing reader states
-----------------------------------------------------------------------------------------

/-- An admitted empty source input gives the current factory its empty observation. -/
theorem createWorkQueueForSchedule_initialized (work : Work)
    (source : EventSource (List GraphEvent)) (empty : source.admissible [])
    : (createWorkQueueForSchedule work source).Initialized := by
  exact ⟨rfl, [], empty, rfl⟩

/-- Semantic termination suppresses all later accounting, publication, and host effects. -/
theorem State.handleGraphEvents_after_termination (state : State)
    (batch : List GraphEvent) (terminated : state.queue.terminated = true)
    : state.handleGraphEvents batch = { state } := by
  simp [State.handleGraphEvents, terminated]

/-- Abrupt cancellation suppresses later input without manufacturing termination. -/
theorem State.handleGraphEvents_after_stop (state : State)
    (batch : List GraphEvent) (stopped : state.stopped = true)
    : state.handleGraphEvents batch = { state } := by
  simp [State.handleGraphEvents, stopped]

-----------------------------------------------------------------------------------------
-- Normalized replay and terminal suffixes
-----------------------------------------------------------------------------------------

private abbrev NormalizedAcc :=
  State × ReferenceWorkQueue.IncrementalPublisher × List (List Execution.WorkQueueEvent)

private def normalizedStep (acc : NormalizedAcc) (batch : List GraphEvent)
    : NormalizedAcc :=
  let next := acc.1.handleGraphEvents batch
  if next.workQueueEvents.isEmpty then
    (next.state, acc.2.1, acc.2.2)
  else
    let mapped := acc.2.1.normalizeBatch next.workQueueEvents
    (next.state, mapped.1, acc.2.2 ++ [mapped.2])

private theorem foldl_fixed {σ α : Type} (step : σ → α → σ)
    (state : σ) (inputs : List α) (fixed : ∀ input, step state input = state)
    : inputs.foldl step state = state := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simpa [List.foldl_cons, fixed input] using ih

private theorem runNormalized_absorbs (state : State) (inputs : List (List GraphEvent))
    (closed : ∀ batch, state.handleGraphEvents batch = { state })
    : state.runNormalized inputs = (state, []) := by
  let start : NormalizedAcc :=
    (state, { active := state.queue.initialGroups ++ state.queue.initialStreams }, [])
  have fixed : ∀ batch, normalizedStep start batch = start := by
    intro batch
    simp [normalizedStep, start, closed batch]
  have folded := foldl_fixed normalizedStep start inputs fixed
  change ((inputs.foldl normalizedStep start).1, (inputs.foldl normalizedStep start).2.2)
    = (state, [])
  rw [folded]

/-- A terminated queue emits no later normalized work-event batch. -/
theorem State.runNormalized_after_termination (state : State)
    (inputs : List (List GraphEvent)) (terminated : state.queue.terminated = true)
    : state.runNormalized inputs = (state, []) :=
  runNormalized_absorbs state inputs
    (fun batch => state.handleGraphEvents_after_termination batch terminated)

/-- A cancelled queue emits no later batch, even when semantic work is incomplete. -/
theorem State.runNormalized_after_stop (state : State)
    (inputs : List (List GraphEvent)) (stopped : state.stopped = true)
    : state.runNormalized inputs = (state, []) :=
  runNormalized_absorbs state inputs
    (fun batch => state.handleGraphEvents_after_stop batch stopped)

/-- A terminal replay prefix fixes both its state and normalized output for every suffix. -/
theorem State.runNormalized_termination_stable (state : State)
    (before suffix : List (List GraphEvent))
    (terminated : (state.runNormalized before).1.queue.terminated = true)
    : state.runNormalized (before ++ suffix) = state.runNormalized before := by
  let start : NormalizedAcc :=
    (state, { active := state.queue.initialGroups ++ state.queue.initialStreams }, [])
  let after := before.foldl normalizedStep start
  have done : after.1.queue.terminated = true := terminated
  have fixed : ∀ batch, normalizedStep after batch = after := by
    intro batch
    simp [normalizedStep, after.1.handleGraphEvents_after_termination batch done]
  have folded := foldl_fixed normalizedStep after suffix fixed
  change (((before ++ suffix).foldl normalizedStep start).1,
    ((before ++ suffix).foldl normalizedStep start).2.2) = (after.1, after.2.2)
  rw [List.foldl_append, folded]

-----------------------------------------------------------------------------------------
-- Actual initialized output prefixes and the unchanged source contract
-----------------------------------------------------------------------------------------

/-- Every output prefix of actual initialized replay has an input-batch prefix witness.
Publisher normalization and terminal retirement preserve the reference output exactly.
-/
theorem State.runNormalized_initialize_prefix_reachable (work : Work)
    (inputs : List (List GraphEvent)) (target : List (List Execution.WorkQueueEvent))
    (earlierOutput : target.IsPrefix ((State.initialize work).runNormalized inputs).2)
    : ∃ before,
        before.IsPrefix inputs
        ∧ ((State.initialize work).runNormalized before).2 = target := by
  let queue := State.initialize work
  let publisher : ReferenceWorkQueue.IncrementalPublisher :=
    { active := queue.queue.initialGroups ++ queue.queue.initialStreams }
  let start : NormalizedAcc := (queue, publisher, [])
  have outputStep (acc : NormalizedAcc) (batch : List GraphEvent)
      : acc.2.2.IsPrefix (normalizedStep acc batch).2.2
        ∧ (normalizedStep acc batch).2.2.length ≤ acc.2.2.length + 1 := by
    obtain ⟨queue, publisher, outputs⟩ := acc
    simp only [normalizedStep]
    split <;> simp
  have final : target.IsPrefix (inputs.foldl normalizedStep start).2.2 := earlierOutput
  obtain ⟨before, earlier, same⟩ :=
    ReferenceWorkQueue.foldl_output_prefix_reachable normalizedStep (fun acc => acc.2.2)
      (fun state batch => (outputStep state batch).1)
      (fun state batch => (outputStep state batch).2)
      start inputs target List.nil_prefix final
  exact ⟨before, earlier, same⟩

/-- Source prefix closure transfers without an extra execution or cleanup premise. -/
theorem createWorkQueueForSchedule_prefixClosed (work : Work)
    (source : EventSource (List GraphEvent))
    (closed
      : ∀ before after,
          before.IsPrefix after → source.admissible after → source.admissible before)
    : (createWorkQueueForSchedule work source).PrefixClosed := by
  intro before after earlier admitted
  change ∃ inputs, source.admissible inputs
    ∧ ((State.initialize work).runNormalized inputs).2 = after at admitted
  obtain ⟨inputs, allowed, output⟩ := admitted
  have outputPrefix : before.IsPrefix ((State.initialize work).runNormalized inputs).2 := by
    rw [output]
    exact earlier
  obtain ⟨prior, earlierInputs, observed⟩ :=
    State.runNormalized_initialize_prefix_reachable work inputs before outputPrefix
  exact ⟨prior, closed prior inputs earlierInputs allowed, observed⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
