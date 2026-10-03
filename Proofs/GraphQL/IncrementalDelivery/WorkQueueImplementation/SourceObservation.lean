import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublisherRegistry

/-! Initialization, termination absorption, and output-prefix observation. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The source adapter starts with a real empty observation
-----------------------------------------------------------------------------------------

/-- A source admitting its empty input gives the adapter an admitted empty output.
Witness: replay no graph-event batches from the single initialized queue.
-/
theorem createWorkQueueForSchedule_initialized (work : Execution.Work)
    (source : EventSource (List GraphEvent))
    (empty : source.admissible [])
    : (createWorkQueueForSchedule work source).Initialized := by
  constructor
  · rfl
  · exact ⟨[], empty, rfl⟩

-----------------------------------------------------------------------------------------
-- Observable output prefixes come from input prefixes
-----------------------------------------------------------------------------------------

abbrev NormalizedAcc :=
  State × IncrementalPublisher × List (List Execution.WorkQueueEvent)

def normalizedStep (acc : NormalizedAcc) (batch : List GraphEvent) : NormalizedAcc :=
  let (queue, publisher, outputs) := acc
  let (nextQueue, raw) := queue.handleGraphEvents batch
  if raw.isEmpty then
    (nextQueue, publisher, outputs)
  else
    let (nextPublisher, mapped) := publisher.normalizeBatch raw
    (nextQueue, nextPublisher, outputs ++ [mapped])

/-- Every finite replay retains duplicate-free group task memberships. This
holds for arbitrary input batches, independent of source admissibility.
-/
theorem State.runNormalized_taskMembershipsUnique (queue : State)
    (batches : List (List GraphEvent)) (unique : queue.TaskMembershipsUnique)
    : (queue.runNormalized batches).1.TaskMembershipsUnique := by
  have stepUnique (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentUnique : acc.1.TaskMembershipsUnique)
      : (normalizedStep acc batch).1.TaskMembershipsUnique := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextUnique : next.TaskMembershipsUnique := by
          have handled := currentUnique.handleGraphEvents batch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextUnique
  have foldUnique (more : List (List GraphEvent)) :
      ∀ acc : NormalizedAcc, acc.1.TaskMembershipsUnique
        → (more.foldl normalizedStep acc).1.TaskMembershipsUnique := by
    induction more with
    | nil => intro acc currentUnique; exact currentUnique
    | cons batch rest ih =>
        intro acc currentUnique
        exact ih (normalizedStep acc batch) (stepUnique acc batch currentUnique)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep (queue, publisher, [])).1.TaskMembershipsUnique
  exact foldUnique batches (queue, publisher, []) unique

/-- Queue creation and every finite host replay preserve unique live task
memberships, the static prerequisite for exactly-once group accounting.
-/
theorem createWorkQueue_runNormalized_taskMembershipsUnique
    (work : Work) (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.TaskMembershipsUnique :=
  State.runNormalized_taskMembershipsUnique (State.initialize work) batches
    (createWorkQueue_taskMembershipsUnique work)

/-- Every finite replay retains a unique live node for each group ref, for
arbitrary host batches and without appealing to source admissibility.
-/
theorem State.runNormalized_groupRefsUnique (queue : State)
    (batches : List (List GraphEvent)) (unique : queue.GroupRefsUnique)
    : (queue.runNormalized batches).1.GroupRefsUnique := by
  have stepUnique (acc : NormalizedAcc) (batch : List GraphEvent)
      (currentUnique : acc.1.GroupRefsUnique)
      : (normalizedStep acc batch).1.GroupRefsUnique := by
    obtain ⟨current, publisher, outputs⟩ := acc
    unfold normalizedStep
    cases outcome : current.handleGraphEvents batch with
    | mk next raw =>
        have nextUnique : next.GroupRefsUnique := by
          have handled := currentUnique.handleGraphEvents batch
          rw [outcome] at handled
          exact handled
        dsimp only
        simp only [outcome]
        split <;> exact nextUnique
  have foldUnique (more : List (List GraphEvent)) :
      ∀ acc : NormalizedAcc, acc.1.GroupRefsUnique →
        (more.foldl normalizedStep acc).1.GroupRefsUnique := by
    induction more with
    | nil => intro acc currentUnique; exact currentUnique
    | cons batch rest ih =>
        intro acc currentUnique
        exact ih (normalizedStep acc batch) (stepUnique acc batch currentUnique)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  change (batches.foldl normalizedStep (queue, publisher, [])).1.GroupRefsUnique
  exact foldUnique batches (queue, publisher, []) unique

/-- Initialized queues keep unique group refs through every finite replay. -/
theorem createWorkQueue_runNormalized_groupRefsUnique
    (work : Work) (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.GroupRefsUnique :=
  State.runNormalized_groupRefsUnique (State.initialize work) batches
    (createWorkQueue_groupRefsUnique work)

/-- Once terminated, the queue ignores every subsequent host event batch. -/
theorem State.handleGraphEvents_after_termination (queue : State)
    (batch : List GraphEvent) (terminated : queue.terminated = true)
    : queue.handleGraphEvents batch = (queue, []) := by
  simp [State.handleGraphEvents, terminated]

private theorem foldl_fixed {σ α : Type} (step : σ → α → σ)
    (state : σ) (inputs : List α) (fixed : ∀ input, step state input = state)
    : inputs.foldl step state = state := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simpa [List.foldl_cons, fixed input] using ih

/-- A terminated queue emits no later normalized batch. Witness: termination is an
absorbing state for the graph-event handler and therefore for the replay fold.
-/
theorem State.runNormalized_after_termination (queue : State)
    (inputs : List (List GraphEvent)) (terminated : queue.terminated = true)
    : queue.runNormalized inputs = (queue, []) := by
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let start : NormalizedAcc := (queue, publisher, [])
  have fixed : ∀ input, normalizedStep start input = start := by
    intro input
    simp [normalizedStep, start, queue.handleGraphEvents_after_termination input terminated]
  have folded := foldl_fixed normalizedStep start inputs fixed
  change ((inputs.foldl normalizedStep start).1, (inputs.foldl normalizedStep start).2.2)
    = (queue, [])
  rw [folded]

private theorem normalizedStep_after_termination (acc : NormalizedAcc)
    (batch : List GraphEvent) (terminated : acc.1.terminated = true)
    : normalizedStep acc batch = acc := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  simp [normalizedStep, queue.handleGraphEvents_after_termination batch terminated]

/-- Once a replay has terminated, later host batches leave both the final queue state
and every previously emitted work-event batch unchanged. Witness: fold absorption.
-/
theorem State.runNormalized_termination_stable (queue : State)
    (before suffix : List (List GraphEvent))
    (terminated : (queue.runNormalized before).1.terminated = true)
    : queue.runNormalized (before ++ suffix) = queue.runNormalized before := by
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let start : NormalizedAcc := (queue, publisher, [])
  let after := before.foldl normalizedStep start
  have done : after.1.terminated = true := by
    change (before.foldl normalizedStep start).1.terminated = true at terminated
    exact terminated
  have fixed : ∀ input, normalizedStep after input = after := by
    intro input
    exact normalizedStep_after_termination after input done
  have folded := foldl_fixed normalizedStep after suffix fixed
  change (((before ++ suffix).foldl normalizedStep start).1,
    ((before ++ suffix).foldl normalizedStep start).2.2) =
    ((before.foldl normalizedStep start).1, (before.foldl normalizedStep start).2.2)
  rw [List.foldl_append, folded]

/-- A graph-event batch emits zero or one normalized work-event batch. -/
private theorem normalizedStep_output (acc : NormalizedAcc) (batch : List GraphEvent)
    : acc.2.2.IsPrefix (normalizedStep acc batch).2.2
      ∧ (normalizedStep acc batch).2.2.length ≤ acc.2.2.length + 1 := by
  obtain ⟨queue, publisher, outputs⟩ := acc
  simp only [normalizedStep]
  split <;> simp

/-- Each fold step preserves the previous output as an exact prefix. -/
private theorem foldl_output_prefix {σ α β : Type}
    (step : σ → α → σ) (output : σ → List β)
    (monotone : ∀ state input, (output state).IsPrefix (output (step state input)))
    (state : σ) (inputs : List α)
    : (output state).IsPrefix (output (inputs.foldl step state)) := by
  induction inputs generalizing state with
  | nil => exact List.prefix_refl _
  | cons input rest ih => exact (monotone state input).trans (ih (step state input))

/-- For a one-output-at-a-time fold, every observable prefix occurs at an input
boundary. The witness is the shortest consumed input prefix of that output length.
-/
private theorem foldl_output_prefix_reachable {σ α β : Type}
    (step : σ → α → σ) (output : σ → List β)
    (monotone : ∀ state input, (output state).IsPrefix (output (step state input)))
    (unit : ∀ state input, (output (step state input)).length ≤ (output state).length + 1)
    (state : σ) (inputs : List α) (target : List β)
    (start : (output state).IsPrefix target)
    (final : target.IsPrefix (output (inputs.foldl step state)))
    : ∃ (before : List α),
        before.IsPrefix inputs ∧ output (before.foldl step state) = target := by
  induction inputs generalizing state with
  | nil =>
      have equal : target = output state :=
        final.eq_of_length_le start.length_le
      exact ⟨[], List.nil_prefix, equal.symm⟩
  | cons input rest ih =>
      by_cases reached : output state = target
      · exact ⟨[], List.nil_prefix, reached⟩
      · let next := step state input
        have nextFinal : (output next).IsPrefix
            (output (rest.foldl step next)) :=
          foldl_output_prefix step output monotone next rest
        have shorter : (output state).length < target.length := by
          have le := start.length_le
          have different : (output state).length ≠ target.length := by
            intro same
            exact reached (start.eq_of_length same)
          omega
        have bound : (output next).length ≤ target.length := by
          have stepBound : (output next).length ≤ (output state).length + 1 :=
            unit state input
          omega
        have nextTarget : (output next).IsPrefix target :=
          List.prefix_of_prefix_length_le nextFinal final bound
        obtain ⟨before, earlier, equal⟩ := ih next nextTarget final
        exact ⟨input :: before, by simpa using earlier, by simpa [next] using equal⟩

/-- Every prefix of a normalized output run comes from some input-batch prefix.
Witness: the generic one-output-at-a-time fold lemma.
-/
theorem State.runNormalized_prefix_reachable (queue : State)
    (inputs : List (List GraphEvent)) (target : List (List Execution.WorkQueueEvent))
    (hprefix : target.IsPrefix (queue.runNormalized inputs).2)
    : ∃ before, before.IsPrefix inputs ∧ (queue.runNormalized before).2 = target := by
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let start : NormalizedAcc := (queue, publisher, [])
  have h : target.IsPrefix ((inputs.foldl normalizedStep start).2.2) := by
    change target.IsPrefix ((inputs.foldl normalizedStep start).2.2) at hprefix
    exact hprefix
  obtain ⟨before, earlier, equal⟩ :=
    foldl_output_prefix_reachable normalizedStep (fun acc => acc.2.2)
      (fun state input => (normalizedStep_output state input).1)
      (fun state input => (normalizedStep_output state input).2)
      start inputs target List.nil_prefix h
  refine ⟨before, earlier, ?_⟩
  change (before.foldl normalizedStep start).2.2 = target
  exact equal

/-- Prefix closure of admitted graph-event batches transfers to the queue adapter.
Witness: each output prefix has an input-prefix realization.
-/
theorem createWorkQueueForSchedule_prefixClosed (work : Execution.Work)
    (source : EventSource (List GraphEvent))
    (closed
      : ∀ before after,
          before.IsPrefix after → source.admissible after → source.admissible before)
    : (createWorkQueueForSchedule work source).PrefixClosed := by
  let queue := State.initialize (Work.fromExecution work)
  intro before after earlier admitted
  change ∃ inputs, source.admissible inputs
    ∧ (queue.runNormalized inputs).2 = after at admitted
  obtain ⟨inputs, inputAllowed, output⟩ := admitted
  have outputPrefix : before.IsPrefix (queue.runNormalized inputs).2 := by
    rw [output]
    exact earlier
  obtain ⟨prior, earlierInputs, observed⟩ :=
    queue.runNormalized_prefix_reachable inputs before outputPrefix
  change ∃ inputs, source.admissible inputs
    ∧ (queue.runNormalized inputs).2 = before
  exact ⟨prior, closed prior inputs earlierInputs inputAllowed, observed⟩

-----------------------------------------------------------------------------------------
-- Queue-state facts and the initial abstract observation
-----------------------------------------------------------------------------------------

/-- The spec-facing history produced by one finite graph-event input prefix. -/
def State.normalizedHistory (queue : State) (inputs : List (List GraphEvent)) : History :=
  {
    initialGroups := queue.initialGroups
    initialStreams := queue.initialStreams
    batches := (queue.runNormalized inputs).2
  }

/-- The initial queue observation is a legal abstract prefix. Witness: no
publication or failure has yet occurred, so the initialization premise suffices.
-/
theorem initialQueue_admissiblePrefix (work : Execution.Work)
    (initialized
      : Initializes work
          (State.initialize (Work.fromExecution work)).initialGroups
          (State.initialize (Work.fromExecution work)).initialStreams)
    : AdmissiblePrefix work
        ((State.initialize (Work.fromExecution work)).normalizedHistory []) := by
  refine ⟨[], fun _ => .executionGroup [], [], ⟨initialized, ?_, ?_⟩,
    WorkBatching.nil⟩
  · intro before cut occurrence after impossible
    cases before <;> cases impossible
  · intro index event impossible
    cases impossible

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
