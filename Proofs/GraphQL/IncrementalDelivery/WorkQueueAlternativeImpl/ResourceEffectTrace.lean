import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResponseResourceSafety

/-! Constructed adoption and cleanup observations are licensed by the same actual reader's
inline effects, through FIFO dispatch, terminal teardown and finished-reader guards.
Normal completion is licensed by input settlement instead; acquisitions, asynchronous
settlement and native callback correspondence remain independent observations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Inline adoption and cleanup labels cover the constructed observations
-----------------------------------------------------------------------------------------

/-- Only the two resource-action kinds backed by inline host labels. This makes no claim
about acquisition/completion sites, effect settlement or complete native inventories.
-/
def EffectObservationsCovered (actions : List ResourceAction) (effects : List HostEffect)
    : Prop :=
  (∀ producer inventory, .adopt producer inventory ∈ actions → .adopt producer ∈ effects)
  ∧ (∀ target,
      .requestCleanup target ∈ actions
      → target ∈ effects.filterMap HostEffect.cleanupStart?)

private theorem EffectObservationsCovered.empty (effects : List HostEffect)
    : EffectObservationsCovered [] effects := by
  constructor <;> simp

private theorem EffectObservationsCovered.mono {actions before after}
    (covered : EffectObservationsCovered actions before)
    (included : ∀ effect ∈ before, effect ∈ after)
    : EffectObservationsCovered actions after := by
  refine ⟨fun producer inventory adopted => included _ (covered.1 _ _ adopted), ?_⟩
  intro target requested
  obtain ⟨effect, emitted, same⟩ := List.mem_filterMap.mp (covered.2 _ requested)
  exact List.mem_filterMap.mpr ⟨effect, included _ emitted, same⟩

private theorem EffectObservationsCovered.append {first before last after}
    (earlier : EffectObservationsCovered first before)
    (later : EffectObservationsCovered last after)
    : EffectObservationsCovered (first ++ last) (before ++ after) := by
  constructor
  · intro producer inventory adopted
    rcases List.mem_append.mp adopted with first | last
    · exact List.mem_append_left _ (earlier.1 _ _ first)
    · exact List.mem_append_right _ (later.1 _ _ last)
  · intro target requested
    rw [List.filterMap_append]
    rcases List.mem_append.mp requested with first | last
    · exact List.mem_append_left _ (earlier.2 _ first)
    · exact List.mem_append_right _ (later.2 _ last)

/-- Cache-aware dispatch emits exactly the accepted producer handoffs. -/
theorem graphEffects_adoptedProducers_available (state : State) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat))
    : (graphEffects state.queue event).filterMap HostEffect.adoptedProducer?
      = (state.handleGraphEvent event available).2.2.1.filterMap
          HostEffect.adoptedProducer? := by
  have labels := graphEffects_eq_of_accepts state.queue (state.queue.cacheTaskFailures available)
    event (state.queue.cacheTaskFailures_acceptsGraphEvent available event).symm
  rw [labels]
  clear labels
  cases event with
  | taskSuccess occurrence result =>
      simp only [State.handleGraphEvent, State.taskSuccess_adoptedProducers, graphEffects]
      cases found : (state.queue.cacheTaskFailures available).taskNode? occurrence <;> rfl
  | streamItems stream items =>
      simp only [State.handleGraphEvent, State.streamItems_adoptedProducers, graphEffects]
      have mapped : (items.map (fun item => HostEffect.adopt item.occurrence)).filterMap
          HostEffect.adoptedProducer? = items.map (·.occurrence) := by
        induction items with
        | nil => rfl
        | cons item rest ih => simpa only [List.map_cons, List.filterMap_cons,
            HostEffect.adoptedProducer?] using congrArg (List.cons item.occurrence) ih
      cases active : (state.queue.cacheTaskFailures available).rootStreams.contains stream.ref <;>
        simp [mapped, HostEffect.adoptedProducer?, List.filterMap_append]
  | taskFailure occurrence errors =>
      simp only [State.handleGraphEvent, graphEffects, cleanupEffects_adoptedProducers,
        List.filterMap_nil]
  | groupFailure | streamSuccess => rfl
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, graphEffects]

/-- A dispatch observes no adoption or cleanup without its own actual inline label. -/
theorem ResourceState.observeDispatch_effectCoverage (resources : ResourceState)
    (inventories : ProducerInventories) (before : State) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : EffectObservationsCovered
        (resources.observeDispatch inventories before event available).2
        (({ state := before } : GraphBatchResult).handleGraphEvent event
          available).effects := by
  constructor
  · intro producer inventory adopted
    rcases resources.observeDispatch_actions_available inventories before event available _
      adopted with
      ⟨target, _, same⟩ | ⟨other, emitted, same⟩ | ⟨effect, _, target, _, same⟩
    · cases same
    · cases same
      simp only [GraphBatchResult.handleGraphEvent, List.nil_append]
      have listed : producer
          ∈ (graphEffects before.queue event).filterMap HostEffect.adoptedProducer? :=
        List.mem_filterMap.mpr ⟨.adopt producer, emitted, rfl⟩
      rw [graphEffects_adoptedProducers_available before event available] at listed
      obtain ⟨label, actual, selected⟩ := List.mem_filterMap.mp listed
      cases label <;> simp_all only [HostEffect.adoptedProducer?, Option.some.injEq, reduceCtorEq]
    · cases same
  · intro target requested
    rcases resources.observeDispatch_actions_available inventories before event available _
      requested with
      ⟨other, _, same⟩ | ⟨producer, _, same⟩ | ⟨effect, emitted, other, identifies, same⟩
    · cases same
    · cases same
    · cases same
      exact List.mem_filterMap.mpr ⟨effect, emitted, identifies⟩

private theorem GraphBatchResult.handleGraphEvent_effects_append
    (before : GraphBatchResult) (event : GraphEvent)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : (before.handleGraphEvent event available).effects
      = before.effects
        ++ (({ state := before.state } : GraphBatchResult).handleGraphEvent
              event available).effects := by
  simp only [GraphBatchResult.handleGraphEvent, List.nil_append]

/-- Coverage follows the same FIFO accumulator, including any earlier observed prefix. -/
theorem ResourceBatchObservation.fold_effectCoverage (before : ResourceBatchObservation)
    (inventories : ProducerInventories) (events : List GraphEvent)
    (covered : EffectObservationsCovered before.actions before.dispatch.effects)
    (available : List (WorkQueueSemantics.Occurrence × Nat) := [])
    : let after :=
        events.foldl (fun acc event => acc.handleGraphEvent inventories event available)
          before
      EffectObservationsCovered after.actions after.dispatch.effects := by
  induction events generalizing before with
  | nil => exact covered
  | cons event rest ih =>
      apply ih
      change EffectObservationsCovered
        (before.actions
          ++ (before.resources.observeDispatch inventories before.dispatch.state event available).2)
        (before.dispatch.handleGraphEvent event available).effects
      rw [GraphBatchResult.handleGraphEvent_effects_append before.dispatch event available]
      exact covered.append (before.resources.observeDispatch_effectCoverage _ _ _ available)

private theorem ResourceState.observeStop_effectCoverage (resources : ResourceState)
    (state : State)
    : EffectObservationsCovered (resources.observeStop state).2 state.cancel.2 := by
  constructor
  · intro producer inventory adopted
    obtain ⟨target, _, same⟩ := resources.requestQueueCleanup_actions _ _ adopted
    cases same
  · intro target requested
    obtain ⟨other, emitted, same⟩ := resources.requestQueueCleanup_actions _ _ requested
    cases same
    exact emitted

/-- Every constructed batch observation is covered by the actual dispatch effects,
including terminal cancellation before record clearing. No endpoint coverage is assumed.
-/
theorem State.observeResourceBatch_effectCoverage (state : State)
    (resources : ResourceState) (inventories : ProducerInventories)
    (batch : List GraphEvent)
    : let observed := State.observeResourceBatch state resources inventories batch
      EffectObservationsCovered observed.actions observed.dispatch.effects := by
  unfold State.observeResourceBatch
  split
  · exact EffectObservationsCovered.empty _
  · have covered := ResourceBatchObservation.fold_effectCoverage
      { dispatch := { state }, resources } inventories batch (EffectObservationsCovered.empty _)
        (ReferenceWorkQueue.GraphEvent.availableFailures batch)
    dsimp only at covered ⊢
    split
    · exact covered.append (ResourceState.observeStop_effectCoverage _ _)
    · exact covered

-----------------------------------------------------------------------------------------
-- The actual response mapper adds no adoption or cleanup operation
-----------------------------------------------------------------------------------------

/-- For a live reader, all dispatcher labels survive the mapper and optional finish hook. -/
theorem ResponseStreamCursor.handleBatch_effects_include (cursor : ResponseStreamCursor)
    (batch : List GraphEvent) (running : cursor.finished = false)
    : ∀ effect ∈ (cursor.queue.handleGraphEvents batch).effects,
        effect ∈ (cursor.handleBatch batch).2.2 := by
  unfold ResponseStreamCursor.handleBatch
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split
  · exact fun _ member => member
  · split
    · exact fun _ member => member
    · exact fun _ member => List.mem_append_left _ member

/-- Observe the actual reader guard, not an unguarded synthetic graph dispatch. -/
def ResourceState.observeReaderBatch (resources : ResourceState)
    (cursor : ResponseStreamCursor) (inventories : ProducerInventories)
    (batch : List GraphEvent)
    : ResourceState × List ResourceAction :=
  if cursor.finished then
    (resources, [])
  else
    let observed := State.observeResourceBatch cursor.queue resources inventories batch
    (observed.resources, observed.actions)

/-- Both reader branches construct one compatible legal ownership history. -/
theorem ResourceState.observeReaderBatch_replay (resources : ResourceState)
    (cursor : ResponseStreamCursor) (inventories : ProducerInventories)
    (batch : List GraphEvent)
    : ResourceReplay resources (resources.observeReaderBatch cursor inventories batch).2
        (resources.observeReaderBatch cursor inventories batch).1 := by
  unfold ResourceState.observeReaderBatch
  split
  · exact .nil _
  · exact State.observeResourceBatch_replay _ _ _ _

/-- Adoption/cleanup observations come from this same actual mapper call's effects. -/
theorem ResourceState.observeReaderBatch_effectCoverage (resources : ResourceState)
    (cursor : ResponseStreamCursor) (inventories : ProducerInventories)
    (batch : List GraphEvent)
    : EffectObservationsCovered (resources.observeReaderBatch cursor inventories batch).2
        (cursor.handleBatch batch).2.2 := by
  unfold ResourceState.observeReaderBatch
  split
  · exact EffectObservationsCovered.empty _
  · rename_i live
    have running : cursor.finished = false := Bool.eq_false_iff.mpr live
    have covered := State.observeResourceBatch_effectCoverage cursor.queue resources inventories
      batch
    dsimp only at covered ⊢
    rw [State.observeResourceBatch_dispatch] at covered
    exact covered.mono (ResponseStreamCursor.handleBatch_effects_include cursor batch running)

-----------------------------------------------------------------------------------------
-- Replay carries one actual reader and its effects alongside the resource history
-----------------------------------------------------------------------------------------

/-- Proof-only coupled observation; not a new publisher or native resource ledger. -/
structure ResourceReaderObservation where
  cursor : ResponseStreamCursor
  resources : ResourceState
  actions : List ResourceAction := []
  effects : List HostEffect := []

/-- Advance the actual reader once and observe only the work it really accepts. -/
def ResourceReaderObservation.handleBatch (before : ResourceReaderObservation)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : ResourceReaderObservation :=
  let observed := before.resources.observeReaderBatch before.cursor inventories batch
  let next := before.cursor.handleBatch batch
  {
    cursor := next.2.1
    resources := observed.1
    actions := before.actions ++ observed.2
    effects := before.effects ++ next.2.2
  }

/-- Finite supplied batches only; native acquisitions/settlements are not synthesized. -/
def ResponseStreamCursor.observeResourceRun (cursor : ResponseStreamCursor)
    (resources : ResourceState) (inventories : ProducerInventories)
    (inputs : List (List GraphEvent))
    : ResourceReaderObservation :=
  inputs.foldl (fun acc batch => acc.handleBatch inventories batch) { cursor, resources }

/-- The observer uses the exact same actual reader and ordered inline effects as run. -/
theorem ResponseStreamCursor.observeResourceRun_projection (cursor : ResponseStreamCursor)
    (resources : ResourceState) (inventories : ProducerInventories)
    (inputs : List (List GraphEvent))
    : let observed :=
        ResponseStreamCursor.observeResourceRun cursor resources inventories inputs
      observed.cursor = (cursor.run inputs).2.1
      ∧ observed.effects = (cursor.run inputs).2.2 := by
  let step := fun (acc : ResponseStreamCursor × List HostEffect) batch =>
    let next := acc.1.handleBatch batch
    (next.2.1, acc.2 ++ next.2.2)
  have observer := List.foldl_hom
    (fun acc : ResourceReaderObservation => (acc.cursor, acc.effects))
    (g₁ := fun acc batch => acc.handleBatch inventories batch) (g₂ := step)
    (l := inputs) (init := { cursor, resources }) (by intro acc batch; rfl)
  have reader := List.foldl_hom
    (fun acc
      : List Execution.IncrementalStreamUpdateResult × ResponseStreamCursor × List HostEffect =>
      acc.2)
    (g₁ := fun acc batch =>
      let next := acc.2.1.handleBatch batch
      (acc.1 ++ next.1.toList, next.2.1, acc.2.2 ++ next.2.2))
    (g₂ := step) (l := inputs) (init := ([], cursor, [])) (by intro acc batch; rfl)
  have same := reader.symm.trans observer
  exact ⟨congrArg Prod.fst same.symm, congrArg Prod.snd same.symm⟩

/-- The same replay constructs a legal resource history whose adoption and request actions
are licensed by actual reader effects. This asserts neither native callback completeness
nor successful asynchronous cleanup.
-/
theorem ResponseStreamCursor.observeResourceRun_safety (cursor : ResponseStreamCursor)
    (resources : ResourceState) (inventories : ProducerInventories)
    (inputs : List (List GraphEvent))
    : let observed :=
        ResponseStreamCursor.observeResourceRun cursor resources inventories inputs
      ResourceReplay resources observed.actions observed.resources
      ∧ EffectObservationsCovered observed.actions (cursor.run inputs).2.2 := by
  have invariant : ∀ (before : ResourceReaderObservation),
      ResourceReplay resources before.actions before.resources
      → EffectObservationsCovered before.actions before.effects
      → let after := inputs.foldl (fun acc batch => acc.handleBatch inventories batch) before
        ResourceReplay resources after.actions after.resources
          ∧ EffectObservationsCovered after.actions after.effects := by
    intro before earlier covered
    induction inputs generalizing before with
    | nil => exact ⟨earlier, covered⟩
    | cons batch rest ih =>
        apply ih
        · exact earlier.append (before.resources.observeReaderBatch_replay _ _ _)
        · exact covered.append (before.resources.observeReaderBatch_effectCoverage _ _ _)
  obtain ⟨legal, covered⟩ := invariant { cursor, resources } (.nil _)
    (EffectObservationsCovered.empty _)
  change EffectObservationsCovered
    (ResponseStreamCursor.observeResourceRun cursor resources inventories inputs).actions
    (ResponseStreamCursor.observeResourceRun cursor resources inventories inputs).effects at covered
  rw [(ResponseStreamCursor.observeResourceRun_projection cursor resources inventories inputs).2]
    at covered
  exact ⟨legal, covered⟩

-----------------------------------------------------------------------------------------
-- Close extends the same trace; it cannot invent cleanup behind a finished guard
-----------------------------------------------------------------------------------------

private theorem ResourceState.observeReaderClose_effectCoverage
    (resources : ResourceState) (cursor : ResponseStreamCursor)
    : EffectObservationsCovered (resources.observeReaderClose cursor).2
        cursor.close.2 := by
  unfold ResourceState.observeReaderClose
  split
  · exact EffectObservationsCovered.empty _
  · rename_i live
    have running : cursor.finished = false := Bool.eq_false_iff.mpr live
    rw [ResponseStreamCursor.close_effects _ running]
    exact (resources.observeStop_effectCoverage cursor.queue).mono
      (fun _ member => List.mem_append_left _ member)

/-- The actual replay and its abrupt close construct one legal ownership history and one
compatible effect trace. No request is justified by a different close or a cleared record.
This root does not assert coverage of unobserved native acquisitions or producer suffixes.
-/
theorem ResponseStreamCursor.observeResourceRun_close_safety
    (cursor : ResponseStreamCursor) (resources : ResourceState)
    (inventories : ProducerInventories) (inputs : List (List GraphEvent))
    : let observed :=
        ResponseStreamCursor.observeResourceRun cursor resources inventories inputs
      let closed := observed.resources.observeReaderClose observed.cursor
      ResourceReplay resources (observed.actions ++ closed.2) closed.1
      ∧ EffectObservationsCovered (observed.actions ++ closed.2)
          ((cursor.run inputs).2.2 ++ (cursor.run inputs).2.1.close.2) := by
  obtain ⟨legal, covered⟩ :=
    ResponseStreamCursor.observeResourceRun_safety cursor resources inventories
    inputs
  let observed := ResponseStreamCursor.observeResourceRun cursor resources inventories inputs
  change ResourceReplay resources
      (observed.actions ++ (observed.resources.observeReaderClose observed.cursor).2)
      (observed.resources.observeReaderClose observed.cursor).1
    ∧ EffectObservationsCovered
      (observed.actions ++ (observed.resources.observeReaderClose observed.cursor).2)
      ((cursor.run inputs).2.2 ++ (cursor.run inputs).2.1.close.2)
  refine ⟨legal.append (observed.resources.observeReaderClose_replay observed.cursor), ?_⟩
  have closeCovered := observed.resources.observeReaderClose_effectCoverage observed.cursor
  have same : observed.cursor = (cursor.run inputs).2.1 :=
    (ResponseStreamCursor.observeResourceRun_projection cursor resources inventories inputs).1
  exact covered.append
    (closeCovered.mono (by intro effect member; simpa only [same] using member))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
