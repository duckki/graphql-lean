import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceHandoff

/-! One compatible ownership observation follows the actual FIFO batch dispatcher, including
terminal record clearing and stopped-reader guards. Native acquisitions remain independent.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- The resource observer follows actual intermediate dispatch states
-----------------------------------------------------------------------------------------

/-- Proof-only coupling, not another runtime buffer or resource ledger. -/
structure ResourceBatchObservation where
  dispatch : GraphBatchResult
  resources : ResourceState
  actions : List ResourceAction := []

/-- Observe the same input against the same accepting pre-state, before advancing both
projections. The dispatcher alone determines queue state, wire events and host effects.
-/
def ResourceBatchObservation.handleGraphEvent (before : ResourceBatchObservation)
    (inventories : ProducerInventories) (event : GraphEvent)
    : ResourceBatchObservation :=
  let observed := before.resources.observeDispatch inventories before.dispatch.state event
  {
    dispatch := before.dispatch.handleGraphEvent event
    resources := observed.1
    actions := before.actions ++ observed.2
  }

/-- The FIFO fold projects to the real dispatcher, not a separately chosen graph history. -/
theorem ResourceBatchObservation.fold_dispatch (before : ResourceBatchObservation)
    (inventories : ProducerInventories) (events : List GraphEvent)
    : (events.foldl (fun acc event => acc.handleGraphEvent inventories event)
        before).dispatch
      = events.foldl GraphBatchResult.handleGraphEvent before.dispatch := by
  exact (List.foldl_hom ResourceBatchObservation.dispatch
          (g₁ := fun acc event => acc.handleGraphEvent inventories event)
          (g₂ := GraphBatchResult.handleGraphEvent) (l := events) (init := before)
          (by intro acc event; rfl)).symm

/-- Each step extends the same legal ownership history at its actual intermediate queue. -/
theorem ResourceBatchObservation.fold_replay (before : ResourceBatchObservation)
    (inventories : ProducerInventories) (events : List GraphEvent)
    (initial : ResourceState)
    (earlier : ResourceReplay initial before.actions before.resources)
    : let after :=
        events.foldl (fun acc event => acc.handleGraphEvent inventories event) before
      ResourceReplay initial after.actions after.resources := by
  induction events generalizing before with
  | nil => exact earlier
  | cons event rest ih =>
      apply ih
      exact earlier.append (before.resources.observeDispatch_replay inventories before.dispatch.state event)

-----------------------------------------------------------------------------------------
-- The actual batch boundary controls terminal teardown and ignored late input
-----------------------------------------------------------------------------------------

/-- Mirror only the real batch wrapper's control flow. Terminal cleanup observes the
same ending.cancel used by handleGraphEvents, before its record-clearing finally block.
There are no acquisition observations here, nor any implicit inventory completeness claim.
-/
def State.observeResourceBatch (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : ResourceBatchObservation :=
  if state.stopped || state.queue.terminated then
    { dispatch := { state }, resources }
  else
    let reduced :=
      batch.foldl
        (fun acc event => acc.handleGraphEvent inventories event)
        { dispatch := { state }, resources : ResourceBatchObservation }
    let queue := reduced.dispatch.state.queue
    if queue.rootGroups.isEmpty && queue.rootStreams.isEmpty then
      let ending :=
        { reduced.dispatch.state with queue := { queue with terminated := true } }
      let (state, cleanup) := ending.cancel
      let observed := reduced.resources.observeStop ending
      {
        dispatch :=
          {
            state,
            workQueueEvents :=
              reduced.dispatch.workQueueEvents ++ [.workQueueTermination],
            effects := reduced.dispatch.effects ++ cleanup
          }
        resources := observed.1
        actions := reduced.actions ++ observed.2
      }
    else
      reduced

/-- Exact batch root: queue state, wire events and inline effects all project unchanged. -/
theorem State.observeResourceBatch_dispatch (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : (State.observeResourceBatch state resources inventories batch).dispatch
      = state.handleGraphEvents batch := by
  unfold State.observeResourceBatch State.handleGraphEvents
  split
  · rfl
  · simp only [ResourceBatchObservation.fold_dispatch]
    split
    · rfl
    · exact ResourceBatchObservation.fold_dispatch _ _ _

/-- The batch root constructs the full compatible resource history, including actual
terminal stop requests. It does not assert every native resource was acquired or represented.
-/
theorem State.observeResourceBatch_replay (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : let observed := State.observeResourceBatch state resources inventories batch
      ResourceReplay resources observed.actions observed.resources := by
  unfold State.observeResourceBatch
  split
  · exact .nil _
  · have dispatched := ResourceBatchObservation.fold_replay
      { dispatch := { state }, resources } inventories batch resources (.nil _)
    dsimp only at dispatched ⊢
    split
    · exact dispatched.append (ResourceState.observeStop_replay _ _)
    · exact dispatched

/-- A stopped or semantically terminated reader cannot adopt or finish any late input.
There is no resource observation behind the public batch guard.
-/
theorem State.observeResourceBatch_closed (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    (closed : state.stopped = true ∨ state.queue.terminated = true)
    : State.observeResourceBatch state resources inventories batch
      = { dispatch := { state }, resources } := by
  rcases closed with stopped | terminated
  · simp [State.observeResourceBatch, stopped]
  · simp [State.observeResourceBatch, terminated]

-----------------------------------------------------------------------------------------
-- Finite replay uses the same intermediate batch states as normalized publication
-----------------------------------------------------------------------------------------

/-- The current graph state and one accumulated proof-only resource history. -/
structure ResourceRunObservation where
  state : State
  resources : ResourceState
  actions : List ResourceAction := []

/-- Observe the actual next batch, including its guard and terminal teardown. -/
def ResourceRunObservation.handleBatch (before : ResourceRunObservation)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : ResourceRunObservation :=
  let observed :=
    State.observeResourceBatch before.state before.resources inventories batch
  {
    state := observed.dispatch.state
    resources := observed.resources
    actions := before.actions ++ observed.actions
  }

/-- Observe dispatch/completion/cleanup over these supplied inputs only. Acquisitions and
asynchronous settlements interleaved by a native run must still be observed independently;
the adapter is not a replacement for their complete runtime history.
-/
def State.observeResourceBatches (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batches : List (List GraphEvent))
    : ResourceRunObservation :=
  batches.foldl (fun acc batch => acc.handleBatch inventories batch) { state, resources }

private theorem ResourceRunObservation.fold_state (before : ResourceRunObservation)
    (inventories : ProducerInventories) (batches : List (List GraphEvent))
    : (batches.foldl (fun acc batch => acc.handleBatch inventories batch) before).state
      = batches.foldl (fun state batch => (state.handleGraphEvents batch).state)
          before.state := by
  exact (List.foldl_hom ResourceRunObservation.state
          (g₁ := fun acc batch => acc.handleBatch inventories batch)
          (g₂ := fun state batch => (state.handleGraphEvents batch).state)
          (l := batches) (init := before)
          (by
            intro acc batch
            exact (congrArg GraphBatchResult.state
              (State.observeResourceBatch_dispatch _ _ _ _)).symm)).symm

/-- The publisher affects output only; the actual state follows the batch-handler fold. -/
theorem State.runNormalized_stateFold (state : State) (batches : List (List GraphEvent))
    : (state.runNormalized batches).1
      = batches.foldl (fun state batch => (state.handleGraphEvents batch).state)
          state := by
  unfold State.runNormalized
  dsimp only
  exact (List.foldl_hom
          (fun acc : State
                      × ReferenceWorkQueue.IncrementalPublisher
                      × List (List Execution.WorkQueueEvent) =>
            acc.1)
          (g₂ := fun (state : State) batch => (state.handleGraphEvents batch).state)
          (l := batches)
          (by
            intro acc batch; rcases acc with ⟨state, publisher, outputs⟩; dsimp only; split <;> rfl)).symm

/-- Exact replay root: ownership observation does not change the normalized runner's state. -/
theorem State.observeResourceBatches_state (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batches : List (List GraphEvent))
    : (State.observeResourceBatches state resources inventories batches).state
      = (state.runNormalized batches).1 :=
  (ResourceRunObservation.fold_state _ _ _).trans (State.runNormalized_stateFold _ _).symm

/-- Appended batches use the actual current state, independently of publisher restart. -/
theorem State.runNormalized_append_state (state : State)
    (before after : List (List GraphEvent))
    : (state.runNormalized (before ++ after)).1
      = ((state.runNormalized before).1.runNormalized after).1 := by
  rw [State.runNormalized_stateFold, List.foldl_append,
    State.runNormalized_stateFold, State.runNormalized_stateFold]

/-- The resource observer projects to exactly the next real normalized batch state. -/
theorem State.observeResourceBatch_state (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : (State.observeResourceBatch state resources inventories batch).dispatch.state
      = (state.runNormalized [batch]).1 := by
  rw [State.observeResourceBatch_dispatch, State.runNormalized_stateFold]
  rfl

/-- The singleton convenience boundary is not a scheduling or publication policy. -/
theorem State.observeResourceSingleton_state (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (event : GraphEvent)
    : (State.observeResourceBatch state resources inventories [event]).dispatch.state
      = (state.runNormalized [[event]]).1 :=
  State.observeResourceBatch_state state resources inventories [event]

/-- One legal resource history spans every batch, including terminal and ignored suffixes. -/
theorem State.observeResourceBatches_replay (state : State) (resources : ResourceState)
    (inventories : ProducerInventories) (batches : List (List GraphEvent))
    : let observed := State.observeResourceBatches state resources inventories batches
      ResourceReplay resources observed.actions observed.resources := by
  have fold (batches : List (List GraphEvent)) (before : ResourceRunObservation)
      (earlier : ResourceReplay resources before.actions before.resources)
      : let after := batches.foldl (fun acc batch => acc.handleBatch inventories batch) before
        ResourceReplay resources after.actions after.resources := by
    induction batches generalizing before with
    | nil => exact earlier
    | cons batch rest ih =>
        apply ih
        exact earlier.append (State.observeResourceBatch_replay _ _ _ _)
  exact fold batches { state, resources } (.nil _)

-----------------------------------------------------------------------------------------
-- Released leases cannot be resurrected by any legal later ownership observation
-----------------------------------------------------------------------------------------

/-- Legal acquisition requires unacquired, so a normally completed or cleanup-settled
identity cannot be acquired a second time, stolen by adoption, or requested again.
-/
theorem ResourceStep.released_persists {before action after}
    (step : ResourceStep before action after) (target : CleanupTarget)
    (released : before target = .released)
    : after target = .released := by
  cases step with
  | acquire other owner fresh =>
      by_cases same : target = other
      · subst target; rw [released] at fresh; cases fresh
      · simp [ResourceState.set, same, released]
  | adopt producer inventory =>
      rw [before.adopt_unchanged]
      · exact released
      · rw [released]; simp
  | request other owner owned =>
      by_cases same : target = other
      · subst target; rw [released] at owned; cases owned
      · simp [ResourceState.set, same, released]
  | settle other owner requested =>
      by_cases same : target = other
      · subst target; rw [released] at requested; cases requested
      · simp [ResourceState.set, same, released]
  | finish other owner owned =>
      by_cases same : target = other
      · subst target; rw [released] at owned; cases owned
      · simp [ResourceState.set, same, released]

/-- This applies to arbitrary compatible later histories, including independently
observed acquisitions and asynchronous cleanup settlements, not just the batch adapter.
-/
theorem ResourceReplay.released_persists {before actions after}
    (replay : ResourceReplay before actions after) (target : CleanupTarget)
    (released : before target = .released)
    : after target = .released := by
  induction replay with
  | nil => exact released
  | cons step rest ih => exact ih (step.released_persists target released)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
