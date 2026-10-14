import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RawResourceInvariant

/-! Construct acquired-lease record preservation through the actual arbitrary-width FIFO
fold and terminal batch wrapper. Incoming structural identities refer to its real intermediate
resource states. No endpoint law, native inventory completeness or narrower source is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
private abbrev initial (work : Work) :=
  ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)

-----------------------------------------------------------------------------------------
-- Structural identity at each actual FIFO handoff, not desired endpoint coverage
-----------------------------------------------------------------------------------------

/-- Native abstraction-map evidence at each actual intermediate adoption site.
Only independently owned incoming task/source identities are constrained.
-/
def BatchProducerIdentities (work : Work) (before : ResourceBatchObservation)
    (inventories : ProducerInventories) (batch : List GraphEvent)
    : Prop :=
  ∀ earlier event later,
    batch = earlier ++ event :: later
    → let current :=
        earlier.foldl (fun acc event => acc.handleGraphEvent inventories event) before
      ProducerTasksMatchWork work current.resources inventories
        (graphEffects current.dispatch.state.queue event)
      ∧ ProducerSourcesMatchWork work current.resources inventories
          (graphEffects current.dispatch.state.queue event)

-----------------------------------------------------------------------------------------
-- Every input uses the same accepted history and real FIFO accumulator
-----------------------------------------------------------------------------------------

/-- Raw record/pending-history preservation spans the entire actual FIFO fold.
This also covers roots becoming empty before the wrapper's final clearing step.
-/
theorem generatedRaw_resourceFold {work past batch before inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (past ++ batch))
    (accepted : (initial work).acceptsBatch (past ++ batch) = true)
    (same : before.dispatch.state.queue = (initial work).replayGraphEvents past)
    (running : before.dispatch.state.stopped = false)
    (represented
      : QueueResourcesRepresented before.dispatch.state.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements past) before.resources)
    (identities : BatchProducerIdentities work before inventories batch)
    : let after :=
        batch.foldl (fun acc event => acc.handleGraphEvent inventories event) before
      after.dispatch.state.queue = (initial work).replayGraphEvents (past ++ batch)
      ∧ QueueResourcesRepresented after.dispatch.state.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements (past ++ batch))
          after.resources := by
  induction batch generalizing past before with
  | nil => simpa only [List.append_nil, List.foldl_nil] using And.intro same represented
  | cons event rest ih =>
      obtain ⟨tasks, sources⟩ := identities [] event rest rfl
      have firstValid : ReferenceWorkQueue.ValidGraphEvents work (past ++ [event]) :=
        valid.prefix ⟨rest, by simp⟩
      have firstAccepted : (initial work).acceptsBatch (past ++ [event]) = true :=
        ReferenceWorkQueue.State.acceptsBatch_prefix (by simpa only [List.append_assoc, List.singleton_append] using accepted)
      have progress := generatedRaw_resourceInvariant generated firstValid firstAccepted
        (same ▸ represented) (same ▸ tasks) (same ▸ sources)
      let next := before.handleGraphEvent inventories event
      have beforeState : before.dispatch.state = { queue := (initial work).replayGraphEvents past } := by
        rw [State.eq_queue_of_running _ running, same]
      have nextSame : next.dispatch.state.queue = (initial work).replayGraphEvents (past ++ [event]) := by
        rw [ReferenceWorkQueue.State.replayGraphEvents_append, ← same]
        change (before.dispatch.state.handleGraphEvent event).1.queue
          = (before.dispatch.state.queue.handleGraphEvent event).1
        rw [beforeState]
        exact congrArg Prod.fst (referencePrefix_handleGraphEvent generated past event firstValid
          (ReferenceWorkQueue.State.acceptsBatch_prefix firstAccepted))
      have nextRunning : next.dispatch.state.stopped = false :=
        (State.handleGraphEvent_stopped before.dispatch.state event).trans running
      have observer := before.resources.observeDispatch_sameQueue inventories before.dispatch.state
        { queue := (initial work).replayGraphEvents past } event same running
      have nextRepresented : QueueResourcesRepresented next.dispatch.state.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements (past ++ [event])) next.resources := by
        rw [nextSame, ReferenceWorkQueue.GraphEvent.taskSettlements_append,
          ReferenceWorkQueue.State.replayGraphEvents_append]
        change QueueResourcesRepresented (((initial work).replayGraphEvents past).handleGraphEvent event).1
          (event.recordTaskOutcome (ReferenceWorkQueue.GraphEvent.taskSettlements past))
          (before.resources.observeDispatch inventories before.dispatch.state event).1
        rw [observer]
        exact progress
      have nextIdentities : BatchProducerIdentities work next inventories rest := by
        intro earlier input later partition
        have result := identities (event :: earlier) input later
          (by simpa only [List.cons_append] using congrArg (List.cons event) partition)
        simpa only [List.foldl_cons] using result
      have suffix := ih (past := past ++ [event])
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
        (by simpa only [List.append_assoc, List.singleton_append] using accepted)
        nextSame nextRunning nextRepresented nextIdentities
      simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using suffix

/-- All root/record evidence is derived at the actual pre-clear raw endpoint. -/
theorem generatedRaw_recordRootEvidence {work events}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work events)
    (accepted : (initial work).acceptsBatch events = true)
    : let queue := (initial work).replayGraphEvents events
      queue.GroupMembershipSound
      ∧ queue.StartedTasksRegistered
      ∧ queue.LiveContributorsCovered
      ∧ queue.BufferedOwnersPresent := by
  have ledger := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated events valid accepted
  exact ⟨ledger.sound, ledger.started, generated.replayGraphEvents_liveContributorsCovered _ valid accepted,
    generated.replayGraphEvents_bufferedOwnersPresent _ valid accepted⟩

-----------------------------------------------------------------------------------------
-- The actual arbitrary-width wrapper retains records or safely clears them
-----------------------------------------------------------------------------------------

/-- The next started batch has not crossed the same public terminal/stopped guard. -/
theorem generatedReplay_beforeBatchRunning {work inputs batch}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1
      before.stopped = false ∧ before.queue.terminated = false := by
  dsimp only
  obtain ⟨raw, priorStarted, _⟩ := generatedReplay_beforeBatch generated valid started
  have flag : ((State.initialize work).runNormalized inputs).1.queue.terminated = false := by
    rw [raw, ← ReferenceWorkQueue.State.rawEventReplay_state, ReferenceWorkQueue.State.rawEventReplay_terminated]
    exact ReferenceWorkQueue.createWorkQueue_terminated _
  refine ⟨?_, flag⟩
  rw [State.runNormalized_initialize work inputs generated valid priorStarted] at flag ⊢
  simp only [State.fromReference] at flag ⊢
  split <;> simp_all [State.clearRecords]

/-- Every started generated FIFO batch preserves record/pending-history coverage and
constructs a compatible legal history. Terminal erasure leaves no queue-owned remainder.
Incoming identities use the same real fold, not a separately chosen collection of snapshots.
-/
def GeneratedResourceBatchInvariant : Prop :=
  ∀ work inputs batch,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch)
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let observed := State.observeResourceBatch before resources inventories batch
        QueueResourcesRepresented before.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
        → BatchProducerIdentities work { dispatch := { state := before }, resources }
            inventories batch
        → ResourceReplay resources observed.actions observed.resources
          ∧ QueueResourcesRepresented observed.dispatch.state.queue
              (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
              observed.resources
          ∧ (observed.dispatch.state.stopped = true
              → ∀ target, observed.resources target ≠ .owned .queue)

/-- Compose the raw FIFO induction with generated topology before terminal clearing.
The model never obtains resource safety merely by erasing a record or setting stopped.
-/
theorem GeneratedResourceBatchInvariant_holds : GeneratedResourceBatchInvariant := by
  intro work inputs batch generated valid started resources inventories
  dsimp only
  intro represented identities
  let before := ((State.initialize work).runNormalized inputs).1
  let first : ResourceBatchObservation := { dispatch := { state := before }, resources }
  let reduced := batch.foldl (fun acc event => acc.handleGraphEvent inventories event) first
  have accepted : (initial work).acceptsBatch (inputs.flatten ++ batch) = true := by
    have all := (initial work).batchesStarted_acceptsBatch (inputs ++ [batch])
      (by rwa [← ReferenceWorkQueue.inputsStarted_eq_batchesStarted])
    simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using all
  have priorValid := valid.prefix ⟨batch, rfl⟩
  obtain ⟨running, active⟩ := generatedReplay_beforeBatchRunning generated priorValid started
  obtain ⟨same, after⟩ := generatedRaw_resourceFold generated valid accepted
    (generatedReplay_beforeBatch generated priorValid started).1 running represented identities
  refine ⟨State.observeResourceBatch_replay before resources inventories batch, ?_⟩
  change QueueResourcesRepresented (State.observeResourceBatch before resources inventories batch).dispatch.state.queue
      (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
      (State.observeResourceBatch before resources inventories batch).resources
    ∧ ((State.observeResourceBatch before resources inventories batch).dispatch.state.stopped = true
      → ∀ target, (State.observeResourceBatch before resources inventories batch).resources target ≠ .owned .queue)
  change before.stopped = false at running
  change before.queue.terminated = false at active
  simp only [State.observeResourceBatch, running, active, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  by_cases empty :
    (reduced.dispatch.state.queue.rootGroups.isEmpty
      && reduced.dispatch.state.queue.rootStreams.isEmpty)
    = true
  · change (batch.foldl (fun acc event => acc.handleGraphEvent inventories event) first).dispatch.state.queue
        = (initial work).replayGraphEvents (inputs.flatten ++ batch) at same
    obtain ⟨sound, registered, covered, owners⟩ := generatedRaw_recordRootEvidence generated valid accepted
    have noOwned := after.emptyRoots_no_owned (same.symm ▸ sound) (same.symm ▸ registered)
      (same.symm ▸ covered) (same.symm ▸ owners) empty
    have requestedNoOwned : ∀ state target, (reduced.resources.observeStop state).1 target ≠ .owned .queue := by
      intro state target owned
      obtain ⟨earlier, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
      exact noOwned target earlier
    dsimp only [reduced, first] at empty
    simp only [empty, ↓reduceIte]
    exact ⟨⟨fun occurrence owned => False.elim (requestedNoOwned _ _ owned),
      fun key owned => False.elim (requestedNoOwned _ _ owned)⟩, fun _ => requestedNoOwned _⟩
  · dsimp only [reduced, first] at empty
    simp only [empty, Bool.false_eq_true, ↓reduceIte]
    refine ⟨after, ?_⟩
    intro stopped
    have preserved : reduced.dispatch.state.stopped = before.stopped := by
      have loop (events : List GraphEvent) (current : ResourceBatchObservation)
          : (events.foldl (fun acc event => acc.handleGraphEvent inventories event) current).dispatch.state.stopped
              = current.dispatch.state.stopped := by
        induction events generalizing current with
        | nil => rfl
        | cons event rest ih =>
            rw [List.foldl_cons, ih]
            exact State.handleGraphEvent_stopped current.dispatch.state event
      exact loop batch first
    change reduced.dispatch.state.stopped = true at stopped
    rw [preserved, running] at stopped
    cases stopped

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
