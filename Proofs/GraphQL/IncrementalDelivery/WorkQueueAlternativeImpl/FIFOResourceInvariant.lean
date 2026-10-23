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
        earlier.foldl
          (fun acc event =>
            acc.handleGraphEvent inventories event
              (ReferenceWorkQueue.GraphEvent.availableFailures batch))
          before
      ProducerTasksMatchWork work current.resources inventories
        (graphEffects current.dispatch.state.queue event)
      ∧ ProducerSourcesMatchWork work current.resources inventories
          (graphEffects current.dispatch.state.queue event)

/-- The actual FIFO fold preserves the full representation invariant at batch completion.
Intermediate cuts use full-batch exclusions while keeping the consumed-outcome ledger exact.
-/
theorem generatedRaw_resourceFold {work inputs batch resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    (represented
      : QueueResourcesRepresented
          ((State.initialize work).runNormalized inputs).1.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources)
    (identities
      : BatchProducerIdentities work
          {
            dispatch := { state := ((State.initialize work).runNormalized inputs).1 },
            resources
          }
          inventories batch)
    : let after := resourceFifoPrefix work inputs batch batch resources inventories
      QueueResourcesRepresented after.dispatch.state.queue
        (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
        after.resources := by
  have loop (remaining fifo : List GraphEvent) (partition : batch = fifo ++ remaining)
      (prior : let actual := resourceFifoPrefix work inputs batch fifo resources inventories
        BatchResourcesRepresented actual.dispatch.state.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ fifo))
          (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
          actual.resources)
      : let after := resourceFifoPrefix work inputs batch batch resources inventories
        QueueResourcesRepresented after.dispatch.state.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
          after.resources := by
    induction remaining generalizing fifo with
    | nil =>
        have same : batch = fifo := by simpa only [List.append_nil] using partition
        subst fifo
        exact prior.complete
    | cons event rest ih =>
        obtain ⟨tasks, sources⟩ := identities fifo event rest partition
        have next := generatedRaw_resourceInvariant generated valid started partition prior tasks
          sources
        have combined : resourceFifoPrefix work inputs batch (fifo ++ [event]) resources inventories
            = (resourceFifoPrefix work inputs batch fifo resources inventories).handleGraphEvent
                inventories event (ReferenceWorkQueue.GraphEvent.availableFailures batch) := by
          simp only [resourceFifoPrefix, List.foldl_append, List.foldl_cons, List.foldl_nil]
        apply ih (fifo ++ [event])
          (by simpa only [List.append_assoc, List.singleton_append] using partition)
        rw [combined]
        simpa only [List.append_assoc] using next
  apply loop batch [] (by simp)
  simpa only [resourceFifoPrefix, List.foldl_nil, List.append_nil]
    using (represented.batch
            (excluded :=
              ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch)))

/-- Root evidence is derived at the actual exposed pre-clear endpoint. Cache exposure
changes no roots, memberships, contributors, or stored-source attachment.
-/
theorem generatedRaw_recordRootEvidence {work inputs batch resources inventories}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ batch))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    : let actual := resourceFifoPrefix work inputs batch batch resources inventories
      let queue :=
        actual.dispatch.state.queue.cacheTaskFailures
          (ReferenceWorkQueue.GraphEvent.availableFailures batch)
      queue.GroupMembershipSound
      ∧ queue.StartedTasksRegistered
      ∧ queue.LiveContributorsCovered
      ∧ queue.BufferedOwnersPresent := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := resourceFifoPrefix_sourceFrame (resources := resources)
    (inventories := inventories)
    generated canonical valid started (fifo := batch) (tail := []) (by simp)
  have ledger := resourceFifoPrefix_pendingAccounting (resources := resources)
    (inventories := inventories) generated valid started (fifo := batch) (tail := []) (by simp)
  refine ⟨ledger.sound, ledger.started, ?_, source.tasks.owners.buffered⟩
  rw [(resourceFifoPrefix_cacheProjection generated valid started (fifo := batch) (tail := [])
    (by simp)).1]
  exact (generated.batchPrefix_liveContributorsCovered valid started (fifo := batch)
          (tail := []) (by simp)).cacheTaskFailures
    _

/-- The started next batch begins before the public terminal/stopped guard. -/
theorem generatedReplay_beforeBatchRunning {work inputs batch}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [batch]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1
      before.stopped = false ∧ before.queue.terminated = false := by
  obtain ⟨same, active⟩ := generatedResource_beforeBatch generated valid started
  rw [same]
  exact ⟨rfl, active⟩

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

/-- Compose actual cached FIFO resource progress with topology before terminal erasure.
No record is deemed safe merely because the wrapper clears it or marks the reader stopped.
-/
theorem GeneratedResourceBatchInvariant_holds : GeneratedResourceBatchInvariant := by
  intro work inputs batch generated valid started resources inventories
  dsimp only
  intro represented identities
  let before := ((State.initialize work).runNormalized inputs).1
  let first : ResourceBatchObservation := { dispatch := { state := before }, resources }
  let available := ReferenceWorkQueue.GraphEvent.availableFailures batch
  let reduced :=
    batch.foldl (fun acc event => acc.handleGraphEvent inventories event available) first
  have after := generatedRaw_resourceFold generated valid started represented identities
  have priorValid := valid.prefix ⟨batch, rfl⟩
  obtain ⟨running, active⟩ := generatedReplay_beforeBatchRunning generated priorValid started
  refine ⟨State.observeResourceBatch_replay before resources inventories batch, ?_⟩
  change QueueResourcesRepresented
      (State.observeResourceBatch before resources inventories batch).dispatch.state.queue
      (ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch))
      (State.observeResourceBatch before resources inventories batch).resources
    ∧ ((State.observeResourceBatch before resources inventories batch).dispatch.state.stopped = true
      → ∀ target, (State.observeResourceBatch before resources inventories batch).resources target
        ≠ .owned .queue)
  change before.stopped = false at running
  change before.queue.terminated = false at active
  simp only [State.observeResourceBatch, running, active, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte]
  by_cases empty :
    (reduced.dispatch.state.queue.rootGroups.isEmpty
      && reduced.dispatch.state.queue.rootStreams.isEmpty
      && reduced.dispatch.state.queue.groupFailureEvents.isEmpty) = true
  · have keys := resourceFifoPrefix_taskKeys (resources := resources) (inventories := inventories)
      generated valid started (fifo := batch) (tail := []) (by simp)
    have licensed (occurrence errors) (member : (occurrence, errors) ∈ available)
        : occurrence ∈ ReferenceWorkQueue.GraphEvent.taskSettlements (inputs.flatten ++ batch) := by
      obtain ⟨event, included, failure⟩ := List.mem_filterMap.mp member
      cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at failure
      obtain ⟨rfl, rfl⟩ := failure
      exact List.mem_reverse.mpr (List.mem_flatMap.mpr
        ⟨_, List.mem_append_right _ included, List.mem_cons_self⟩)
    have exposed := (after.batch.cacheTaskFailures keys available licensed).complete
    obtain ⟨sound, registered, covered, owners⟩ := generatedRaw_recordRootEvidence
      (resources := resources) (inventories := inventories) generated valid started
    have roots := reduced.dispatch.state.queue.cacheTaskFailures_frame available
    have emptyExposed :
        ((reduced.dispatch.state.queue.cacheTaskFailures available).rootGroups.isEmpty
        && (reduced.dispatch.state.queue.cacheTaskFailures available).rootStreams.isEmpty)
          = true := by
      have groups := congrArg ReferenceWorkQueue.State.rootGroups roots
      have streams := congrArg ReferenceWorkQueue.State.rootStreams roots
      rw [groups, streams]
      exact (Bool.and_eq_true_iff.mp empty).1
    have noOwned := exposed.emptyRoots_no_owned sound registered covered owners emptyExposed
    have requestedNoOwned : ∀ state target,
        (reduced.resources.observeStop state).1 target ≠ .owned .queue := by
      intro state target owned
      obtain ⟨earlier, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
      exact noOwned target earlier
    dsimp only [reduced, first, available] at empty
    simp only [empty, ↓reduceIte]
    exact ⟨⟨fun occurrence owned => False.elim (requestedNoOwned _ _ owned),
      fun key owned => False.elim (requestedNoOwned _ _ owned)⟩, fun _ => requestedNoOwned _⟩
  · dsimp only [reduced, first, available] at empty
    simp only [empty, Bool.false_eq_true, ↓reduceIte]
    refine ⟨after, ?_⟩
    intro stopped
    have preserved : reduced.dispatch.state.stopped = before.stopped := by
      have loop (events : List GraphEvent) (current : ResourceBatchObservation)
          : (events.foldl (fun acc event => acc.handleGraphEvent inventories event available)
              current).dispatch.state.stopped = current.dispatch.state.stopped := by
        induction events generalizing current with
        | nil => rfl
        | cons event rest ih =>
            rw [List.foldl_cons, ih]
            exact State.handleGraphEvent_stopped current.dispatch.state event available
      exact loop batch first
    change reduced.dispatch.state.stopped = true at stopped
    rw [preserved, running] at stopped
    cases stopped

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
