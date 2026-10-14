import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.DispatchResourceInvariant
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceBatchReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveContributorReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedOwnerExistence

/-! Empty-root terminal clearing cannot forget any represented acquired queue lease.
Topology/ownership evidence is derived before clearing, at the same actual dispatch.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Every concrete record location requires an active graph root
-----------------------------------------------------------------------------------------

/-- Membership soundness and contributor coverage protect task records; live owners of
stored buffers protect held sources. Active sources are already explicit roots.
-/
theorem recordTargetRequiresRoot {queue : Kernel}
    (sound : queue.GroupMembershipSound) (started : queue.StartedTasksRegistered)
    (covered : queue.LiveContributorsCovered) (owners : queue.BufferedOwnersPresent)
    {target} (represented : RecordTargetRepresented queue target)
    : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) ≠ true := by
  intro empty
  obtain ⟨noGroups, noStreams⟩ := Bool.and_eq_true_iff.mp empty
  have noRoot : ∀ root, root ∉ queue.rootGroups := by
    rw [List.isEmpty_iff.mp noGroups]
    simp
  cases represented with
  | @task key occurrence group found linked =>
      obtain ⟨task, registered, _, contributes⟩ := sound group (List.mem_of_find?_eq_some found) occurrence linked
      obtain ⟨root, active, _⟩ := covered task registered group.group.node.ref contributes
        ⟨group, (ReferenceWorkQueue.State.groupNode?_ref found).symm ▸ found⟩
      exact noRoot root active
  | activeStream active =>
      rw [List.isEmpty_iff.mp noStreams] at active
      cases active
  | bufferedStream found stored _ =>
      obtain ⟨key, contributes, live⟩ := owners _ (List.mem_of_find?_eq_some found) stored
      have lookup : ∃ group, queue.groupNode? key = some group := by
        cases tested : queue.groupNode? key with
        | some group => exact ⟨group, rfl⟩
        | none => exact False.elim ((queue.groupNode?_eq_none_iff key).mp tested live)
      obtain ⟨root, active, _⟩ := covered _ (started _ (List.mem_of_find?_eq_some found)) key contributes lookup
      exact noRoot root active

/-- No queue lease can remain when the concrete represented state has no roots. -/
theorem QueueResourcesRepresented.emptyRoots_no_owned {queue settled resources}
    (represented : QueueResourcesRepresented queue settled resources)
    (sound : queue.GroupMembershipSound) (started : queue.StartedTasksRegistered)
    (covered : queue.LiveContributorsCovered) (owners : queue.BufferedOwnersPresent)
    (empty : (queue.rootGroups.isEmpty && queue.rootStreams.isEmpty) = true)
    : ∀ target, resources target ≠ .owned .queue := by
  intro target owned
  exact recordTargetRequiresRoot sound started covered owners (represented.records target owned) empty

-----------------------------------------------------------------------------------------
-- Derive root evidence at the actual generated pre-clear handler endpoint
-----------------------------------------------------------------------------------------

/-- The actual endpoint, before terminal erasure, has sound task records and rooted owners.
This strengthens neither the input contract nor native resource-inventory completeness.
-/
theorem generatedDispatch_recordRootEvidence {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1
      let after := (before.handleGraphEvent event).1.queue
      after.GroupMembershipSound
      ∧ after.StartedTasksRegistered
      ∧ after.LiveContributorsCovered
      ∧ after.BufferedOwnersPresent := by
  dsimp only
  have endpoint : (((State.initialize work).runNormalized inputs).1.handleGraphEvent event).1.queue
      = (((State.initialize work).runNormalized inputs).1.queue.handleGraphEvent event).1 :=
    congrArg Prod.fst (generatedReplay_dispatchProjection generated valid started)
  rw [endpoint]
  let before := ((State.initialize work).runNormalized inputs).1.queue
  obtain ⟨prior, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨raw, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  have accounted := generatedReplay_nextAccounting generated valid started
  have next := accounted.handleGraphEvent generated
    (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _) event matching fresh
    (generatedReplay_nextAccepted generated valid started)
  refine ⟨next.sound, next.started, ?_, ?_⟩
  · have accepted : (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)).acceptsBatch
        (inputs.flatten ++ [event]) = true := by
      have all := (ReferenceWorkQueue.State.initialize (ReferenceWorkQueue.Work.fromExecution work)).batchesStarted_acceptsBatch
        (inputs ++ [[event]]) (by rwa [← ReferenceWorkQueue.inputsStarted_eq_batchesStarted])
      simpa only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil] using all
    have covered := generated.replayGraphEvents_liveContributorsCovered _ valid accepted
    rw [ReferenceWorkQueue.State.replayGraphEvents_append] at covered
    rwa [raw]
  · have owners := generatedReplay_bufferedOwnersPresent generated prior priorStarted
    have links := (generatedReplay_taskInvariants generated inputs prior priorStarted).2.2
    exact owners.handleGraphEvent links accounted event matching fresh

-----------------------------------------------------------------------------------------
-- Terminal record clearing cannot erase an outstanding owned lease
-----------------------------------------------------------------------------------------

/-- All still-owned leases have disappeared by normal completion or actual pruning when
this generated dispatch empties both root sets. Terminal erasure cannot hide an orphan.
-/
def GeneratedDispatchTerminalNoOwned : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        QueueResourcesRepresented before.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
        → ProducerTasksMatchWork work resources inventories
            (graphEffects before.queue event)
        → ProducerSourcesMatchWork work resources inventories
            (graphEffects before.queue event)
        → (reduced.state.queue.rootGroups.isEmpty
            && reduced.state.queue.rootStreams.isEmpty)
          = true
        → ∀ target,
            (resources.observeDispatch inventories before event).1 target ≠ .owned .queue

/-- Combine acquired-lease progress and endpoint topology before any record is cleared. -/
theorem GeneratedDispatchTerminalNoOwned_holds : GeneratedDispatchTerminalNoOwned := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro represented taskIdentity sourceIdentity empty
  have after := GeneratedDispatchResourcesRepresented_holds work inputs event generated valid started
    resources inventories represented taskIdentity sourceIdentity
  obtain ⟨sound, registered, covered, owners⟩ := generatedDispatch_recordRootEvidence generated valid started
  exact after.emptyRoots_no_owned sound registered covered owners empty

-----------------------------------------------------------------------------------------
-- The real batch wrapper preserves the invariant through terminal clearing
-----------------------------------------------------------------------------------------

/-- A generated next input has not crossed the stopped/terminated batch guard. -/
theorem generatedReplay_nextRunning {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1
      before.stopped = false ∧ before.queue.terminated = false := by
  dsimp only
  have raw := (generatedReplay_beforeNext generated valid started).1
  have flag : ((State.initialize work).runNormalized inputs).1.queue.terminated = false := by
    rw [raw, ← ReferenceWorkQueue.State.rawEventReplay_state,
      ReferenceWorkQueue.State.rawEventReplay_terminated]
    exact ReferenceWorkQueue.createWorkQueue_terminated _
  refine ⟨?_, flag⟩
  rw [generatedReplay_beforeNextState generated valid started]

/-- The actual singleton FIFO batch observes the same generated invariant, including its
terminal branch. Batch width one is a proof boundary, not a new publication/source policy.
-/
def GeneratedResourceSingletonBatchInvariant : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (resources : ResourceState) (inventories : ProducerInventories),
        let before := ((State.initialize work).runNormalized inputs).1
        let observed := State.observeResourceBatch before resources inventories [event]
        QueueResourcesRepresented before.queue
          (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten) resources
        → ProducerTasksMatchWork work resources inventories
            (graphEffects before.queue event)
        → ProducerSourcesMatchWork work resources inventories
            (graphEffects before.queue event)
        → ResourceReplay resources observed.actions observed.resources
          ∧ QueueResourcesRepresented observed.dispatch.state.queue
              (event.recordTaskOutcome
                (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
              observed.resources
          ∧ (observed.dispatch.state.stopped = true
              → ∀ target, observed.resources target ≠ .owned .queue)

/-- The terminal case already has no owned leases before clearing, derived from its real
records and generated roots. Stop requests cannot reintroduce ownership; open batches retain
the dispatch invariant. The guard is discharged by the existing start checker.
-/
theorem GeneratedResourceSingletonBatchInvariant_holds
    : GeneratedResourceSingletonBatchInvariant := by
  intro work inputs event generated valid started resources inventories
  dsimp only
  intro represented taskIdentity sourceIdentity
  let before := ((State.initialize work).runNormalized inputs).1
  refine ⟨State.observeResourceBatch_replay before resources inventories [event], ?_⟩
  obtain ⟨running, active⟩ := generatedReplay_nextRunning generated valid started
  have after := GeneratedDispatchResourcesRepresented_holds work inputs event generated valid started
    resources inventories represented taskIdentity sourceIdentity
  simp only [State.observeResourceBatch, running, active, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, List.foldl_cons, List.foldl_nil, ResourceBatchObservation.handleGraphEvent]
  by_cases empty :
    ((({ state := before } : GraphBatchResult).handleGraphEvent
        event).state.queue.rootGroups.isEmpty
      && (({ state := before } : GraphBatchResult).handleGraphEvent
            event).state.queue.rootStreams.isEmpty)
    = true
  · dsimp only [before] at empty
    simp only [empty, ↓reduceIte]
    have noOwned := GeneratedDispatchTerminalNoOwned_holds work inputs event generated valid started
      resources inventories represented taskIdentity sourceIdentity empty
    have stoppedNoOwned : ∀ target,
        ((resources.observeDispatch inventories before event).1.observeStop
          { (({ state := before } : GraphBatchResult).handleGraphEvent event).state with
            queue := { (({ state := before } : GraphBatchResult).handleGraphEvent event).state.queue with terminated := true } }).1
          target ≠ .owned .queue := by
      intro target owned
      obtain ⟨earlier, _⟩ := ResourceState.requestQueueCleanup_still_owned _ _ target owned
      exact noOwned target earlier
    exact ⟨⟨fun occurrence owned => False.elim (stoppedNoOwned _ owned),
      fun key owned => False.elim (stoppedNoOwned _ owned)⟩, fun _ => stoppedNoOwned⟩
  · dsimp only [before] at empty
    simp only [empty, Bool.false_eq_true, ↓reduceIte]
    refine ⟨after, ?_⟩
    intro stopped
    change (before.handleGraphEvent event).1.stopped = true at stopped
    rw [State.handleGraphEvent_stopped, running] at stopped
    cases stopped

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
