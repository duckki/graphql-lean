import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulStreamTransfer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedDispatchBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshot
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedPublications

/-! Actual successful contributor publication transfers prepared buffered sources through
the complete handler, including mixed release-time draining. No native inventory is acquired.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode rawStreamNoticeRefs)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Successful publication discharges the prepared buffer's transfer branch
-----------------------------------------------------------------------------------------

private theorem eagerRegistrationSnapshot_childStreams {queue : Kernel}
    (inventory : queue.ChildStreamInventory) (event : GraphEvent)
    : (eagerRegistrationSnapshot queue event).ChildStreamInventory := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using inventory
      | some node =>
          simp only [eagerRegistrationSnapshot, found]
          have known := inventory node (List.mem_of_find?_eq_some found)
          exact (inventory.putTaskNode { node with value := some result.value }
            known.1 known.2).maybeIntegrateWork result.work (some occurrence)
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte]
            using inventory
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          exact ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun current => current.ChildStreamInventory) inventory items []
            (fun _ item _ current => ((current.maybeIntegrateWork item.work).pruneEmptyGroups
              _).startNewWork _)
  | taskFailure | groupFailure | streamSuccess | streamFailure => exact inventory

private theorem eagerRegistrationSnapshot_conserves {queue : Kernel} {work settled before}
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (old
      : queue.BufferedStreamsConserved (queue.handleGraphEvent event).2.1
          (queue.handleGraphEvent event).1)
    : (eagerRegistrationSnapshot queue event).BufferedStreamsConserved
        (queue.handleGraphEvent event).2.1 (queue.handleGraphEvent event).1 := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using old
      | some node =>
          have unsettled : occurrence ∉ settled := by
            intro member
            exact fresh.2.2.1 occurrence List.mem_cons_self (included member)
          simpa only [eagerRegistrationSnapshot, found,
            ReferenceWorkQueue.State.handleGraphEvent,
            ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
            using ReferenceWorkQueue.State.taskSuccess_preparedBufferedStreams
              accounted links inventory found unsettled
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using old
      | true =>
          have preparedLinks := (eagerRegistrationSnapshot_taskEvidence accounted links included
            (.streamItems stream items) matching fresh).buffered
          have preparedChildren := eagerRegistrationSnapshot_childStreams inventory
            (.streamItems stream items)
          have preparedEq := eagerRegistrationSnapshot_streamItems queue stream items active
          rw [preparedEq] at preparedLinks preparedChildren ⊢
          have drained := ReferenceWorkQueue.State.drainReadyGroups_bufferedStreamsConserved
            preparedLinks preparedChildren
          change (queue.preparedStreamItems items).BufferedStreamsConserved
            (queue.streamItems stream items).2.1 (queue.streamItems stream items).1
          rw [queue.streamItems_eq stream items]
          simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          intro occurrence node value key found stored held owner contributes live uncancelled
          rcases drained occurrence node value key found stored held owner contributes live
            uncancelled with
            noticed | retained
          · exact Or.inl (List.mem_append_right _ noticed)
          · exact Or.inr retained
  | taskFailure | groupFailure | streamSuccess | streamFailure => exact old

private theorem registrationSnapshot_conserves {queue : Kernel} {work settled before}
    (projection : SnapshotProjection queue event)
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (old
      : queue.BufferedStreamsConserved (queue.handleGraphEvent event).2.1
          (queue.handleGraphEvent event).1)
    : (registrationSnapshot queue event).BufferedStreamsConserved
        (queue.handleGraphEvent event).2.1 (queue.handleGraphEvent event).1 := by
  have conserved := eagerRegistrationSnapshot_conserves accounted links inventory included
    event matching fresh old
  have groups := congrArg (fun queue : Kernel => queue.groupNodes.map
    (fun node => node.group.node.ref)) projection.core
  change (registrationSnapshot queue event).groupNodes.map (fun node => node.group.node.ref)
    = (eagerRegistrationSnapshot queue event).groupNodes.map (fun node => node.group.node.ref)
      at groups
  intro occurrence node value key found stored held owner contributes live uncancelled
  exact conserved occurrence node value key (projection.lookup _ _ found) stored held owner
    contributes (groups ▸ live) uncancelled

/-- Generated replay derives conservation for all prepared buffers at the exact next
handler boundary. This includes newly adopted sources, with no caller-supplied ledger.
-/
theorem generatedSnapshot_bufferedStreamsConserved {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    : let before := ((State.initialize work).runNormalized inputs).1.queue
      (registrationSnapshot before event).BufferedStreamsConserved
        (before.handleGraphEvent event).2.1 (before.handleGraphEvent event).1 := by
  dsimp only
  obtain ⟨beforeRaw, priorStarted, accepted⟩ := generatedReplay_beforeNext generated valid started
  have projection := generatedSnapshot_projection generated valid priorStarted
  rw [beforeRaw]
  rw [beforeRaw] at projection
  obtain ⟨earlier, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame :=
    (ReferenceWorkQueue.initial_uncancelledReplayFrame generated canonical).runNormalized
      (before := []) generated canonical inputs earlier
      (by rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at priorStarted)
  have links := generated.runNormalized_storedTaskLinks inputs earlier priorStarted
  have inventory := ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
    (ReferenceWorkQueue.Work.fromExecution work) inputs
  obtain ⟨_, _, publications⟩ := ReferenceWorkQueue.createWorkQueue_runNormalized_publications
    earlier
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at frame links inventory publications
  have old := ReferenceWorkQueue.State.handleGraphEvent_bufferedStreamsConserved frame.pending
    links inventory (publications.stored.mono (fun _ _ source => source.1))
    (ReferenceWorkQueue.GraphEvent.groupSettlements_subsetIdentities _) event matching fresh
  exact registrationSnapshot_conserves projection frame.pending links inventory
    (ReferenceWorkQueue.GraphEvent.groupSettlements_subsetIdentities _) matching fresh old

/-- Any prepared held source whose live contributor succeeds in this dispatch is newly
announced and active afterward. This covers the complete mixed handler, not just an isolated
flush, including newly adopted child sources. Generated retirement health derives the
uncancelled qualification of conservation.
-/
def GeneratedPublishedBufferTransfer : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → ∀ (occurrence : Occurrence) (node : TaskNode) value key owner groups streams,
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        snapshot.taskNode? occurrence = some node
        → node.value = some value
        → key ∈ node.childStreams
        → owner ∈ node.task.groups
        → owner.ref ∈ snapshot.groupNodes.map (fun group => group.group.node.ref)
        → Execution.WorkQueueEvent.groupSuccess owner groups streams
          ∈ (before.queue.handleGraphEvent event).2.1
        → key ∈ (before.queue.handleGraphEvent event).2.1.flatMap rawStreamNoticeRefs
          ∧ key ∈ reduced.state.queue.rootStreams
          ∧ .stream key ∈ reduced.state.cleanupTargets

/-- Exact pre-handler replay, reference conservation, and derived successful retirement
construct the actual source notice/root. The alternative stop map consumes that same notice.
-/
theorem GeneratedPublishedBufferTransfer_holds : GeneratedPublishedBufferTransfer := by
  intro work inputs event generated valid started occurrence node value key owner groups streams
  dsimp only
  intro found stored held contributes live carrier
  have conservation := generatedSnapshot_bufferedStreamsConserved generated valid started
  dsimp only at conservation
  obtain ⟨beforeRaw, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨earlier, matching, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame :=
    (ReferenceWorkQueue.initial_uncancelledReplayFrame generated canonical).runNormalized
      (before := []) generated canonical inputs earlier
      (by rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at priorStarted)
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches, ← beforeRaw] at frame
  obtain ⟨_, _, retirement⟩ := ReferenceWorkQueue.State.handleGraphEvent_successfulRetirements
    frame.parent frame.cancellations generated canonical event matching [] owner groups streams
      carrier
  have notice := conservation.retired_notice found stored held
    (List.mem_map.mpr ⟨owner, contributes, rfl⟩) live retirement.retired.2 retirement.uncancelled
  have actualNotice : key ∈
      (((State.initialize work).runNormalized inputs).1.queue.handleGraphEvent event).2.1.flatMap
        rawStreamNoticeRefs := notice
  have dispatch := generatedReplay_dispatchProjection generated valid started
  exact ⟨actualNotice, (congrArg (fun pair => pair.1.rootStreams) dispatch).symm ▸
      graphEvent_newStream_active _ _ actualNotice,
    GraphBatchResult.releasedStream_cleanupTarget _ _ dispatch actualNotice⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
