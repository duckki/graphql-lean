import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulStreamTransfer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedDispatchBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshot
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulReleaseReplay

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
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using inventory
      | true =>
          rw [eagerRegistrationSnapshot_streamItems queue stream items active]
          exact ReferenceWorkQueue.State.preparedStreamItems_preserves
            (fun current => current.ChildStreamInventory) inventory items
            (fun _ item _ current => ((current.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
  | taskFailure | streamSuccess | streamFailure => exact inventory

private theorem eagerRegistrationSnapshot_conserves {queue : Kernel} {work settled before}
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (old
      : queue.BufferedStreamsConserved (queue.handleGraphEvent event).2
          (queue.handleGraphEvent event).1)
    : (eagerRegistrationSnapshot queue event).BufferedStreamsConserved
        (queue.handleGraphEvent event).2 (queue.handleGraphEvent event).1 := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none => simpa only [eagerRegistrationSnapshot, found] using old
      | some node =>
          have unsettled : occurrence ∉ settled := by
            intro member
            exact fresh.2.2.1 occurrence List.mem_cons_self (included member)
          simpa only [eagerRegistrationSnapshot, found,
            ReferenceWorkQueue.State.handleGraphEvent]
            using ReferenceWorkQueue.State.taskSuccess_preparedBufferedStreams
              accounted links inventory found unsettled
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.ref with
      | false =>
          simpa only [eagerRegistrationSnapshot, active, Bool.false_eq_true, ↓reduceIte] using old
      | true =>
          have preparedLinks := (eagerRegistrationSnapshot_taskEvidence accounted links included
            (.streamItems stream items) matching fresh).buffered
          have preparedChildren := eagerRegistrationSnapshot_childStreams inventory (.streamItems stream items)
          rw [eagerRegistrationSnapshot_streamItems queue stream items active] at preparedLinks preparedChildren ⊢
          have drained := ReferenceWorkQueue.State.drainReadyGroups_bufferedStreamsConserved
            preparedLinks preparedChildren
          change (queue.preparedStreamItems items).BufferedStreamsConserved
            (queue.streamItems stream items).2 (queue.streamItems stream items).1
          rw [queue.streamItems_eq stream items]
          simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          intro occurrence node value key found stored held owner contributes live uncancelled
          rcases drained occurrence node value key found stored held owner contributes live uncancelled with
            noticed | retained
          · exact Or.inl (List.mem_append_right _ noticed)
          · exact Or.inr retained
  | taskFailure | streamSuccess | streamFailure => exact old

private theorem registrationSnapshot_conserves {queue : Kernel} {work settled before}
    (projection : SnapshotProjection queue event)
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory)
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (old
      : queue.BufferedStreamsConserved (queue.handleGraphEvent event).2
          (queue.handleGraphEvent event).1)
    : (registrationSnapshot queue event).BufferedStreamsConserved
        (queue.handleGraphEvent event).2 (queue.handleGraphEvent event).1 := by
  have conserved := eagerRegistrationSnapshot_conserves accounted links inventory included
    event matching fresh old
  have groups := congrArg (fun queue : Kernel => queue.groupNodes.map
    (fun node => node.group.node.ref)) projection.core
  change (registrationSnapshot queue event).groupNodes.map (fun node => node.group.node.ref)
    = (eagerRegistrationSnapshot queue event).groupNodes.map (fun node => node.group.node.ref) at groups
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
        (before.handleGraphEvent event).2 (before.handleGraphEvent event).1 := by
  dsimp only
  obtain ⟨beforeRaw, priorStarted, accepted⟩ := generatedReplay_beforeNext generated valid started
  have projection := generatedSnapshot_projection generated valid priorStarted
  rw [beforeRaw]
  rw [beforeRaw] at projection
  obtain ⟨earlier, matching, fresh⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  have old := generated.handleGraphEvent_bufferedStreamsConserved earlier accepted matching fresh
  have accounted := (ReferenceWorkQueue.createWorkQueue_pendingAccounting work).replayGraphEvents
    (before := []) generated inputs.flatten earlier accepted
  have links := generated.replayGraphEvents_storedTaskLinks inputs.flatten earlier accepted
  have inventory := generatedReplay_childStreamInventory work inputs generated earlier priorStarted
  rw [beforeRaw] at inventory
  exact registrationSnapshot_conserves projection accounted links inventory
    (ReferenceWorkQueue.GraphEvent.taskSettlements_subsetIdentities _) matching fresh old

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
          ∈ (before.queue.handleGraphEvent event).2
        → key ∈ (before.queue.handleGraphEvent event).2.flatMap rawStreamNoticeRefs
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
  obtain ⟨beforeRaw, _, accepted⟩ := generatedReplay_beforeNext generated valid started
  rw [beforeRaw] at found live carrier conservation
  obtain ⟨_, _, retired, _, uncancelled⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy valid accepted carrier
  rw [ReferenceWorkQueue.State.replayGraphEvents_append] at retired uncancelled
  have notice := conservation.retired_notice found stored held
    (List.mem_map.mpr ⟨owner, contributes, rfl⟩) live retired.2 uncancelled
  have actualNotice : key ∈
      (((State.initialize work).runNormalized inputs).1.queue.handleGraphEvent event).2.flatMap
        rawStreamNoticeRefs := by rwa [beforeRaw]
  have dispatch := generatedReplay_dispatchProjection generated valid started
  exact ⟨actualNotice, (congrArg (fun pair => pair.1.rootStreams) dispatch).symm ▸
      graphEvent_newStream_active _ _ actualNotice,
    GraphBatchResult.releasedStream_cleanupTarget _ _ dispatch actualNotice⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
