import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessFoldRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationActivationSafety

/-! Generated source histories construct the universal pending-buffer cut and hence
actual mixed-release source disposal. Native acquisition/whole-replay coverage is separate.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Generated preparation derives the exact domain needed by the handler construction
-----------------------------------------------------------------------------------------

private theorem viewOwner_present {before : Kernel} {event events key group}
    (found : (failurePruningView before event events).groupNode? key = some group)
    : key
      ∈ (registrationSnapshot before event).groupNodes.map
          (fun group => group.group.node.ref) := by
  obtain ⟨old, member, same, _⟩ := failurePruningView_groupOrigin
    (List.mem_of_find?_eq_some found)
  exact List.mem_map.mpr ⟨old, member,
    (congrArg (fun group : ReferenceWorkQueue.Group => group.node.ref) same).symm.trans
      (ReferenceWorkQueue.State.groupNode?_ref found)⟩

-----------------------------------------------------------------------------------------
-- Every generated success/item dispatch constructs the same actual owner cut
-----------------------------------------------------------------------------------------

/-- Universal construction of the pending-buffer failure cut. Generated preparation
supplies registration, catalogue equality, and the finite forest; the actual success fold
retains unpublished buffers/owners and supplies closure evidence for the actual mixed drain.
Rejected fresh successes cannot remove an earlier stored occurrence. No cut or native
resource inventory is assumed, and the original host/source contract is unchanged.
-/
theorem GeneratedPendingBufferLossCut_holds : GeneratedPendingBufferLossCut := by
  intro work inputs event generated valid started release occurrence node
  dsimp only
  intro found stored pending changed owner contributes group viewLive
  let before := ((State.initialize work).runNormalized inputs).1.queue
  let snapshot := registrationSnapshot before event
  let events := (before.handleGraphEvent event).2
  obtain ⟨_, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  have frame := GeneratedSnapshotTaskEvidence_holds work inputs event generated valid priorStarted
  obtain ⟨parents, forest, _⟩ := generatedSnapshot_removalForest generated valid priorStarted
  have dispatch := generatedReplay_dispatchProjection generated valid started
  change SnapshotTaskEvidence snapshot work at frame
  change snapshot.RemovalForest parents at forest
  change snapshot.taskNode? occurrence = some node at found
  obtain ⟨task, catalogue, sameGroups⟩ := generatedSnapshot_taskCatalogue generated valid priorStarted found
  have unpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
      key ∉ publicationRoots events := by
    intro key member
    obtain ⟨contributor, listed, same⟩ := List.mem_map.mp member
    exact same ▸ pruningPending_unpublished catalogue pending (sameGroups.symm ▸ listed)
  have present : owner.ref ∈ snapshot.groupNodes.map (fun group => group.group.node.ref) :=
    viewOwner_present viewLive
  cases event with
  | taskSuccess incoming result =>
      cases inputFound : before.taskNode? incoming with
      | none =>
          have unchanged : snapshot = before := by simp [snapshot, registrationSnapshot, inputFound]
          have next : (before.handleGraphEvent (.taskSuccess incoming result)).1 = before := by
            simp [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.taskSuccess, inputFound]
          rw [unchanged] at found
          exact False.elim (changed (by rw [next]; exact found))
      | some incomingNode =>
          let native : State := { queue := before }
          let nativeStored : State :=
            { native with queue := native.queue.putTaskNode { incomingNode with value := some result.value } }
          let registered := nativeStored.maybeIntegrateWork result.work (some incoming)
          let folded := incomingNode.task.groups.foldl ReferenceWorkQueue.successGroupStep
            (snapshot, [], {})
          let starting : State := { registered.1 with queue := folded.1 }
          let initial := (starting.startNewWork folded.2.2 registered.2).1.queue
          have prepared : snapshot = registered.1.queue := by
            simp only [snapshot, registrationSnapshot, inputFound]
            rfl
          have handler : before.handleGraphEvent (.taskSuccess incoming result)
              = (initial.drainReadyGroups.1, folded.2.1 ++ initial.drainReadyGroups.2) := by
            let active := starting.startNewWork folded.2.2 registered.2
            have raw : before = (ReferenceWorkQueue.State.initialize
                (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten :=
              (generatedReplay_beforeNext generated valid started).1
            have accepted := (generatedReplay_beforeNext generated valid started).2.2
            have sourceFound : ReferenceWorkQueue.State.taskNode?
                ((ReferenceWorkQueue.State.initialize
                  (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents inputs.flatten)
                incoming = some incomingNode := by rw [← raw]; exact inputFound
            have phase : active.1.queue = referenceTaskSuccessReady before incoming result incomingNode := by
              have actual : active.1.queue = (taskSuccessReadyPhase native incoming result incomingNode).1.queue := by
                simp only [taskSuccessReadyPhase]
                rw [← prepared]
              rw [actual]
              change (taskSuccessReadyPhase { queue := before } incoming result incomingNode).1.queue = _
              rw [raw]
              exact referencePrefix_taskSuccess_readyProjection generated inputs.flatten
                incoming result valid accepted incomingNode sourceFound
            obtain ⟨readyParents, readyFrame, readyForest⟩ := referencePrefix_taskSuccess_drainFrames
              generated inputs.flatten incoming result valid accepted incomingNode sourceFound
            rw [← raw] at readyFrame readyForest
            have actualFrame : active.1.queue.TaskOwnerFrame work := by rw [phase]; exact readyFrame
            have actualForest : active.1.queue.RemovalForest readyParents := by rw [phase]; exact readyForest
            have running : active.1.stopped = false :=
              (State.startNewWork_stopped starting folded.2.2 registered.2 []).trans
                (nativeStored.maybeIntegrateWork_stopped result.work (some incoming))
            have drain := active.1.drainReadyGroups_projection running actualFrame actualForest active.2
            rw [← dispatch]
            rw [generatedReplay_beforeNextState generated valid started]
            change ((native.taskSuccess incoming result).1.queue,
              (native.taskSuccess incoming result).2.1) = _
            rw [State.taskSuccess_eq native incoming result incomingNode inputFound]
            dsimp only
            rw [← prepared]
            exact congrArg (fun pair => (pair.1, folded.2.1 ++ pair.2)) drain
          have outputs : events = folded.2.1 ++ initial.drainReadyGroups.2 :=
            congrArg Prod.snd handler
          have foldUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∉ publicationRoots folded.2.1 := by
            intro key listed published
            apply unpublished key listed
            rw [outputs, publicationRoots, List.filterMap_append]
            exact List.mem_append_left _ published
          obtain ⟨foldFrame, foldForest, foldEdges, foldClosures⟩ :=
            successGroupFold_releaseEvidence frame forest incomingNode.task.groups
          obtain ⟨foldFound, foldOwners⟩ := successGroupFold_pendingBuffer_retained frame
            incomingNode.task.groups found stored foldUnpublished
          have initialFound : initial.taskNode? occurrence = some node :=
            State.startNewWork_lookup_existing (state := starting) foldFound _ _
          have initialPresent : owner.ref ∈ initial.groupNodes.map (fun group => group.group.node.ref) := by
            rw [State.startNewWork_groupNodes]
            exact foldOwners _ (List.mem_map.mpr ⟨owner, contributes, rfl⟩) present
          have initialEdges : initial.GroupEdgesFrom snapshot := by
            intro key candidate lookup
            rw [ReferenceWorkQueue.State.groupNode?,
              State.startNewWork_groupNodes] at lookup
            exact foldEdges key candidate lookup
          have initialClosures := foldClosures.post
            (fun _ retired => retiredGroup_startAlternative (state := starting) retired
              folded.2.2 registered.2)
          have drainUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∉ publicationRoots (folded.2.1 ++ initial.drainReadyGroups.2) := by
            rwa [← outputs]
          have tracked := drain_pendingBuffer_ownerCut
            (foldFrame.startAlternative (state := starting) _ _)
            (removalForest_startAlternative (state := starting) foldForest _ _)
            initialEdges initialClosures initial.groupNodes.length initialFound stored
            drainUnpublished contributes initialPresent
          rcases tracked with kept | cut
          · change (before.handleGraphEvent (.taskSuccess incoming result)).1.taskNode? occurrence ≠ some node at changed
            rw [handler] at changed
            change initial.drainReadyGroups.1.taskNode? occurrence = some node ∧ _ at kept
            exact False.elim (changed kept.1)
          · obtain ⟨root, failed, path⟩ := cut
            refine ⟨root, ?_, ?_⟩
            · change root ∈ failureRoots events
              rw [outputs, failureRoots, List.filterMap_append]
              exact List.mem_append_right _ failed
            · change (failurePruningView before (.taskSuccess incoming result)
                (folded.2.1 ++ initial.drainReadyGroups.2)).LiveDescendant root owner.ref at path
              rwa [← outputs] at path
  | streamItems stream items =>
      cases active : before.rootStreams.contains stream.ref with
      | false =>
          have unchanged : snapshot = before := by
            simp only [snapshot, registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte]
          have next : (before.handleGraphEvent (.streamItems stream items)).1 = before := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent, ReferenceWorkQueue.State.streamItems,
              active, Bool.not_false, ↓reduceIte]
          rw [unchanged] at found
          exact False.elim (changed (by rw [next]; exact found))
      | true =>
          let prepared := items.foldl ReferenceWorkQueue.streamItemStep (before, [], [], [])
          let notice := WorkQueueEvent.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1
          have projection := generatedSnapshot_projection generated valid priorStarted
          have same : snapshot = prepared.1 :=
            registrationSnapshot_streamItems before stream items projection active
          have handler : before.handleGraphEvent (.streamItems stream items)
              = (snapshot.drainReadyGroups.1, notice :: snapshot.drainReadyGroups.2) := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              before.streamItems_eq stream items, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            rw [← same]
          have outputs : events = notice :: snapshot.drainReadyGroups.2 := congrArg Prod.snd handler
          have closures : ReferenceWorkQueue.GroupClosureAccounting snapshot (snapshot, [notice]) := by
            refine ⟨?_, ?_, fun _ retired => retired, ?_⟩
            · simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
            · simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
            · simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
          have drainUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∉ publicationRoots ([notice] ++ snapshot.drainReadyGroups.2) := by
            simpa only [List.singleton_append, ← outputs] using unpublished
          have tracked := drain_pendingBuffer_ownerCut frame forest (.refl snapshot) closures
            snapshot.groupNodes.length found stored drainUnpublished contributes present
          rcases tracked with kept | cut
          · change (before.handleGraphEvent (.streamItems stream items)).1.taskNode? occurrence ≠ some node at changed
            rw [handler] at changed
            change snapshot.drainReadyGroups.1.taskNode? occurrence = some node ∧ _ at kept
            exact False.elim (changed kept.1)
          · obtain ⟨root, failed, path⟩ := cut
            refine ⟨root, ?_, ?_⟩
            · change root ∈ failureRoots events
              simpa only [outputs, failureRoots, notice, List.filterMap_cons,
                ReferenceWorkQueue.State.drainReadyGroups] using failed
            · change (failurePruningView before (.streamItems stream items)
                ([notice] ++ snapshot.drainReadyGroups.2)).LiveDescendant root owner.ref at path
              simpa only [List.singleton_append, ← outputs] using path
  | taskFailure | streamSuccess | streamFailure => cases release

/-- Disappearance is a special case of the exact prepared-record loss construction. -/
theorem GeneratedPendingBufferFailureCut_holds : GeneratedPendingBufferFailureCut :=
  GeneratedPendingBufferFailureCut_of_lossCut GeneratedPendingBufferLossCut_holds

/-- Every dropped, initially owned prepared source is activated or actually requested by
its generated success/item dispatch, with the same legal completion/cleanup observation.
This supplies the generated cut internally; it is not an additional source law.
-/
theorem GeneratedReleaseFailureDisposal_holds : GeneratedReleaseFailureDisposal := by
  intro work inputs event generated valid started release resources
  have strong := GeneratedStoredReleaseDisposal_holds work inputs event generated valid started release resources
  refine ⟨strong.1, ?_⟩
  intro occurrence node key found stored _owned held dropped
  exact strong.2 occurrence node key found stored held dropped

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
