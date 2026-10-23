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
  let eager := eagerRegistrationSnapshot before event
  let events := (before.handleGraphEvent event).2.1
  obtain ⟨_, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  have projection := generatedSnapshot_projection generated valid priorStarted
  have frame := generatedEagerSnapshot_taskEvidence generated valid priorStarted
  obtain ⟨parents, forest, _⟩ := generatedSnapshot_removalForest generated valid priorStarted
  change SnapshotTaskEvidence eager work at frame
  change snapshot.RemovalForest parents at forest
  change snapshot.taskNode? occurrence = some node at found
  have eagerFound : eager.taskNode? occurrence = some node := projection.lookup _ _ found
  have groups := congrArg ReferenceWorkQueue.State.groupNodes projection.core
  change snapshot.groupNodes = eager.groupNodes at groups
  have registry := congrArg ReferenceWorkQueue.State.registeredGroups projection.core
  change snapshot.registeredGroups = eager.registeredGroups at registry
  have eagerForest : eager.RemovalForest parents :=
    forest.of_subset (by rw [← groups]; exact List.Subset.refl _)
  have eagerEdges : eager.GroupEdgesFrom snapshot := by
    intro key candidate lookup
    exact ⟨candidate, by simpa only [ReferenceWorkQueue.State.groupNode?, groups] using lookup, rfl⟩
  have eagerClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot (eager, []) :=
    .silent
      (fun _ retired => by
        simpa only [ReferenceWorkQueue.State.RetiredGroup, groups, registry]
          using retired)
  obtain ⟨task, catalogue, sameGroups⟩ :=
    generatedSnapshot_taskCatalogue generated valid priorStarted found
  have unpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
      key ∉ publicationRoots events := by
    intro key member
    obtain ⟨contributor, listed, same⟩ := List.mem_map.mp member
    exact same ▸ pruningPending_unpublished catalogue pending (sameGroups.symm ▸ listed)
  have present : owner.ref ∈ eager.groupNodes.map (fun group => group.group.node.ref) := by
    rw [← groups]
    exact viewOwner_present viewLive
  cases event with
  | taskSuccess incoming result =>
      cases inputFound : before.taskNode? incoming with
      | none =>
          have unchanged : snapshot = before := by simp [snapshot, registrationSnapshot, inputFound]
          have next : (before.handleGraphEvent (.taskSuccess incoming result)).1 = before := by
            simp [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures,
              ReferenceWorkQueue.State.taskSuccess, inputFound]
          rw [unchanged] at found
          exact False.elim (changed (by rw [next]; exact found))
      | some input =>
          let folded := input.task.groups.foldl ReferenceWorkQueue.successGroupStep (eager, [], {})
          let startup := folded.1.startNewWork folded.2.2
          let drained := startup.1.drainReadyGroups
          have handler : before.handleGraphEvent (.taskSuccess incoming result)
              = (drained.1, folded.2.1 ++ drained.2.1, startup.2 ++ drained.2.2) := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil]
            rw [ReferenceWorkQueue.State.taskSuccess_eq incoming result input inputFound]
            simp only [folded, startup, drained, eager, eagerRegistrationSnapshot, inputFound]
          have outputs : events = folded.2.1 ++ drained.2.1 := congrArg (fun r => r.2.1) handler
          have foldUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∉ publicationRoots folded.2.1 := by
            intro key listed published
            apply unpublished key listed
            rw [outputs, publicationRoots, List.filterMap_append]
            exact List.mem_append_left _ published
          obtain ⟨foldFrame, foldForest, foldEdges, foldClosures⟩ :=
            successGroupFold_releaseEvidence frame eagerForest input.task.groups
          obtain ⟨foldFound, foldOwners⟩ := successGroupFold_pendingBuffer_retained frame
            input.task.groups eagerFound stored foldUnpublished
          have foldPresent := foldOwners _ (List.mem_map.mpr ⟨owner, contributes, rfl⟩) present
          have foldLookup : ∃ old, folded.1.groupNode? owner.ref = some old := by
            obtain ⟨old, member, same⟩ := List.mem_map.mp foldPresent
            exact ⟨old, same ▸ foldFrame.keys.groupNode?_of_mem member⟩
          have actualEdges := foldEdges.trans eagerEdges
          have actualClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot
              (folded.1, folded.2.1) := by
            simpa only [List.nil_append] using eagerClosures.append foldClosures
          rcases ReferenceWorkQueue.State.startNewWork_ownerCut foldForest folded.2.2
              foldLookup with kept | cut
          · obtain ⟨keptOwner, ownerLookup⟩ := kept
            have initialFound : startup.1.taskNode? occurrence = some node :=
              ReferenceWorkQueue.State.startNewWork_lookup_existing foldFound folded.2.2 []
                (by intro errors impossible; cases impossible) contributes
                (List.mem_of_find?_eq_some ownerLookup)
                (ReferenceWorkQueue.State.groupNode?_ref ownerLookup)
            have initialPresent : owner.ref ∈ startup.1.groupNodes.map
                (fun group => group.group.node.ref) :=
              List.mem_map.mpr ⟨keptOwner, List.mem_of_find?_eq_some ownerLookup,
                ReferenceWorkQueue.State.groupNode?_ref ownerLookup⟩
            have initialEdges := (ReferenceWorkQueue.State.startNewWork_groupEdgesFrom
              folded.1 folded.2.2).trans actualEdges
            have initialClosures := actualClosures.post
              (fun _ retired => retired.startNewWork folded.2.2)
            have drainUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
                key ∉ publicationRoots (folded.2.1 ++ drained.2.1) := by rwa [← outputs]
            rcases drain_pendingBuffer_ownerCut (foldFrame.startNewWork folded.2.2)
                (foldForest.startNewWork folded.2.2) initialEdges initialClosures
                startup.1.groupNodes.length initialFound stored drainUnpublished contributes
                initialPresent with retained | cut
            · exact False.elim (changed (by rw [handler]; exact retained.1))
            · obtain ⟨failure, queued, path⟩ := cut
              refine ⟨failure.group.ref, ?_, ?_⟩
              · rw [handler]
                apply List.mem_append_right
                rw [List.map_append]
                exact List.mem_append_right _ (List.mem_map_of_mem queued)
              · change (failurePruningView before (.taskSuccess incoming result)
                  events).LiveDescendant failure.group.ref owner.ref
                rw [outputs]
                exact path
          · obtain ⟨failure, queued, path⟩ := cut
            refine ⟨failure.group.ref, ?_, ?_⟩
            · rw [handler]
              apply List.mem_append_right
              rw [List.map_append]
              exact List.mem_append_left _ (List.mem_map_of_mem queued)
            · have transported := startupFailureBoundary_path folded.2.2 foldForest
                actualEdges actualClosures startup.1.groupNodes.length queued path
              change (failurePruningView before (.taskSuccess incoming result)
                events).LiveDescendant failure.group.ref owner.ref
              rw [outputs]
              exact transported
  | streamItems stream items =>
      cases active : before.rootStreams.contains stream.ref with
      | false =>
          have unchanged : snapshot = before := by
            simp only [snapshot, registrationSnapshot, active, Bool.false_eq_true, ↓reduceIte]
          have next : (before.handleGraphEvent (.streamItems stream items)).1 = before := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
              ReferenceWorkQueue.State.streamItems, active, Bool.not_false, ↓reduceIte]
          rw [unchanged] at found
          exact False.elim (changed (by rw [next]; exact found))
      | true =>
          let prepared := items.foldl ReferenceWorkQueue.streamItemStep (before, [], [], [], [])
          let notice := WorkQueueEvent.streamValues stream prepared.2.2.2.1 prepared.2.1
            prepared.2.2.1
          have same : eager = prepared.1 := by
            simp only [eager, eagerRegistrationSnapshot, active, ↓reduceIte]
            rfl
          have handler : before.handleGraphEvent (.streamItems stream items)
              = (eager.drainReadyGroups.1, notice :: eager.drainReadyGroups.2.1,
                  prepared.2.2.2.2 ++ eager.drainReadyGroups.2.2) := by
            simp only [ReferenceWorkQueue.State.handleGraphEvent,
              ReferenceWorkQueue.State.cacheTaskFailures, List.foldl_nil,
              before.streamItems_eq stream items, active, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte]
            rw [← same]
          have outputs : events = notice :: eager.drainReadyGroups.2.1 :=
            congrArg (fun r => r.2.1) handler
          have closures : ReferenceWorkQueue.GroupClosureAccounting eager (eager, [notice]) := by
            refine ⟨?_, ?_, fun _ retired => retired, ?_⟩ <;>
              simp [notice, ReferenceWorkQueue.rawGroupClosureRefs]
          have actualClosures : ReferenceWorkQueue.GroupClosureAccounting snapshot
              (eager, [notice]) := by
            simpa only [List.nil_append] using eagerClosures.append closures
          have drainUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∉ publicationRoots ([notice] ++ eager.drainReadyGroups.2.1) := by
            simpa only [List.singleton_append, ← outputs] using unpublished
          rcases drain_pendingBuffer_ownerCut frame eagerForest eagerEdges actualClosures
              eager.groupNodes.length eagerFound stored drainUnpublished contributes present with
              kept | cut
          · exact False.elim (changed (by rw [handler]; exact kept.1))
          · obtain ⟨failure, queued, path⟩ := cut
            refine ⟨failure.group.ref, ?_, ?_⟩
            · rw [handler]
              apply List.mem_append_right
              rw [List.map_append]
              exact List.mem_append_right _ (List.mem_map_of_mem queued)
            · change (failurePruningView before (.streamItems stream items)
                events).LiveDescendant failure.group.ref owner.ref
              rw [outputs]
              exact path
  | taskFailure | groupFailure | streamSuccess | streamFailure => cases release

/-- Disappearance is a special case of the exact prepared-record loss construction. -/
theorem GeneratedPendingBufferFailureCut_holds : GeneratedPendingBufferFailureCut :=
  GeneratedPendingBufferFailureCut_of_lossCut GeneratedPendingBufferLossCut_holds

/-- Every dropped, initially owned prepared source is activated or actually requested by
its generated success/item dispatch, with the same legal completion/cleanup observation.
This supplies the generated cut internally; it is not an additional source law.
-/
theorem GeneratedReleaseFailureDisposal_holds : GeneratedReleaseFailureDisposal := by
  intro work inputs event generated valid started release resources
  have strong := GeneratedStoredReleaseDisposal_holds work inputs event generated valid started
    release resources
  refine ⟨strong.1, ?_⟩
  intro occurrence node key found stored _owned held dropped
  exact strong.2 occurrence node key found stored held dropped

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
