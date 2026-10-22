import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StartupFailurePath
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePathTransport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulBufferRetention

/-! Construct pending-buffer owner cuts along successful draining and cached startup.
Each owner retains its exact buffer or lies below a queued startup failure.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode GroupNode)
open GraphQL.IncrementalDelivery.Execution (DeliveryNode WorkQueueEvent)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Local lookup and output facts used by the actual drain induction
-----------------------------------------------------------------------------------------

private theorem liveLookup {queue : Kernel} {key : Nat}
    (present : key ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    : ∃ group, queue.groupNode? key = some group := by
  cases found : queue.groupNode? key with
  | some group => exact ⟨group, rfl⟩
  | none =>
      obtain ⟨group, member, same⟩ := List.mem_map.mp present
      have excluded := List.find?_eq_none.mp found group member
      simp [same] at excluded

private theorem readyMember {queue : Kernel} {node : GroupNode}
    (selected
      : queue.rootGroups.findSome?
          (fun key => do
            let group ← queue.groupNode? key
            if group.pending == 0 then
              some group
            else
              none)
        = some node)
    : node ∈ queue.groupNodes := by
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some candidate =>
      simp only [found] at choice
      change (if _ then some candidate else none) = some node at choice
      split at choice
      · cases Option.some.inj choice
        exact List.mem_of_find?_eq_some found
      · contradiction

private theorem flushKey (queue : Kernel) (node : GroupNode)
    : node.group.node.ref ∈ publicationRoots (queue.finishGroupSuccess node).2.1 := by
  obtain ⟨selected, _, _, output, _, _⟩ := queue.finishGroupSuccess_publications node
  rw [output]
  split <;> simp [publicationRoots]

-----------------------------------------------------------------------------------------
-- Track each contributor through success, shared retention, and actual failure
-----------------------------------------------------------------------------------------

/-- A live owner of an unpublished buffer either survives successful draining with its
exact buffer, or lies below a queued startup failure. The failure path uses the complete
handler's publication-filtered view. No runtime cause cache or desired cleanup is assumed.
-/
theorem drain_pendingBuffer_ownerCut {before current : Kernel}
    {work event parents preceding occurrence node}
    (frame : SnapshotTaskEvidence current work)
    (forest : current.RemovalForest parents)
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (closures
      : ReferenceWorkQueue.GroupClosureAccounting
          (registrationSnapshot before event) (current, preceding))
    (fuel : Nat) (found : current.taskNode? occurrence = some node)
    (stored : node.value.isSome = true)
    (unpublished
      : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
          key
          ∉ publicationRoots
              (preceding
                ++ (ReferenceWorkQueue.State.drainReadyGroups.go [] fuel current).2.1))
    {owner : DeliveryNode} (contributes : owner ∈ node.task.groups)
    (present : owner.ref ∈ current.groupNodes.map (fun group => group.group.node.ref))
    : let drained := ReferenceWorkQueue.State.drainReadyGroups.go [] fuel current
      (drained.1.taskNode? occurrence = some node
        ∧ owner.ref ∈ drained.1.groupNodes.map (fun group => group.group.node.ref))
      ∨ ∃ failure ∈ drained.2.2,
          (failurePruningView before event (preceding ++ drained.2.1)).LiveDescendant
            failure.group.ref owner.ref := by
  induction fuel generalizing current preceding with
  | zero => exact Or.inl ⟨found, present⟩
  | succ fuel ih =>
      unfold ReferenceWorkQueue.State.drainReadyGroups.go at unpublished ⊢
      dsimp only at unpublished ⊢
      split
      · exact Or.inl ⟨found, present⟩
      · rename_i group selected
        simp only [selected] at unpublished
        have member := readyMember selected
        let released := current.finishGroupSuccess group
        let startup := released.1.startNewWork released.2.2
        let next := startup.1
        have noncontributor : group.group.node.ref ∉ node.task.groups.map DeliveryNode.ref := by
          intro contributesKey
          apply unpublished _ contributesKey
          rw [publicationRoots, List.filterMap_append, List.filterMap_append]
          exact List.mem_append_right _ (List.mem_append_left _ (flushKey current group))
        obtain ⟨retained, owners⟩ := successfulFlush_noncontributorBuffer frame group member
          found stored noncontributor
        have afterClosures := closures.append
          (ReferenceWorkQueue.State.finishGroupSuccess_closureAccounting frame.live group member)
        have afterEdges := ((current.finishGroupSuccess_descendants group).1).trans edges
        have afterForest := forest.finishGroupSuccess group
        have ownerPresent := owners _ (List.mem_map.mpr ⟨owner, contributes, rfl⟩) present
        rcases ReferenceWorkQueue.State.startNewWork_ownerCut (key := owner.ref)
            afterForest released.2.2
            (by obtain ⟨kept, live, same⟩ := List.mem_map.mp ownerPresent
                exact ⟨kept, by
                  rw [← same]
                  exact (frame.keys.finishGroupSuccess group).groupNode?_of_mem live⟩)
            with kept | cut
        · obtain ⟨keptOwner, ownerLookup⟩ := kept
          have nextFound : next.taskNode? occurrence = some node :=
            ReferenceWorkQueue.State.startNewWork_lookup_existing retained released.2.2 []
              (by intro errors impossible; cases impossible) contributes
              (List.mem_of_find?_eq_some ownerLookup)
              (ReferenceWorkQueue.State.groupNode?_ref ownerLookup)
          have nextPresent : owner.ref ∈ next.groupNodes.map (fun group => group.group.node.ref) :=
            List.mem_map.mpr ⟨keptOwner, List.mem_of_find?_eq_some ownerLookup,
              ReferenceWorkQueue.State.groupNode?_ref ownerLookup⟩
          have nextFrame := (frame.finishGroupSuccess group).startNewWork released.2.2
          have nextForest := afterForest.startNewWork released.2.2
          have nextEdges := (ReferenceWorkQueue.State.startNewWork_groupEdgesFrom
            released.1 released.2.2).trans afterEdges
          have nextClosures := afterClosures.post
            (fun _ retired => retired.startNewWork released.2.2)
          have nextUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
              key ∉ publicationRoots ((preceding ++ released.2.1)
                ++ (ReferenceWorkQueue.State.drainReadyGroups.go [] fuel next).2.1) := by
            simpa only [List.append_assoc] using unpublished
          rcases ih nextFrame nextForest nextEdges nextClosures nextFound nextUnpublished
              nextPresent with retained | cut
          · exact .inl retained
          · obtain ⟨failure, queued, path⟩ := cut
            exact .inr ⟨failure, List.mem_append_right _ queued,
              by simpa only [List.append_assoc] using path⟩
        · obtain ⟨failure, queued, path⟩ := cut
          refine .inr ⟨failure, List.mem_append_left _ queued, ?_⟩
          simpa only [List.append_assoc] using startupFailureBoundary_path released.2.2 afterForest
            afterEdges afterClosures fuel queued path

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
