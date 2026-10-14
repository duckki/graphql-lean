import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePathTransport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SuccessfulBufferRetention

/-! Construct pending-buffer owner cuts along the actual bounded mixed drain. Each owner
is either retained with the exact buffer or covered by a failure emitted in that drain.
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
            if group.failure.isSome || group.pending == 0 then some group else none)
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

/-- Every live owner of a pending buffer survives a bounded drain with that exact buffer,
or has a path below a failure actually emitted in that drain. The path belongs to the
full handler's publication-filtered snapshot view, including preceding successful output.
No failure cut, resource inventory, or final-state cancellation premise is supplied.
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
                ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel current).2))
    {owner : DeliveryNode} (contributes : owner ∈ node.task.groups)
    (present : owner.ref ∈ current.groupNodes.map (fun group => group.group.node.ref))
    : let drained := ReferenceWorkQueue.State.drainReadyGroups.go fuel current
      (drained.1.taskNode? occurrence = some node
        ∧ owner.ref ∈ drained.1.groupNodes.map (fun group => group.group.node.ref))
      ∨ ∃ root ∈ failureRoots drained.2,
          (failurePruningView before event (preceding ++ drained.2)).LiveDescendant
            root owner.ref := by
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
        cases cached : group.failure with
        | none =>
            simp only [cached] at unpublished
            dsimp only at unpublished ⊢
            let released := current.finishGroupSuccess group
            let next := released.1.startNewWork released.2.2
            have noncontributor : group.group.node.ref ∉ node.task.groups.map DeliveryNode.ref := by
              intro contributesKey
              apply unpublished _ contributesKey
              rw [publicationRoots, List.filterMap_append, List.filterMap_append]
              exact List.mem_append_right _ (List.mem_append_left _ (flushKey current group))
            obtain ⟨retained, owners⟩ := successfulFlush_noncontributorBuffer frame group member
              found stored noncontributor
            have nextFound : next.taskNode? occurrence = some node :=
              ReferenceWorkQueue.State.startNewWork_lookup_existing retained _
            have nextPresent : owner.ref ∈ next.groupNodes.map (fun group => group.group.node.ref) := by
              rw [(ReferenceWorkQueue.State.startNewWork_groupCore _ _).1]
              exact owners _ (List.mem_map.mpr ⟨owner, contributes, rfl⟩) present
            have nextFrame := (frame.finishGroupSuccess group).startNewWork released.2.2
            have nextForest := (forest.finishGroupSuccess group).startNewWork released.2.2
            have nextEdges : next.GroupEdgesFrom (registrationSnapshot before event) := by
              apply ReferenceWorkQueue.State.GroupEdgesFrom.trans _ edges
              intro key candidate lookup
              rw [ReferenceWorkQueue.State.groupNode?,
                (ReferenceWorkQueue.State.startNewWork_groupCore _ _).1] at lookup
              exact (current.finishGroupSuccess_descendants group).1 key candidate lookup
            have nextClosures := closures.append
              ((ReferenceWorkQueue.State.finishGroupSuccess_closureAccounting frame.live group
                member).post (fun _ retired => retired.startNewWork released.2.2))
            have nextUnpublished
                : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
                    key ∉ publicationRoots
                      ((preceding ++ released.2.1)
                        ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel next).2) := by
              simpa only [List.append_assoc] using unpublished
            rcases ih nextFrame nextForest nextEdges nextClosures nextFound nextUnpublished
                nextPresent with kept | cut
            · exact Or.inl kept
            · obtain ⟨root, failed, path⟩ := cut
              refine Or.inr ⟨root, ?_, ?_⟩
              · rw [failureRoots, List.filterMap_append]
                exact List.mem_append_right _ failed
              · simpa only [List.append_assoc] using path
        | some errors =>
            simp only [cached] at unpublished
            dsimp only [ReferenceWorkQueue.State.finishGroupFailure] at unpublished ⊢
            by_cases affected : current.LiveDescendant group.group.node.ref owner.ref
            · refine Or.inr ⟨group.group.node.ref, ?_, ?_⟩
              · simp [failureRoots]
              · have retired : ∀ key ∈ publicationRoots preceding, current.groupNode? key = none := by
                  intro key published
                  obtain ⟨carrier, groups, streams, emitted, same⟩ := mem_publicationRoots.mp published
                  exact (closures.closed key
                    (List.mem_flatMap.mpr ⟨_, emitted, same ▸ List.mem_cons_self⟩)).lookup_none
                simpa only [List.append_assoc]
                  using failureBoundary_path group.group.node errors fuel forest edges
                    retired affected
            · let next := current.removeGroup group.group.node.ref
              obtain ⟨oldOwner, lookup⟩ := liveLookup present
              have nextLookup : next.groupNode? owner.ref = some oldOwner :=
                (ReferenceWorkQueue.State.removeGroup_groupNodeRetained forest affected).trans lookup
              have nextFound := ReferenceWorkQueue.State.removeGroup_lookup_survivingOwner found
                group.group.node.ref contributes (List.mem_of_find?_eq_some nextLookup)
                (ReferenceWorkQueue.State.groupNode?_ref nextLookup)
              have nextPresent : owner.ref ∈ next.groupNodes.map (fun group => group.group.node.ref) :=
                List.mem_map.mpr ⟨oldOwner, List.mem_of_find?_eq_some nextLookup,
                  ReferenceWorkQueue.State.groupNode?_ref nextLookup⟩
              have nextEdges : next.GroupEdgesFrom (registrationSnapshot before event) := by
                apply ReferenceWorkQueue.State.GroupEdgesFrom.trans _ edges
                exact current.filterRefs_groupEdgesFrom
                  (fun key => !(ReferenceWorkQueue.State.removeGroup.collect
                    (current.groupNodes.length + 1) current [group.group.node.ref] []).contains key)
              have nextClosures := closures.append
                (ReferenceWorkQueue.State.finishGroupFailure_closureAccounting frame.live group
                  member errors)
              have nextUnpublished
                  : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
                      key ∉ publicationRoots
                        ((preceding ++ [.groupFailure group.group.node errors])
                          ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel next).2) := by
                simpa only [ReferenceWorkQueue.State.finishGroupFailure,
                  List.append_assoc]
                  using unpublished
              rcases ih (frame.removeGroup _) (forest.removeGroup _) nextEdges nextClosures
                  nextFound nextUnpublished nextPresent with kept | cut
              · exact Or.inl kept
              · obtain ⟨root, failed, path⟩ := cut
                refine Or.inr ⟨root, ?_, ?_⟩
                · simp only [failureRoots, List.filterMap_append, List.filterMap_cons,
                    List.filterMap_nil, List.mem_append]
                  exact Or.inr failed
                · simpa only [ReferenceWorkQueue.State.finishGroupFailure,
                    List.append_assoc]
                    using path

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
