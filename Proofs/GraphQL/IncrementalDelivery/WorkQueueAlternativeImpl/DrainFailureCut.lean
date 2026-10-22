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
            if (queue.rejectedTask? group).isSome || group.pending == 0 then
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
        cases cached : current.rejectedTask? group with
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
        | some rejection =>
            obtain ⟨failed, errors⟩ := rejection
            simp only [cached] at unpublished
            dsimp only at unpublished ⊢
            let next := (current.taskFailure failed errors).1
            rcases taskFailure_ownerCut failed errors fuel forest frame.keys edges closures present with
              nextPresent | cut
            · obtain ⟨oldOwner, lookup⟩ := liveLookup nextPresent
              have unchanged : occurrence ≠ failed ∨ node.rejection = some errors := by
                by_cases different : occurrence ≠ failed
                · exact .inl different
                · have same : occurrence = failed := Classical.not_not.mp different
                  subst failed
                  obtain ⟨_, source, selected, rejected⟩ :=
                    ReferenceWorkQueue.State.rejectedTask?_sound cached
                  have equal : source = node := Option.some.inj (selected.symm.trans found)
                  exact .inr (equal ▸ rejected)
              have nextFound := ReferenceWorkQueue.State.taskFailure_lookup_survivingOwner_unchanged
                found failed errors unchanged contributes (List.mem_of_find?_eq_some lookup)
                  (ReferenceWorkQueue.State.groupNode?_ref lookup)
              have nextEdges := (current.taskFailure_groupEdgesFrom failed errors).trans edges
              have nextClosures := closures.append
                (ReferenceWorkQueue.State.taskFailure_closureAccounting frame.live failed errors)
              have nextUnpublished : ∀ key ∈ node.task.groups.map DeliveryNode.ref,
                  key ∉ publicationRoots
                    ((preceding ++ (current.taskFailure failed errors).2)
                      ++ (ReferenceWorkQueue.State.drainReadyGroups.go fuel next).2) := by
                simpa only [List.append_assoc] using unpublished
              rcases ih (frame.taskFailure failed errors) (forest.taskFailure failed errors)
                  nextEdges nextClosures nextFound nextUnpublished nextPresent with kept | cut
              · exact .inl kept
              · obtain ⟨root, reported, path⟩ := cut
                refine .inr ⟨root, ?_, ?_⟩
                · rw [failureRoots, List.filterMap_append]
                  exact List.mem_append_right _ reported
                · simpa only [List.append_assoc] using path
            · obtain ⟨root, reported, path⟩ := cut
              refine .inr ⟨root, ?_, ?_⟩
              · rw [failureRoots, List.filterMap_append]
                exact List.mem_append_left _ reported
              · simpa only [List.append_assoc] using path

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
