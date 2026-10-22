import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePathTransport

/-! Every live owner of an unsettled task survives the actual mixed drain or lies below
a failure emitted by that drain. This covers unstarted tasks, without a buffered-value
premise, a cleanup conclusion, or a stronger event-source contract.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence NodeRefs)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (GroupNode)

private abbrev Kernel := ReferenceWorkQueue.State

private theorem liveLookup {queue : Kernel} {key : Nat}
    (present : key ∈ queue.groupNodes.map (fun group => group.group.node.ref))
    : ∃ group, queue.groupNode? key = some group := by
  cases found : queue.groupNode? key with
  | some group => exact ⟨group, rfl⟩
  | none =>
      obtain ⟨group, member, same⟩ := List.mem_map.mp present
      have excluded := List.find?_eq_none.mp found group member
      simp [same] at excluded

private theorem readyFacts {queue : Kernel} {node : GroupNode}
    (selected
      : queue.rootGroups.findSome?
          (fun key => do
            let group ← queue.groupNode? key
            if (queue.rejectedTask? group).isSome || group.pending == 0 then
              some group
            else
              none)
        = some node)
    : node ∈ queue.groupNodes ∧ (queue.rejectedTask? node = none → node.pending = 0) := by
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some candidate =>
      simp only [found] at choice
      change (if _ then some candidate else none) = some node at choice
      split at choice
      · rename_i ready
        cases Option.some.inj choice
        refine ⟨List.mem_of_find?_eq_some found, ?_⟩
        intro healthy
        simpa only [healthy, Option.isSome_none, Bool.false_or, beq_iff_eq] using ready
      · contradiction

-----------------------------------------------------------------------------------------
-- The actual drain constructs retention or a chronological emitted failure path
-----------------------------------------------------------------------------------------

/-- Each initially live contributing owner of an unsettled linked task is retained or
covered by an actual failure in the full handler's publication-filtered view. Counter
accounting rules out successful selection; links rule out silent empty-shell retirement.
No task computation node, stored value, or assumed owner-loss cut is needed.
-/
theorem drain_unsettledTask_ownerCut {before current : Kernel}
    {work event parents preceding occurrence keys settled key}
    (frame : SnapshotTaskEvidence current work) (forest : current.RemovalForest parents)
    (edges : current.GroupEdgesFrom (registrationSnapshot before event))
    (closures
      : ReferenceWorkQueue.GroupClosureAccounting
          (registrationSnapshot before event) (current, preceding))
    (links : current.TaskLinkedOn occurrence keys)
    (bounded : current.PendingBound (fun _ => True) settled)
    (fresh : occurrence ∉ settled) (fuel : Nat) (contributes : key ∈ keys)
    (present : key ∈ current.groupNodes.map (fun group => group.group.node.ref))
    : let drained := ReferenceWorkQueue.State.drainReadyGroups.go fuel current
      key ∈ drained.1.groupNodes.map (fun group => group.group.node.ref)
      ∨ ∃ root ∈ failureRoots drained.2,
          (failurePruningView before event (preceding ++ drained.2)).LiveDescendant root
            key := by
  induction fuel generalizing current preceding with
  | zero => exact Or.inl present
  | succ fuel ih =>
      unfold ReferenceWorkQueue.State.drainReadyGroups.go
      dsimp only
      split
      · exact Or.inl present
      · rename_i group selected
        obtain ⟨member, zero⟩ := readyFacts selected
        cases cached : current.rejectedTask? group with
        | none =>
            dsimp only
            let released := current.finishGroupSuccess group
            let next := released.1.startNewWork released.2.2
            have all := bounded.allSettled member trivial (zero cached)
            have unlisted : occurrence ∉ group.tasks := fun listed => fresh (all occurrence listed)
            have nextPresent : key ∈ next.groupNodes.map (fun group => group.group.node.ref) := by
              rw [(ReferenceWorkQueue.State.startNewWork_groupCore _ _).1]
              exact finishGroupSuccess_linkedOwner_present links group member unlisted contributes present
            have nextLinks := (links.finishOtherGroupSuccess group unlisted).startNewWork released.2.2
            have nextBound := (bounded.finishGroupSuccess group all).startNewWork released.2.2
            have nextEdges : next.GroupEdgesFrom (registrationSnapshot before event) := by
              apply ReferenceWorkQueue.State.GroupEdgesFrom.trans _ edges
              intro key candidate lookup
              rw [ReferenceWorkQueue.State.groupNode?,
                (ReferenceWorkQueue.State.startNewWork_groupCore _ _).1] at lookup
              exact (current.finishGroupSuccess_descendants group).1 key candidate lookup
            have nextClosures := closures.append
              ((ReferenceWorkQueue.State.finishGroupSuccess_closureAccounting frame.live group member).post
                (fun _ retired => retired.startNewWork released.2.2))
            rcases ih (frame.finishGroupSuccess group |>.startNewWork released.2.2)
                (forest.finishGroupSuccess group |>.startNewWork released.2.2)
                nextEdges nextClosures nextLinks nextBound nextPresent with kept | cut
            · exact Or.inl kept
            · obtain ⟨root, failed, path⟩ := cut
              refine Or.inr ⟨root, ?_, ?_⟩
              · rw [failureRoots, List.filterMap_append]
                exact List.mem_append_right _ failed
              · simpa only [List.append_assoc] using path
        | some rejection =>
            obtain ⟨failed, errors⟩ := rejection
            dsimp only
            let next := (current.taskFailure failed errors).1
            rcases taskFailure_ownerCut failed errors fuel forest frame.keys edges closures present with
              nextPresent | cut
            · have nextEdges := (current.taskFailure_groupEdgesFrom failed errors).trans edges
              have nextClosures := closures.append
                (ReferenceWorkQueue.State.taskFailure_closureAccounting frame.live failed errors)
              rcases ih (frame.taskFailure failed errors) (forest.taskFailure failed errors)
                  nextEdges nextClosures (links.taskFailure_preserves failed errors)
                  (bounded.taskFailure_preserves failed errors) nextPresent with kept | cut
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
