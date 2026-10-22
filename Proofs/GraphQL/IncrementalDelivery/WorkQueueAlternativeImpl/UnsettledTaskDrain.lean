import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StartupFailurePath
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskRetention
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePathTransport

/-! An unsettled task owner survives successful draining or lies below a queued startup
failure. This covers unstarted tasks, without a buffered-value
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
            if group.pending == 0 then some group else none)
        = some node)
    : node ∈ queue.groupNodes ∧ node.pending = 0 := by
  obtain ⟨key, _, choice⟩ := List.exists_of_findSome?_eq_some selected
  cases found : queue.groupNode? key with
  | none => simp [found] at choice
  | some candidate =>
      simp only [found] at choice
      change (if _ then some candidate else none) = some node at choice
      split at choice
      · rename_i ready
        cases Option.some.inj choice
        exact ⟨List.mem_of_find?_eq_some found, beq_iff_eq.mp ready⟩
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
    : let drained := ReferenceWorkQueue.State.drainReadyGroups.go [] fuel current
      key ∈ drained.1.groupNodes.map (fun group => group.group.node.ref)
      ∨ ∃ failure ∈ drained.2.2,
          (failurePruningView before event (preceding ++ drained.2.1)).LiveDescendant
            failure.group.ref key := by
  induction fuel generalizing current preceding with
  | zero => exact .inl present
  | succ fuel ih =>
      unfold ReferenceWorkQueue.State.drainReadyGroups.go
      dsimp only
      split
      · exact .inl present
      · rename_i group selected
        obtain ⟨member, zero⟩ := readyFacts selected
        let released := current.finishGroupSuccess group
        let startup := released.1.startNewWork released.2.2
        let next := startup.1
        have all := bounded.allSettled member trivial zero
        have unlisted : occurrence ∉ group.tasks := fun listed => fresh (all occurrence listed)
        have afterPresent := finishGroupSuccess_linkedOwner_present links group member unlisted
          contributes present
        have afterForest := forest.finishGroupSuccess group
        have afterEdges := ((current.finishGroupSuccess_descendants group).1).trans edges
        have afterClosures := closures.append
          (ReferenceWorkQueue.State.finishGroupSuccess_closureAccounting frame.live group member)
        rcases ReferenceWorkQueue.State.startNewWork_ownerCut afterForest released.2.2
            (liveLookup afterPresent) with kept | cut
        · obtain ⟨owner, lookup⟩ := kept
          have nextPresent : key ∈ next.groupNodes.map (fun group => group.group.node.ref) :=
            List.mem_map.mpr ⟨owner, List.mem_of_find?_eq_some lookup,
              ReferenceWorkQueue.State.groupNode?_ref lookup⟩
          have nextLinks := (links.finishOtherGroupSuccess group unlisted).startNewWork released.2.2
          have nextBound := (bounded.finishGroupSuccess group all).startNewWork released.2.2
          have nextEdges := (ReferenceWorkQueue.State.startNewWork_groupEdgesFrom
            released.1 released.2.2).trans afterEdges
          have nextClosures := afterClosures.post
            (fun _ retired => retired.startNewWork released.2.2)
          rcases ih (frame.finishGroupSuccess group |>.startNewWork released.2.2)
              (afterForest.startNewWork released.2.2) nextEdges nextClosures nextLinks nextBound
              nextPresent with kept | cut
          · exact .inl kept
          · obtain ⟨failure, queued, path⟩ := cut
            exact .inr ⟨failure, List.mem_append_right _ queued,
              by simpa only [List.append_assoc] using path⟩
        · obtain ⟨failure, queued, path⟩ := cut
          refine .inr ⟨failure, List.mem_append_left _ queued, ?_⟩
          simpa only [List.append_assoc] using startupFailureBoundary_path released.2.2
            afterForest afterEdges afterClosures fuel queued path

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
