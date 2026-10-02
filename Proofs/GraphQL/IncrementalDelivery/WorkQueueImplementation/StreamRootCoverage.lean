import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! The queue actually activates every stream notice emitted by a successful handler. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Integration stores every stream it releases
-----------------------------------------------------------------------------------------

/-- Stream registration retains old descriptors and stores every returned stream notice.
Witness: fresh descriptors are appended before either root release or task attachment.
No property of the incoming stream list or parent occurrence is required.
-/
theorem State.addStreams_registered (queue : State) (streams : List Stream)
    (parent : Option Occurrence)
    : queue.streams.Subset (queue.addStreams streams parent).1.streams
      ∧ (queue.addStreams streams parent).2.Subset
          ((queue.addStreams streams parent).1.streams.map Stream.node) := by
  unfold State.addStreams
  cases parent with
  | none =>
      refine ⟨List.subset_append_left _ _, ?_⟩
      intro node member
      obtain ⟨stream, selected, same⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨stream, List.mem_append_right _ selected, same⟩
  | some occurrence =>
      dsimp only
      split <;> exact ⟨List.subset_append_left _ _, by intro node impossible; cases impossible⟩

/-- Full work integration retains streams and registers all newly released descriptors.
Witness: group/task stages preserve the registry, then actual stream registration appends.
-/
theorem State.maybeIntegrateWork_streams_registered (queue : State) (work : Work)
    (parent : Option Occurrence := none)
    : queue.streams.Subset (queue.maybeIntegrateWork work parent).1.streams
      ∧ (queue.maybeIntegrateWork work parent).2.newStreams.Subset
          ((queue.maybeIntegrateWork work parent).1.streams.map Stream.node) := by
  have known := State.addStreams_registered
    (work.tasks.foldl State.addTask (queue.addGroups work.groups).1) work.streams parent
  rw [fold_projection State.streams State.addTask State.addTask_streams,
    State.addGroups_streams] at known
  exact known

-----------------------------------------------------------------------------------------
-- Group processing only adds stream roots, and covers every emitted stream notice
-----------------------------------------------------------------------------------------

/-- A recursive group drain activates every stream it announces and keeps old stream roots.
Witness: each successful release activates registered descriptors; group failure changes
neither stream roots nor stream notices. Concatenate exact notice lists through recursion.
-/
theorem State.drainReadyGroups_go_streamRoots_cover (fuel : Nat) (queue : State)
    : (queue.rootStreams
        ++ (State.drainReadyGroups.go fuel queue).2.flatMap rawStreamNoticeKeys).Subset
        (State.drainReadyGroups.go fuel queue).1.rootStreams := by
  induction fuel generalizing queue with
  | zero =>
      intro key member
      simpa only [State.drainReadyGroups.go, List.flatMap_nil, List.append_nil] using member
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · intro key member; simpa using member
      · rename_i node selected
        cases cached : node.failure with
        | none =>
            have first := queue.finishGroupSuccess_streamRoots_cover node
            have later := ih ((queue.finishGroupSuccess node).1.startNewWork
              (queue.finishGroupSuccess node).2.2)
            intro key member
            apply later
            simp only [List.flatMap_append] at member
            rcases List.mem_append.mp member with old | notice
            · exact List.mem_append_left _ (first (List.mem_append_left _ old))
            · rcases List.mem_append.mp notice with early | late
              · exact List.mem_append_left _ (first (List.mem_append_right _ early))
              · exact List.mem_append_right _ late
        | some errors =>
            have same : (queue.removeGroup node.group.node.key).rootStreams
                = queue.rootStreams := rfl
            simpa only [State.finishGroupFailure, List.flatMap_append,
              List.flatMap_singleton, rawStreamNoticeKeys, List.nil_append, same]
              using ih (queue.removeGroup node.group.node.key)

/-- The actual owner fold retains its registry and roots while accumulating registered
stream releases, with exactly the same keys as its emitted notices.
Witness: each successful flush preserves stream fields and resolves every release by
lookup; counter-only and missing-owner steps leave this invariant unchanged.
-/
theorem State.successGroupFold_streamRelease (queue : State)
    (groups : List Execution.DeliveryNode)
    : let folded := groups.foldl successGroupStep (queue, [], {})
      folded.1.rootStreams = queue.rootStreams
      ∧ folded.1.streams = queue.streams
      ∧ folded.2.2.newStreams.map Execution.DeliveryNode.key
        = folded.2.1.flatMap rawStreamNoticeKeys
      ∧ folded.2.2.newStreams.Subset (folded.1.streams.map Stream.node) := by
  have loop (remaining : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork)
      (roots : acc.1.rootStreams = queue.rootStreams)
      (streams : acc.1.streams = queue.streams)
      (notices : acc.2.2.newStreams.map Execution.DeliveryNode.key
        = acc.2.1.flatMap rawStreamNoticeKeys)
      (registered : acc.2.2.newStreams.Subset (acc.1.streams.map Stream.node))
      : let folded := remaining.foldl successGroupStep acc
        folded.1.rootStreams = queue.rootStreams
        ∧ folded.1.streams = queue.streams
        ∧ folded.2.2.newStreams.map Execution.DeliveryNode.key
            = folded.2.1.flatMap rawStreamNoticeKeys
        ∧ folded.2.2.newStreams.Subset (folded.1.streams.map Stream.node) := by
    induction remaining generalizing acc with
    | nil => exact ⟨roots, streams, notices, registered⟩
    | cons group rest ih =>
        rw [List.foldl_cons]
        obtain ⟨current, outputs, released⟩ := acc
        unfold successGroupStep
        dsimp only
        split
        · exact ih _ roots streams notices registered
        · rename_i node found
          split
          · apply ih
            · rw [State.finishGroupSuccess_rootStreams]; exact roots
            · rw [State.finishGroupSuccess_streams]; exact streams
            · simp only [List.map_append, List.flatMap_append, notices,
                State.finishGroupSuccess_streamNotices]
            · intro stream member
              rcases List.mem_append.mp member with old | added
              · rw [State.finishGroupSuccess_streams]
                exact registered old
              · exact State.finishGroupSuccess_streams_registered _ _ added
          · exact ih _ roots streams notices registered
  exact loop groups (queue, [], {}) rfl rfl rfl
    (by intro node impossible; cases impossible)

/-- Task success activates every stream notice, even when owners release in one pass.
Witness: the owner fold accumulates registered releases; their activation and the final
drain both cover their exact notice inventories while retaining all old stream roots.
-/
theorem State.taskSuccess_streamRoots_cover (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.rootStreams
        ++ (queue.taskSuccess occurrence result).2.flatMap rawStreamNoticeKeys).Subset
        (queue.taskSuccess occurrence result).1.rootStreams := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      intro key member; simpa using member
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found]
      split
      · intro key member
        change key ∈ queue.rootStreams
        simpa using member
      · let prepared := ((queue.putTaskNode
          { incoming with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1
        let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
        have roots : prepared.rootStreams = queue.rootStreams :=
          State.maybeIntegrateWork_rootStreams _ _ _
        have release := prepared.successGroupFold_streamRelease incoming.task.groups
        have first := folded.1.startNewWork_streamRoots_cover folded.2.2 release.2.2.2
        rw [release.1, release.2.2.1, roots] at first
        have later := State.drainReadyGroups_go_streamRoots_cover
          (folded.1.startNewWork folded.2.2).groupNodes.length
          (folded.1.startNewWork folded.2.2)
        intro key member
        apply later
        simp only [List.flatMap_append] at member
        rcases List.mem_append.mp member with old | noticed
        · exact List.mem_append_left _ (first (List.mem_append_left _ old))
        · rcases List.mem_append.mp noticed with early | late
          · exact List.mem_append_left _ (first (List.mem_append_right _ early))
          · exact List.mem_append_right _ late

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
