import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamCompletionReplay

/-! Every earlier stream notice remains represented in the permanent stream registry. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice-producing handlers retain both old descriptors and newly announced refs
-----------------------------------------------------------------------------------------

/-- Every stream notice from a group drain belongs to its unchanged stream registry.
Witness: each flush resolves stored child refs; subsequent activation and group removal
leave descriptors untouched. This includes several releases inside the same drain.
-/
theorem State.drainReadyGroups_streamNotices_registered (queue : State)
    : (queue.drainReadyGroups.2.flatMap rawStreamNoticeRefs).Subset
        (queue.streams.map (fun stream => stream.node.ref)) := by
  have loop (fuel : Nat) (current : State)
      : ((State.drainReadyGroups.go fuel current).2.flatMap rawStreamNoticeRefs).Subset
          (current.streams.map (fun stream => stream.node.ref)) := by
    induction fuel generalizing current with
    | zero => intro ref impossible; cases impossible
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · intro ref impossible; cases impossible
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              dsimp only
              have later := ih ((current.finishGroupSuccess node).1.startNewWork
                (current.finishGroupSuccess node).2.2)
              rw [State.startNewWork_streams, State.finishGroupSuccess_streams] at later
              intro ref member
              rw [List.flatMap_append] at member
              rcases List.mem_append.mp member with earlier | after
              · rw [← State.finishGroupSuccess_streamNotices] at earlier
                obtain ⟨stream, included, same⟩ := List.mem_map.mp earlier
                have known := State.finishGroupSuccess_streams_registered current node included
                rw [State.finishGroupSuccess_streams] at known
                obtain ⟨descriptor, registered, equal⟩ := List.mem_map.mp known
                exact List.mem_map.mpr ⟨descriptor, registered,
                  (congrArg Execution.DeliveryNode.ref equal).trans same⟩
              · exact later after
          | some errors =>
              intro ref member
              apply ih (current.removeGroup node.group.node.ref)
              simpa only [State.finishGroupFailure, List.flatMap_append,
                List.flatMap_singleton, rawStreamNoticeRefs, List.nil_append] using member
  exact loop _ queue

/-- Task success retains old stream refs and registers all its emitted stream notices.
Witness: preparation appends descriptors once; the shared-owner fold and final drain
only release entries from that registry. Ignored settlements leave it unchanged.
-/
theorem State.taskSuccess_streamRegistry (queue : State) (occurrence : Occurrence)
    (result : TaskResult)
    : let final := queue.taskSuccess occurrence result
      (queue.streams.map (fun stream => stream.node.ref)).Subset
        (final.1.streams.map (fun stream => stream.node.ref))
      ∧ (final.2.flatMap rawStreamNoticeRefs).Subset
          (final.1.streams.map (fun stream => stream.node.ref)) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact ⟨List.Subset.refl _, by intro ref impossible; cases impossible⟩
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found]
      split
      · exact ⟨List.Subset.refl _, by intro ref impossible; cases impossible⟩
      · let stored := queue.putTaskNode { incoming with value := some result.value }
        let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
        let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
        have release := prepared.successGroupFold_streamRelease incoming.task.groups
        have registry : (folded.1.startNewWork folded.2.2).drainReadyGroups.1.streams
            = prepared.streams := by
          rw [State.drainReadyGroups_streams, State.startNewWork_streams, release.2.1]
        change (queue.streams.map _).Subset
            ((folded.1.startNewWork folded.2.2).drainReadyGroups.1.streams.map _)
          ∧ ((folded.2.1 ++ (folded.1.startNewWork folded.2.2).drainReadyGroups.2).flatMap
              rawStreamNoticeRefs).Subset _
        rw [registry]
        refine ⟨List.map_subset _ (stored.maybeIntegrateWork_streams_registered
          result.work (some occurrence)).1, ?_⟩
        intro ref member
        rw [List.flatMap_append] at member
        rcases List.mem_append.mp member with earlier | later
        · rw [← release.2.2.1] at earlier
          obtain ⟨node, included, same⟩ := List.mem_map.mp earlier
          have known := release.2.2.2 included
          rw [release.2.1] at known
          obtain ⟨stream, registered, descriptor⟩ := List.mem_map.mp known
          exact List.mem_map.mpr ⟨stream, registered,
            (congrArg Execution.DeliveryNode.ref descriptor).trans same⟩
        · have known := (folded.1.startNewWork folded.2.2).drainReadyGroups_streamNotices_registered
            later
          rwa [State.startNewWork_streams, release.2.1] at known

/-- Item processing retains old stream refs and registers its leading and drained notices.
Witness: the multi-item inventory supplies preparation's registry, and the group drain
retains it. The inactive-stream branch emits nothing and changes nothing.
-/
theorem State.streamItems_streamRegistry (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : let final := queue.streamItems stream items
      (queue.streams.map (fun stream => stream.node.ref)).Subset
        (final.1.streams.map (fun stream => stream.node.ref))
      ∧ (final.2.flatMap rawStreamNoticeRefs).Subset
          (final.1.streams.map (fun stream => stream.node.ref)) := by
  rw [queue.streamItems_eq stream items]
  split
  · exact ⟨List.Subset.refl _, by intro ref impossible; cases impossible⟩
  · let prepared := items.foldl streamItemStep (queue, [], [], [])
    have inventory := streamItemFold_streamNoticeInventory items
      (queue.streams.map (fun stream => stream.node.ref)) (queue, [], [], [])
      (List.Subset.refl _) (by intro ref impossible; cases impossible) (by simp) (by simp)
    dsimp only
    rw [State.drainReadyGroups_streams]
    refine ⟨inventory.1, ?_⟩
    intro ref member
    rcases List.mem_append.mp member with leading | later
    · exact inventory.2.1 leading
    · exact prepared.1.drainReadyGroups_streamNotices_registered later

-----------------------------------------------------------------------------------------
-- Completed streams retain registration after they leave the active-root list
-----------------------------------------------------------------------------------------

/-- Every raw handler preserves old registrations and stores each emitted stream notice.
Witness: success handlers use their exact registries; failures/completions retain the
registry even when active stream roots are removed.
-/
theorem State.handleGraphEvent_streamRegistry (queue : State) (event : GraphEvent)
    : let final := queue.handleGraphEvent event
      (queue.streams.map (fun stream => stream.node.ref)).Subset
        (final.1.streams.map (fun stream => stream.node.ref))
      ∧ (final.2.flatMap rawStreamNoticeRefs).Subset
          (final.1.streams.map (fun stream => stream.node.ref)) := by
  cases event with
  | taskSuccess occurrence result =>
      exact queue.taskSuccess_streamRegistry occurrence result
  | streamItems stream items => exact queue.streamItems_streamRegistry stream items
  | taskFailure occurrence errors =>
      simp only [State.handleGraphEvent, State.taskFailure_streams,
        State.taskFailure_streamNoticeRefs]
      exact ⟨List.Subset.refl _, by intro ref impossible; cases impossible⟩
  | streamSuccess stream =>
      simp only [State.handleGraphEvent]
      unfold State.streamSuccess
      split <;> exact ⟨List.Subset.refl _, by intro ref impossible; cases impossible⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent]
      unfold State.streamFailure
      split <;> exact ⟨List.Subset.refl _, by intro ref impossible; cases impossible⟩

/-- Every initial registered ref and earlier stream notice is registered at replay's end.
Witness: compose the concrete per-handler registry inclusions along actual raw replay.
No source matching, uniqueness, or generated-work assumption is needed.
-/
theorem State.rawEventReplay_streamRegistry (queue : State) (events : List GraphEvent)
    : (queue.streams.map (fun stream => stream.node.ref)
        ++ (queue.rawEventReplay events).2.flatMap rawStreamNoticeRefs).Subset
        ((queue.rawEventReplay events).1.streams.map
          (fun stream => stream.node.ref)) := by
  induction events generalizing queue with
  | nil => intro ref member; simpa [State.rawEventReplay] using member
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      have first := queue.handleGraphEvent_streamRegistry event
      have later := ih (queue.handleGraphEvent event).1
      intro ref member
      apply later
      change ref ∈ queue.streams.map _
        ++ ((queue.handleGraphEvent event).2 ++
          ((queue.handleGraphEvent event).1.rawEventReplay rest).2).flatMap
            rawStreamNoticeRefs at member
      rw [List.flatMap_append] at member
      rcases List.mem_append.mp member with old | noticed
      · exact List.mem_append_left _ (first.1 old)
      · rcases List.mem_append.mp noticed with early | late
        · exact List.mem_append_left _ (first.2 early)
        · exact List.mem_append_right _ late

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
