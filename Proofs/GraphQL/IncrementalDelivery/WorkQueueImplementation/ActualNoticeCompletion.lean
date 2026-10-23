import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SnapshotNoticeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExactOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes

/-! Completion cuts compose through actual host batches without flattening queue state. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An actual FIFO group notice completes its announced task-bearing ancestors.
The same source frame supplies endpoint noncancellation and the selected phase's roots.
-/
theorem UncancelledReplayFrame.groupNoticeAncestor_completed
    {queue work parents before initial outputs event index group groups streams child
      dependencies ref occurrence owners}
    (frame : UncancelledReplayFrame queue work parents before)
    (tracked : GroupNoticeTracking initial (queue, outputs))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (task : TaskHasOwners work occurrence owners) (contributes : ref ∈ owners)
    (selected
      : (queue.handleGraphEvent event available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (announced
      : ref
        ∈ initial
          ++ (outputs
              ++ (queue.handleGraphEvent event available).2.1.take (index + 1)).flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ (outputs ++ (queue.handleGraphEvent event available).2.1.take (index + 1)).flatMap
          rawGroupClosureRefs := by
  have matching := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  have ancestry := frame.noticeAncestorRetirements generated canonical event valid available
    licensed
  have retired := ancestry child.ref (List.mem_flatMap.mpr
    ⟨_, List.mem_of_getElem? selected, List.mem_map_of_mem noticed⟩)
    child dependencies known rfl ref ancestor occurrence owners task contributes
  cases event with
  | taskSuccess address result =>
      exact frame.taskNoticeAncestor_completed tracked generated canonical matching available
        selected noticed known ancestor retired.uncancelled announced
  | streamItems stream items =>
      exact frame.itemDrainNoticeAncestor_completed tracked generated canonical matching available
        selected noticed known ancestor retired.uncancelled announced
  | taskFailure address errors =>
      exact False.elim ((queue.cacheTaskFailures available).taskFailure_noGroupSuccess
        address errors group groups streams (List.mem_of_getElem? selected))
  | streamSuccess stream =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member
  | groupFailure notice =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · cases member
      · split at member <;> simp at member

/-- A selected item receipt completes announced ancestors strictly before that receipt.
Inversion fixes the leading index and the preparation frontier under the same snapshot.
-/
theorem UncancelledReplayFrame.itemNoticeAncestor_completed
    {queue work parents before initial outputs event index owner values groups streams
      child dependencies ref occurrence owners}
    (frame : UncancelledReplayFrame queue work parents before)
    (tracked : GroupNoticeTracking initial (queue, outputs))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (task : TaskHasOwners work occurrence owners) (contributes : ref ∈ owners)
    (selected
      : (queue.handleGraphEvent event available).2.1[index]?
        = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (announced
      : ref
        ∈ initial
          ++ (outputs ++ (queue.handleGraphEvent event available).2.1.take index).flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ (outputs ++ (queue.handleGraphEvent event available).2.1.take index).flatMap
          rawGroupClosureRefs := by
  obtain ⟨stream, items, rfl⟩ := queue.handleGraphEvent_streamValues_source event available selected
  let current := queue.cacheTaskFailures available
  change (current.streamItems stream items available).2.1[index]? = _ at selected
  rw [current.streamItems_eq stream items available] at selected
  cases active : current.rootStreams.contains stream.ref with
  | false => simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil,
      reduceCtorEq] at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at selected
      cases index with
      | zero =>
          cases selected
          simp only [List.take_zero, List.append_nil] at announced ⊢
          exact frame.leadingNoticeAncestor_completed tracked generated canonical valid available
            licensed task contributes noticed known ancestor announced
      | succ index =>
          have absent :=
            (current.preparedStreamItems items available).drainReadyGroups_noStreamValues
              owner values groups streams available
          exact False.elim (absent (List.mem_of_getElem? selected))

/-- Earlier complete batches and a FIFO prefix retain the same notice tracking evidence. -/
theorem State.batchPrefix_groupNoticeTracking (queue : State)
    (earlier : List (List GraphEvent)) (fifo : List GraphEvent)
    (available : List (Occurrence × Nat))
    : GroupNoticeTracking queue.rootGroups
        (
          ((queue.replayBatches earlier).replayGraphEvents fifo available),
          (queue.rawBatches earlier).2
          ++ ((queue.replayBatches earlier).rawEventReplay fifo available).2
        ) := by
  have first := queue.rawBatches_groupNoticeTracking earlier
  change GroupNoticeTracking _ ((queue.rawBatches earlier).1, _) at first
  rw [State.rawBatches_state] at first
  have next := (queue.replayBatches earlier).rawEventReplay_groupNoticeTracking fifo available
  change GroupNoticeTracking _ (((queue.replayBatches earlier).rawEventReplay fifo available).1, _)
    at next
  rw [State.rawEventReplay_state _ fifo available] at next
  exact first.append next (State.replayGraphEvents_cancelledGroups_subset _ fifo available)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
