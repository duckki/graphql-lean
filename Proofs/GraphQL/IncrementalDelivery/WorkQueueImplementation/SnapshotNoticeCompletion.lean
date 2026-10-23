import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPreparedFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceNoticeAncestorRetirements

/-! Notice ancestor completions at actual FIFO handlers under their fixed cache snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Exposing cached rejections preserves tracked roots, cancellations, and output. -/
theorem GroupNoticeTracking.cacheTaskFailures {initial queue before}
    (tracked : GroupNoticeTracking initial (queue, before))
    (available : List (Occurrence × Nat))
    : GroupNoticeTracking initial (queue.cacheTaskFailures available, before) := by
  intro ref announced
  simpa only [State.cacheTaskFailures_rootGroups, State.cacheTaskFailures_cancelledGroups]
    using tracked ref announced

/-- An owner-fold notice completes its uncancelled announced ancestors at the same cut.
Earlier notices use the supplied tracking certificate. New owner-fold notices have real
contributors, and the fold's retirement theorem excludes their being noticed ancestors.
-/
theorem GroupNoticeTracking.ownerNoticeAncestor_completed
    {initial queue before work parents group groups streams child dependencies ref index}
    (tracked : GroupNoticeTracking initial (queue, before))
    (parent : ParentCutFrame queue work parents)
    (roots : RootReplayFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (owners : List Execution.DeliveryNode)
    (selected
      : (owners.foldl successGroupStep (queue, [], {})).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies) (uncancelled : ref ∉ queue.cancelledGroups)
    (announced
      : ref
        ∈ initial
          ++ (before
              ++ (owners.foldl successGroupStep (queue, [], {})).2.1.take
                  (index + 1)).flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ (before
          ++ (owners.foldl successGroupStep (queue, [], {})).2.1.take (index + 1)).flatMap
          rawGroupClosureRefs := by
  have alternatives : ref ∈ initial ++ before.flatMap rawGroupNoticeRefs ∨
      ref ∈ ((owners.foldl successGroupStep (queue, [], {})).2.1.take
        (index + 1)).flatMap rawGroupNoticeRefs := by
    simpa only [List.flatMap_append, List.mem_append, or_assoc] using announced
  rw [List.flatMap_append]
  rcases alternatives with earlier | current
  · rcases tracked ref earlier with active | cancelled | closed
    · exact List.mem_append_right _ (successGroupFold_noticeAncestor_completed generated
        roots.live.refs parent.records parent.links canonical parent.live parent.tasks
        roots.live.roots roots.live.support roots.live.present owners selected noticed known
        ancestor active)
    · exact False.elim (uncancelled cancelled)
    · exact List.mem_append_left _ closed
  · obtain ⟨event, included, mentioned⟩ := List.mem_flatMap.mp current
    have located := State.successGroupFold_groupNoticesLocated generated roots.live.refs
      parent.records roots.live.support owners event (List.mem_of_mem_take included)
    obtain ⟨source, contributors, task, contributes⟩ := located.contributor mentioned
    have absent := (successGroupFold_noticeAncestor_status generated roots.live.refs
      parent.records parent.links canonical parent.live parent.tasks roots.live.roots
      roots.live.support roots.live.present owners selected noticed known ancestor task
      contributes).1
    exact False.elim (absent (List.mem_flatMap.mpr ⟨event, included, mentioned⟩))

/-- A leading item notice's announced ancestor closed before this FIFO input.
Preparation retains old roots or marks them cancelled. Its notice certificate excludes
both alternatives for a task-bearing ancestor, so prior tracking supplies the completion.
-/
theorem UncancelledReplayFrame.leadingNoticeAncestor_completed
    {queue work parents before initial outputs stream items child dependencies ref
      occurrence owners}
    (frame : UncancelledReplayFrame queue work parents before)
    (tracked : GroupNoticeTracking initial (queue, outputs))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (task : TaskHasOwners work occurrence owners) (contributes : ref ∈ owners)
    (noticed
      : child
        ∈ (items.foldl (fun acc item => streamItemStep acc item available)
            (queue.cacheTaskFailures available, [], [], [], [])).2.1)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (announced : ref ∈ initial ++ outputs.flatMap rawGroupNoticeRefs)
    : ref ∈ outputs.flatMap rawGroupClosureRefs := by
  have matching := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  let current := queue.cacheTaskFailures available
  let prepared := current.preparedStreamItems items available
  have roots := (frame.streamItems_preparedFrames generated canonical matching available).2
  have ancestry := frame.streamItems_preparedNoticeAncestors generated canonical valid available
    licensed
  have retired := ancestry child.ref (by
      simp only [List.flatMap_singleton, rawGroupNoticeRefs]
      exact List.mem_map_of_mem noticed)
    child dependencies known rfl ref ancestor occurrence owners task contributes
  apply tracked.completed_of_inactive_uncancelled announced
  · intro retained
    have state :=
      List.mem_append.mp
        (current.streamItemFold_rootGroups items available
          (List.mem_append_left _
            (by simpa only [current, State.cacheTaskFailures_rootGroups] using retained)))
    rcases state with active | cancelled
    · exact retired.retired.2 (roots.live.present ref active)
    · exact retired.uncancelled cancelled
  · intro cancelled
    apply retired.uncancelled
    apply current.preparedStreamItems_cancelledGroups_subset items available
    simpa only [current, State.cacheTaskFailures_cancelledGroups] using cancelled

/-- Task notice completion uses the actual owner fold or the actual cached drain.
Tracking is carried from the supplied FIFO state into preparation, and the selected
prefix contains precisely the closures used by the corresponding phase theorem.
-/
theorem UncancelledReplayFrame.taskNoticeAncestor_completed
    {queue work parents before initial outputs occurrence result index group groups
      streams child dependencies ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (tracked : GroupNoticeTracking initial (queue, outputs))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    (selected
      : (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (uncancelled
      : ref
        ∉ (queue.handleGraphEvent (.taskSuccess occurrence result)
            available).1.cancelledGroups)
    (announced
      : ref
        ∈ initial
          ++ (outputs
              ++ (queue.handleGraphEvent (.taskSuccess occurrence result)
                    available).2.1.take
                  (index + 1)).flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ (outputs
          ++ (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1.take
              (index + 1)).flatMap
          rawGroupClosureRefs := by
  let current := queue.cacheTaskFailures available
  have source := tracked.cacheTaskFailures available
  change (current.taskSuccess occurrence result available).2.1[index]? = _ at selected
  change ref ∉ (current.taskSuccess occurrence result available).1.cancelledGroups at uncancelled
  change ref ∈ initial ++ (outputs ++ (current.taskSuccess occurrence result
    available).2.1.take (index + 1)).flatMap rawGroupNoticeRefs at announced
  change ref ∈ (outputs ++ (current.taskSuccess occurrence result available).2.1.take
    (index + 1)).flatMap rawGroupClosureRefs
  cases found : current.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found, List.getElem?_nil, reduceCtorEq] at selected
  | some incoming =>
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (folded.1.startNewWork folded.2.2 available).1
      obtain ⟨parent, roots⟩ := frame.taskSuccess_preparedFrames generated canonical occurrence result
        matching incoming available found
      have preparedTracking : GroupNoticeTracking initial (prepared, outputs) := by
        intro owner member
        rcases source owner member with live | cancelled | closed
        · exact .inl (by rwa [State.maybeIntegrateWork_rootGroups])
        · exact .inr (.inl (by
            change owner ∈
              (stored.maybeIntegrateWork result.work (some occurrence)).1.cancelledGroups
            rw [State.maybeIntegrateWork_cancelledGroups stored result.work (some occurrence)]
            exact stored.addGroups_cancelledGroups_subset result.work.groups cancelled))
        · exact .inr (.inr closed)
      rw [current.taskSuccess_eq occurrence result incoming found available]
        at selected uncancelled announced ⊢
      change (folded.2.1 ++ (active.drainReadyGroups available).2.1)[index]? = _ at selected
      by_cases inFold : index < folded.2.1.length
      · rw [List.getElem?_append_left inFold] at selected
        rw [List.take_append_of_le_length (by omega : index + 1 ≤ folded.2.1.length)]
          at announced ⊢
        apply preparedTracking.ownerNoticeAncestor_completed parent roots generated canonical
          incoming.task.groups selected noticed known ancestor _ announced
        intro cancelled
        apply uncancelled
        apply State.drainReadyGroups_go_cancelledGroups_subset _ _ available
        apply (folded.1.startNewWork_cancelledGroups_prefix folded.2.2 available).subset
        rwa [successGroupFold_cancelledGroups]
      · have inDrain : folded.2.1.length ≤ index := by omega
        rw [List.getElem?_append_right inDrain] at selected
        rw [List.take_append, List.take_of_length_le (by omega
          : folded.2.1.length ≤ index + 1), ← List.append_assoc] at announced ⊢
        have offset : index + 1 - folded.2.1.length = index - folded.2.1.length + 1 := by omega
        rw [offset] at announced ⊢
        have drainTracking := source.taskSuccessPreparation occurrence result incoming available
        exact drainTracking.drainNoticeAncestor_completed
            (roots.successGroupFold_start generated canonical incoming.task.groups available).live
            generated canonical active.groupNodes.length available selected noticed known ancestor
            uncancelled announced

/-- Item-handler group notices complete their ancestors at their indexed recursive drain.
The supplied tracking certificate includes the actual leading receipt before that drain.
-/
theorem UncancelledReplayFrame.itemDrainNoticeAncestor_completed
    {queue work parents before initial outputs stream items index group groups streams
      child dependencies ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (tracked : GroupNoticeTracking initial (queue, outputs))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    (selected
      : (queue.handleGraphEvent (.streamItems stream items) available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (uncancelled
      : ref
        ∉ (queue.handleGraphEvent (.streamItems stream items)
            available).1.cancelledGroups)
    (announced
      : ref
        ∈ initial
          ++ (outputs
              ++ (queue.handleGraphEvent (.streamItems stream items) available).2.1.take
                  (index + 1)).flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ (outputs
          ++ (queue.handleGraphEvent (.streamItems stream items) available).2.1.take
              (index + 1)).flatMap
          rawGroupClosureRefs := by
  let current := queue.cacheTaskFailures available
  change (current.streamItems stream items available).2.1[index]? = _ at selected
  change ref ∉ (current.streamItems stream items available).1.cancelledGroups at uncancelled
  change ref ∈ initial ++ (outputs ++ (current.streamItems stream items
    available).2.1.take (index + 1)).flatMap rawGroupNoticeRefs at announced
  change ref ∈ (outputs ++ (current.streamItems stream items available).2.1.take
    (index + 1)).flatMap rawGroupClosureRefs
  rw [current.streamItems_eq stream items available] at selected uncancelled announced ⊢
  cases active : current.rootStreams.contains stream.ref with
  | false => simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil,
      reduceCtorEq] at selected
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        at selected uncancelled announced ⊢
      cases index with
      | zero => cases selected
      | succ index =>
          simp only [List.take_succ_cons] at announced ⊢
          have roots := (frame.streamItems_preparedFrames generated canonical matching available).2
          have tracking := (tracked.cacheTaskFailures available).streamItemsPreparation stream
            items available
          have completed := tracking.drainNoticeAncestor_completed roots.live generated canonical
            _ available selected noticed known ancestor uncancelled
          simp only [List.append_assoc, List.singleton_append] at completed
          exact completed announced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
