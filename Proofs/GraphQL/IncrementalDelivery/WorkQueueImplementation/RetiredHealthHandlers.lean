import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulTaskHealth

/-! Health of actual source handlers from successful counters and retained rejections. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open ReleaseHealth

/-- A source-valid task success preserves historical health and successful carriers. -/
theorem State.taskSuccess_releaseHealth {queue : State}
    {work parents failed before}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (_failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.UncancelledRetiredHealthy work
        failed
      ∧ (queue.taskSuccess occurrence result available).1.RootAncestorsHealthy work failed
      ∧ SuccessfulGroupsHealthy work failed
          (queue.taskSuccess occurrence result available).2.1 := by
  have frame : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, ledger.refs, ledger.sound, ledger.matching, ledger.registration.live⟩
  have health := frame.taskSuccess ledger generated canonical valid included eventMatches fresh
    available
  exact ⟨health.1.retired, health.1.roots, health.2.1⟩

/-- Source-valid task success preserves both state health certificates. -/
theorem State.taskSuccess_retiredHealth {queue : State}
    {work parents failed before}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (_failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.UncancelledRetiredHealthy work
        failed
      ∧ (queue.taskSuccess occurrence result available).1.RootAncestorsHealthy work
          failed := by
  have frame : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, ledger.refs, ledger.sound, ledger.matching, ledger.registration.live⟩
  have health := frame.taskSuccess ledger generated canonical valid included eventMatches fresh
    available
  exact ⟨health.1.retired, health.1.roots⟩

/-- Every notice in source-valid task success has healthy defer ancestry. -/
theorem State.taskSuccess_noticeAncestorHealth {queue : State}
    {work parents failed before}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (_failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {occurrence result}
    (eventMatches : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeAncestorsHealthy work failed
        (queue.taskSuccess occurrence result available).2.1 := by
  have frame : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, ledger.refs, ledger.sound, ledger.matching, ledger.registration.live⟩
  have health := frame.taskSuccess ledger generated canonical valid included eventMatches fresh
    available
  exact health.2.2.1

-----------------------------------------------------------------------------------------
-- Stream items integrate parentless candidates, prune wrappers, and activate descendants
-----------------------------------------------------------------------------------------

/-- A matching streamed item preserves both health certificates through real pruning.
Witness: initially parentless candidates have healthy ancestry, and pruning propagates
it to descendants before activation; no no-pruning assumption is imposed.
-/
private theorem ReleaseHealth.HealthFrame.integrateStreamItem_with_notices
    {queue work parents failed} (prior : HealthFrame queue work parents failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (member : item ∈ items)
    (available : List (Occurrence × Nat) := [])
    : HealthFrame (queue.integrateStreamItem item available) work parents failed
      ∧ ∀ child ∈
          ((queue.maybeIntegrateWork item.work).1.pruneEmptyGroups
            (queue.maybeIntegrateWork item.work).2.newGroups).2,
          GroupAncestorsHealthy work failed child.ref := by
  let integrated := queue.maybeIntegrateWork item.work
  have known : ∀ group ∈ item.work.groups,
      ∃ dependencies, GroupRecordAt work group.node dependencies :=
    fun _ candidate => matching.streamItem_childGroups_recordAt member candidate
  have parentLinks : ∀ group ∈ item.work.groups,
      group.parent = (parents group.node.ref).head? :=
    fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical member candidate
  have children : ∀ task ∈ item.work.tasks, TaskMatches work task := by
    intro task included
    obtain ⟨address, payload, same, known⟩ := matching.streamItem_childTask_producer member included
    exact ⟨⟨address, payload, _, same, known⟩,
      matching.streamItem_childTask_groupsExact member included⟩
  have frame : HealthFrame integrated.1 work parents failed :=
    prior.maybeIntegrateWork item.work known parentLinks children none generated canonical
      (generated.declarations.sourceStreamItem matching member queue.registeredGroups).parentRefs
  have candidates := queue.maybeIntegrateWork_newGroups_ancestorsHealthy (failed := failed)
    generated canonical
    item.work known parentLinks
  have pruned := frame.retired.pruneEmptyGroups generated frame.groups frame.links canonical
    frame.counts failedKnown integrated.2.newGroups candidates
  have afterPruning : HealthFrame (integrated.1.pruneEmptyGroups integrated.2.newGroups).1
      work parents failed :=
    ⟨frame.groups.pruneEmptyGroups _, frame.links.pruneEmptyGroups _,
      frame.counts.pruneEmptyGroups _, pruned.1, by
        intro ref active
        rw [State.pruneEmptyGroups_rootGroups] at active
        exact frame.roots ref active,
      frame.refs.pruneEmptyGroups _, frame.sound.pruneEmptyGroups _,
      frame.tasks.pruneEmptyGroups _, frame.live.pruneEmptyGroups _⟩
  exact ⟨afterPruning.startNewWork _ pruned.2 available, pruned.2⟩

/-- Item preparation supplies a healthy frame for every failure in the actual final drain. -/
theorem ReleaseHealth.HealthFrame.streamItems_failureAncestorHealth
    {queue work parents failed} (_prior : HealthFrame queue work parents failed)
    (_generated : ExecutedWork work)
    (_canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (_failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (_matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupFailureAncestorsHealthy work failed
        (queue.streamItems stream items available).2.1 := by
  exact .of_noFailures (fun group errors =>
    queue.streamItems_groupFailure_absent stream items group errors available)

private theorem ReleaseHealth.HealthFrame.preparedItems_health
    {queue work parents failed settled} (prior : HealthFrame queue work parents failed)
    (bounded : queue.PendingBound (fun _ => True) settled) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : let final :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      HealthFrame final.1 work parents failed
      ∧ final.1.PendingBound (fun _ => True) settled
      ∧ ∀ child ∈ final.2.1, GroupAncestorsHealthy work failed child.ref := by
  have loop (remaining : List StreamItem) (included : remaining.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List StreamItemValue × List GroupFailureEvent)
      (frame : HealthFrame acc.1 work parents failed)
      (pending : acc.1.PendingBound (fun _ => True) settled)
      (healthy : ∀ child ∈ acc.2.1, GroupAncestorsHealthy work failed child.ref)
      : let final := remaining.foldl (fun acc item => streamItemStep acc item available) acc
        HealthFrame final.1 work parents failed
        ∧ final.1.PendingBound (fun _ => True) settled
        ∧ ∀ child ∈ final.2.1, GroupAncestorsHealthy work failed child.ref := by
    induction remaining generalizing acc with
    | nil => exact ⟨frame, pending, healthy⟩
    | cons item rest ih =>
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let released : NewWork := { integrated.2 with newGroups := pruned.2 }
        have next := frame.integrateStreamItem_with_notices generated canonical failedKnown matching
          (included List.mem_cons_self) available
        have preparedBound : pruned.1.PendingBound (fun _ => True) settled :=
          (pending.maybeIntegrateWork item.work).pruneEmptyGroups _
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (streamItemStep acc item available) next.1
          (preparedBound.startNewWork released available)
        intro child member
        exact (List.mem_append.mp member).elim (healthy child) (next.2 child)
  exact loop items (List.Subset.refl _) (queue, [], [], [], []) prior bounded (by simp)

/-- A matching item batch preserves state health and certifies the final drain's carriers.
Witness: the exact item fold threads the same frame before activating or draining any
released group; the failed-record and root-ancestor obligations stay separate.
-/
theorem State.streamItems_releaseHealth {queue : State} {work parents failed settled}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    (refs : queue.GroupRefsUnique) (sound : queue.GroupMembershipSound)
    (tasks : queue.RegisteredTasksMatch work) (live : queue.LiveGroupsRegistered)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.UncancelledRetiredHealthy work failed
      ∧ (queue.streamItems stream items available).1.RootAncestorsHealthy work failed
      ∧ SuccessfulGroupsHealthy work failed
          (queue.streamItems stream items available).2.1 := by
  have prior : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, refs, sound, tasks, live⟩
  have prepared := prior.preparedItems_health bounded generated canonical failedKnown eventMatches
    available
  rw [queue.streamItems_eq stream items available]
  split
  · exact ⟨retired, roots, .nil work failed⟩
  · have drain := prepared.1.drainReadyGroups generated canonical failedKnown prepared.2.1
      disjoint available
    refine ⟨drain.1.retired, drain.1.roots, ?_⟩
    intro group groups streams member
    exact drain.2 group groups streams
      ((List.mem_cons.mp member).resolve_left (by intro impossible; cases impossible))

/-- Every item-carried or recursively drained group notice has healthy defer ancestry.
Witness: each item's real pruning frontier supplies its own certificate, retained in
the accumulated leading carrier; the final drain uses its exact bounded health frames.
-/
theorem State.streamItems_noticeAncestorHealth {queue : State}
    {work parents failed settled} (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    (refs : queue.GroupRefsUnique) (sound : queue.GroupMembershipSound)
    (tasks : queue.RegisteredTasksMatch work) (live : queue.LiveGroupsRegistered)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeAncestorsHealthy work failed
        (queue.streamItems stream items available).2.1 := by
  have prior : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, refs, sound, tasks, live⟩
  have prepared := prior.preparedItems_health bounded generated canonical failedKnown eventMatches
    available
  rw [queue.streamItems_eq stream items available]
  split
  · simp [GroupNoticeAncestorsHealthy]
  · have drain := prepared.1.drainReadyGroups_noticeHealth generated canonical failedKnown
      prepared.2.1 disjoint available
    intro ref member
    rcases List.mem_append.mp member with leading | later
    · obtain ⟨child, noticed, same⟩ := List.mem_map.mp leading
      exact same ▸ prepared.2.2 child noticed
    · exact drain ref later

/-- Item batches retain the original state-health interface.
Witness: project the strengthened item theorem, including its final-drain carrier health.
-/
theorem State.streamItems_retiredHealth {queue : State} {work parents failed settled}
    (retired : queue.UncancelledRetiredHealthy work failed)
    (roots : queue.RootAncestorsHealthy work failed) (generated : ExecutedWork work)
    (matching : queue.GroupNodesMatchWork work)
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (counts : queue.RetainedFailures work failed)
    (failedKnown
      : ∀ occurrence ∈ failed,
          ∃ owners producer payload,
            TaskAt work occurrence owners producer payload
            ∧ payload.failure.isSome = true)
    {stream items} (eventMatches : (GraphEvent.streamItems stream items).MatchesWork work)
    (refs : queue.GroupRefsUnique) (sound : queue.GroupMembershipSound)
    (tasks : queue.RegisteredTasksMatch work) (live : queue.LiveGroupsRegistered)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (disjoint : ∀ occurrence ∈ settled, occurrence ∉ failed)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.UncancelledRetiredHealthy work failed
      ∧ (queue.streamItems stream items available).1.RootAncestorsHealthy work
          failed := by
  have health := queue.streamItems_releaseHealth retired roots generated matching links canonical
    counts failedKnown eventMatches refs sound tasks live bounded disjoint available
  exact ⟨health.1, health.2.1⟩

/-- At a fixed failure inventory, rejection replay creates only cancelled retirements. -/
theorem State.UncancelledRetiredHealthy.taskFailure {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredHealthy work failed :=
  prior.taskFailure_preserves occurrence errors

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
