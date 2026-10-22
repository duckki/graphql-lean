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
    : (queue.taskSuccess occurrence result).1.UncancelledRetiredHealthy work failed
      ∧ (queue.taskSuccess occurrence result).1.RootAncestorsHealthy work failed
      ∧ SuccessfulGroupsHealthy work failed (queue.taskSuccess occurrence result).2 := by
  have frame : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, ledger.refs, ledger.sound, ledger.matching⟩
  have health := frame.taskSuccess ledger generated canonical valid included eventMatches fresh
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
    : (queue.taskSuccess occurrence result).1.UncancelledRetiredHealthy work failed
      ∧ (queue.taskSuccess occurrence result).1.RootAncestorsHealthy work failed := by
  have frame : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, ledger.refs, ledger.sound, ledger.matching⟩
  have health := frame.taskSuccess ledger generated canonical valid included eventMatches fresh
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
    : GroupNoticeAncestorsHealthy work failed
        (queue.taskSuccess occurrence result).2 := by
  have frame : HealthFrame queue work parents failed :=
    ⟨matching, links, counts, retired, roots, ledger.refs, ledger.sound, ledger.matching⟩
  have health := frame.taskSuccess ledger generated canonical valid included eventMatches fresh
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
    : HealthFrame (queue.integrateStreamItem item) work parents failed
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
    prior.maybeIntegrateWork item.work known parentLinks children
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
      frame.tasks.pruneEmptyGroups _⟩
  exact ⟨afterPruning.startNewWork _ pruned.2, pruned.2⟩

/-- Item preparation supplies a healthy frame for every failure in the actual final drain. -/
theorem ReleaseHealth.HealthFrame.streamItems_failureAncestorHealth
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
    : GroupFailureAncestorsHealthy work failed (queue.streamItems stream items).2 := by
  have prepared := State.preparedStreamItems_preserves
    (fun current => HealthFrame current work parents failed) prior items
    (fun _ _ member frame =>
      (frame.integrateStreamItem_with_notices generated canonical failedKnown matching member).1)
  rw [State.streamItems_eq]
  split
  · exact .of_noFailures (by simp)
  · intro group errors member
    have later := (List.mem_cons.mp member).resolve_left (by intro impossible; cases impossible)
    exact prepared.drainReadyGroups_failureAncestorHealth generated canonical failedKnown
      group errors later

/-- A matching item batch preserves state health and certifies the final drain's carriers.
Witness: the exact item fold threads the same frame before activating or draining any
released group; the failed-record and root-ancestor obligations stay separate.
-/
theorem State.streamItems_releaseHealth {queue : State} {work parents failed}
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
    (tasks : queue.RegisteredTasksMatch work)
    : (queue.streamItems stream items).1.UncancelledRetiredHealthy work failed
      ∧ (queue.streamItems stream items).1.RootAncestorsHealthy work failed
      ∧ SuccessfulGroupsHealthy work failed (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, released) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups released.newGroups
    (pruned.startNewWork { released with newGroups := nonempty },
      groups ++ nonempty, streams ++ released.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (frame : HealthFrame acc.1 work parents failed)
      : HealthFrame (more.foldl step acc).1 work parents failed := by
    induction more generalizing acc with
    | nil => exact frame
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.integrateStreamItem_with_notices generated canonical failedKnown eventMatches
            (included List.mem_cons_self)).1
  unfold State.streamItems
  split
  · exact ⟨retired, roots, .nil work failed⟩
  · have frame := (loop items (fun _ member => member) (queue, [], [], [])
        ⟨matching, links, counts, retired, roots, refs, sound, tasks⟩).drainReadyGroups generated canonical failedKnown
    refine ⟨frame.1.retired, frame.1.roots, ?_⟩
    intro group groups streams member
    exact frame.2 group groups streams
      ((List.mem_cons.mp member).resolve_left (by intro impossible; cases impossible))

/-- Every item-carried or recursively drained group notice has healthy defer ancestry.
Witness: each item's real pruning frontier supplies its own certificate, retained in
the accumulated leading carrier; the final drain uses its exact bounded health frames.
-/
theorem State.streamItems_noticeAncestorHealth {queue : State} {work parents failed}
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
    (tasks : queue.RegisteredTasksMatch work)
    : GroupNoticeAncestorsHealthy work failed (queue.streamItems stream items).2 := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, released) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups released.newGroups
    (pruned.startNewWork { released with newGroups := nonempty },
      groups ++ nonempty, streams ++ released.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (frame : HealthFrame acc.1 work parents failed)
      (healthy : ∀ child ∈ acc.2.1, GroupAncestorsHealthy work failed child.ref)
      : HealthFrame (more.foldl step acc).1 work parents failed
        ∧ ∀ child ∈ (more.foldl step acc).2.1,
            GroupAncestorsHealthy work failed child.ref := by
    induction more generalizing acc with
    | nil => exact ⟨frame, healthy⟩
    | cons item rest ih =>
        have next := frame.integrateStreamItem_with_notices generated canonical failedKnown
          eventMatches (included List.mem_cons_self)
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member)) _ next.1
        intro child member
        exact (List.mem_append.mp member).elim (healthy child) (next.2 child)
  unfold State.streamItems
  split
  · simp [GroupNoticeAncestorsHealthy]
  · obtain ⟨frame, healthy⟩ := loop items (fun _ member => member) (queue, [], [], [])
      ⟨matching, links, counts, retired, roots, refs, sound, tasks⟩ (by simp)
    have drain := frame.drainReadyGroups_noticeHealth generated canonical failedKnown
    intro ref member
    rcases List.mem_append.mp member with leading | later
    · obtain ⟨child, noticed, same⟩ := List.mem_map.mp leading
      exact same ▸ healthy child noticed
    · exact drain ref later

/-- Item batches retain the original state-health interface.
Witness: project the strengthened item theorem, including its final-drain carrier health.
-/
theorem State.streamItems_retiredHealth {queue : State} {work parents failed}
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
    (tasks : queue.RegisteredTasksMatch work)
    : (queue.streamItems stream items).1.UncancelledRetiredHealthy work failed
      ∧ (queue.streamItems stream items).1.RootAncestorsHealthy work failed := by
  have health := queue.streamItems_releaseHealth retired roots generated matching links canonical
    counts failedKnown eventMatches refs sound tasks
  exact ⟨health.1, health.2.1⟩

/-- At a fixed failure inventory, rejection replay creates only cancelled retirements. -/
theorem State.UncancelledRetiredHealthy.taskFailure {queue : State} {work failed}
    (prior : queue.UncancelledRetiredHealthy work failed) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.UncancelledRetiredHealthy work failed :=
  prior.taskFailure_preserves occurrence errors

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
