import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupParents

/-! Exact healthy counters use all-group bounds, not healthy-root assumptions, for safety. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Separate exact selected counters from the bound protecting every flush
-----------------------------------------------------------------------------------------

/-- The success loop preserves exact debt on selected groups and lower bounds everywhere.
Witness: owner-list induction pays both debts together. The all-group bound justifies
every flush, even when its owner is not among the groups requiring an exact counter.
-/
theorem successGroupFold_preservesSelected (eligible : Nat → Prop)
    (settled : List Occurrence) (groups : List Execution.DeliveryNode)
    (unique : (groups.map Execution.DeliveryNode.ref).Nodup)
    (acc : State × List WorkQueueEvent × NewWork) (refs : acc.1.GroupRefsUnique)
    (tracks : acc.1.PendingDebt eligible settled (groups.map Execution.DeliveryNode.ref))
    (bounded
      : acc.1.PendingDebtBound (fun _ => True) settled
          (groups.map Execution.DeliveryNode.ref))
    : (groups.foldl successGroupStep acc).1.PendingDebt eligible settled []
      ∧ (groups.foldl successGroupStep acc).1.PendingBound (fun _ => True) settled := by
  suffices final : (groups.foldl successGroupStep acc).1.PendingDebt eligible settled [] ∧
      (groups.foldl successGroupStep acc).1.PendingDebtBound (fun _ => True) settled [] from
    ⟨final.1, final.2.toBound⟩
  induction groups generalizing acc with
  | nil => exact ⟨tracks, bounded⟩
  | cons group rest ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      have step : (successGroupStep acc group).1.GroupRefsUnique ∧
          (successGroupStep acc group).1.PendingDebt eligible settled
            (rest.map Execution.DeliveryNode.ref) ∧
          (successGroupStep acc group).1.PendingDebtBound (fun _ => True) settled
            (rest.map Execution.DeliveryNode.ref) := by
        obtain ⟨queue, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · rename_i missing
          exact ⟨refs, tracks.skipMissing missing, bounded.skipMissing missing⟩
        · rename_i node found
          have nextRefs := refs.putGroupNode { node with pending := node.pending - 1 }
          have nextTracks := tracks.decrement refs absent found
          have nextBound := bounded.decrement refs absent found
          split
          · rename_i ready
            have zero : node.pending - 1 = 0 := by
              simpa using (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ready).1).2
            have member : { node with pending := node.pending - 1 } ∈
                (queue.putGroupNode { node with pending := node.pending - 1 }).groupNodes := by
              exact List.mem_map.mpr ⟨node, List.mem_of_find?_eq_some found, by simp⟩
            have all := nextBound.allSettled member trivial zero
            exact ⟨nextRefs.finishGroupSuccess _, nextTracks.finishGroupSuccess _ all,
              nextBound.finishGroupSuccess _ all⟩
          · exact ⟨nextRefs, nextTracks, nextBound⟩
      exact ih tailUnique _ step.1 step.2.1 step.2.2

/-- Exact healthy counters survive draining even when some active roots have failed.
Witness: joint induction carries healthy exactness and the all-group lower bound, which
certifies every removed membership as settled. Cached-error closures only remove groups.
-/
theorem State.HealthyPendingTracks.drainReadyGroups_ofBound {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (bounded : queue.PendingBound (fun _ => True) settled)
    : queue.drainReadyGroups.1.HealthyPendingTracks work settled failed := by
  have final := State.drainReadyGroups_preserves
    (fun state => state.HealthyPendingTracks work settled failed ∧
      state.PendingBound (fun _ => True) settled)
    (by
      intro current node prior member _ _ zero
      have all := prior.2.allSettled member trivial zero
      exact ⟨(prior.1.finishGroupSuccess node all).startNewWork _,
        (prior.2.finishGroupSuccess node all).startNewWork _⟩)
    (fun _ node _ prior _ _ _ =>
      ⟨prior.1.removeGroup node.group.node.ref, prior.2.removeGroup node.group.node.ref⟩)
    ⟨tracks, bounded⟩
  exact final.1

-----------------------------------------------------------------------------------------
-- Failed source tasks cannot be members of a still-healthy group
-----------------------------------------------------------------------------------------

/-- A source-matched task cannot have a healthy contributor after its failure is recorded.
Witness: the task's exact structural owner list licenses direct group invalidation.
-/
theorem TaskMatches.not_failed_of_healthy {work : Execution.Work} {task : Task}
    (matching : TaskMatches work task) {failed : List Occurrence} {ref : NodeRef}
    (contributor : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (healthy : ¬GroupInvalidated work failed ref)
    : task.occurrence ∉ failed := by
  obtain ⟨address, payload, producer, same, known⟩ := matching.1
  intro member
  exact healthy (.task ⟨producer, payload, known⟩ contributor member)

/-- Healthy group memberships exclude every recorded source-failed task.
Witness: sound membership supplies the source-matched contributor that would invalidate
the group if its occurrence were in the failure ledger.
-/
theorem State.GroupMembershipSound.healthyMembership_not_failed {queue : State}
    {work failed} (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work) {node : GroupNode}
    (member : node ∈ queue.groupNodes)
    (healthy : ¬GroupInvalidated work failed node.group.node.ref)
    {occurrence : Occurrence} (taskMember : occurrence ∈ node.tasks)
    : occurrence ∉ failed := by
  obtain ⟨task, registered, same, contributor⟩ := sound node member occurrence taskMember
  rw [← same]
  exact (matching task registered).not_failed_of_healthy contributor healthy

/-- Recording an already-failed occurrence as settled leaves healthy counts unchanged.
Witness: such an occurrence cannot appear in a healthy group's membership list.
-/
theorem State.HealthyPendingTracks.recordFailedSettlement {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (sound : queue.GroupMembershipSound) (matching : queue.RegisteredTasksMatch work)
    (occurrence : Occurrence) (recorded : occurrence ∈ failed)
    : queue.HealthyPendingTracks work (occurrence :: settled) failed := by
  intro node member healthy
  change node.pending = unsettledCount node.tasks (occurrence :: settled)
  rw [unsettledCount_settle_absent _ _ _ (by
    intro listed
    exact sound.healthyMembership_not_failed matching member healthy listed recorded)]
  exact tracks node member healthy

-----------------------------------------------------------------------------------------
-- Healthy exactness through the executable settlement and item handlers
-----------------------------------------------------------------------------------------

/-- Failure preserves exact healthy counters in the combined outcome ledger.
Witness: the existing healthy failure theorem excludes the newly failed owners, then
membership provenance shows that recording the failed token changes no healthy count.
This covers ignored failures too, without licensing them as new error contributions.
-/
theorem State.HealthyPendingTracks.taskFailure_allOutcomes {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (accounted : queue.PendingAccounting work settled) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.HealthyPendingTracks work
        (occurrence :: settled) (occurrence :: failed) := by
  have retained := tracks.taskFailure accounted.started accounted.matching accounted.sound
    occurrence errors
  exact retained.recordFailedSettlement (accounted.sound.taskFailure occurrence errors)
    (accounted.matching.taskFailure occurrence errors) occurrence (by simp)

/-- Success preserves exact healthy counters while failed groups retain only a bound.
Witness: a rejected task is absent from healthy memberships; otherwise matched ownership
starts exact healthy debt alongside all-group safety debt. The single-pass fold and drain
discharge both, without assuming that every active root is healthy.
-/
theorem State.HealthyPendingTracks.taskSuccess_allOutcomes {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (accounted : queue.PendingAccounting work settled)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (generated : ExecutedWork work)
    (descriptors
      : ∀ node ∈ queue.groupNodes,
          ∃ dependencies,
            GroupRecordAt work node.group.node dependencies
            ∧ node.group.parent = dependencies.head?)
    (occurrence : Occurrence) (result : TaskResult) (taskNode : TaskNode)
    (found : queue.taskNode? occurrence = some taskNode) (fresh : occurrence ∉ settled)
    (freshChildren : ∀ task ∈ result.work.tasks, task.occurrence ∉ settled)
    (uniqueOwners : (taskNode.task.groups.map Execution.DeliveryNode.ref).Nodup)
    (childrenMatch : ∀ task ∈ result.work.tasks, TaskMatches work task)
    : (queue.taskSuccess occurrence result).1.HealthyPendingTracks work
        (occurrence :: settled) failed := by
  cases active : queue.taskHasHealthyOwner taskNode.task with
  | false =>
      exact tracks.taskSuccess_of_noHealthyOwner accounted.sound accounted.started
        accounted.matching supported cancelled generated descriptors found active result
  | true =>
      let stored := queue.putTaskNode { taskNode with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have storedTracks : stored.HealthyPendingTracks work settled failed := tracks
      have storedBound : stored.PendingBound (fun _ => True) settled := accounted.pending
      have storedRefs : stored.GroupRefsUnique := accounted.refs
      have storedMembers : stored.TaskMembershipsUnique := accounted.memberships
      have storedCovered : stored.TaskGroupsRegistered := accounted.taskGroups
      have storedSound : stored.GroupMembershipSound := accounted.sound
      have storedMatch : stored.RegisteredTasksMatch work := accounted.matching
      have integratedTracks := storedTracks.maybeIntegrateWork result.work freshChildren
        (some occurrence)
      have integratedBound := storedBound.maybeIntegrateWork result.work (some occurrence)
      have integratedRefs := storedRefs.maybeIntegrateWork result.work (some occurrence)
      have integratedMembers := storedMembers.maybeIntegrateWork result.work (some occurrence)
      have integratedLinks := (accounted.links.putTaskNode _).maybeIntegrateWork storedRefs
        storedCovered result.work (some occurrence)
      have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
      have integratedMatch := storedMatch.maybeIntegrateWork result.work childrenMatch
        (some occurrence)
      have member : taskNode.task ∈ integrated.tasks := by
        rw [State.maybeIntegrateWork_tasks_append]
        exact List.mem_append_left _ (accounted.started taskNode
          (List.mem_of_find?_eq_some found))
      have same : taskNode.task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp (List.find?_some
          (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
      have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch member
        (same.symm ▸ fresh)
      rw [same] at owned
      have debt : integrated.PendingDebt (fun ref => ¬GroupInvalidated work failed ref)
          (occurrence :: settled) (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
        State.PendingDebt.beginSettlement integratedTracks integratedMembers
          (fun node member _ => owned node member) fresh
      have bound := integratedBound.beginSettlement integratedMembers
        (fun node member _ => owned node member) fresh
      have final := successGroupFold_preservesSelected
        (fun ref => ¬GroupInvalidated work failed ref) (occurrence :: settled)
        taskNode.task.groups uniqueOwners (integrated, [], {}) integratedRefs debt bound
      let released := taskNode.task.groups.foldl successGroupStep (integrated, [], {})
      have releasedTracks : released.1.HealthyPendingTracks work (occurrence :: settled)
          failed := by
        intro node member healthy
        simpa [GroupNode.PendingTracks] using final.1 node member healthy
      rw [queue.taskSuccess_eq occurrence result taskNode found]
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact (releasedTracks.startNewWork _).drainReadyGroups_ofBound
        (final.2.startNewWork _)

/-- Stream item integration preserves exact healthy counters and safely drains releases.
Witness: fresh child tasks preserve exact counts during item-fold induction; the parallel
all-group bound supplies the settled-membership certificate at the final drain.
-/
theorem State.HealthyPendingTracks.streamItems_ofBound {queue : State}
    {work settled failed} (tracks : queue.HealthyPendingTracks work settled failed)
    (bounded : queue.PendingBound (fun _ => True) settled)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, task.occurrence ∉ settled)
    : (queue.streamItems stream items).1.HealthyPendingTracks work settled failed := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty }, groups ++ nonempty,
      streams ++ newWork.newStreams, values ++ [item.value])
  let invariant (current : State) := current.HealthyPendingTracks work settled failed ∧
    current.PendingBound (fun _ => True) settled
  have stepFacts (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      (item : StreamItem) (prior : invariant acc.1)
      (freshItem : ∀ task ∈ item.work.tasks, task.occurrence ∉ settled)
      : invariant (step acc item).1 := by
    obtain ⟨current, groups, streams, values⟩ := acc
    have integratedTracks := prior.1.maybeIntegrateWork item.work freshItem
    have integratedBound := prior.2.maybeIntegrateWork item.work
    exact ⟨(integratedTracks.pruneEmptyGroups _).startNewWork _,
      (integratedBound.pruneEmptyGroups _).startNewWork _⟩
  have loop (more : List StreamItem) (included : more.Subset items)
      (acc : State × List Execution.DeliveryNode
        × List Execution.DeliveryNode × List StreamItemValue)
      (prior : invariant acc.1) : invariant (more.foldl step acc).1 := by
    induction more generalizing acc with
    | nil => exact prior
    | cons item rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (stepFacts acc item prior (fresh item (included List.mem_cons_self)))
  dsimp only [State.streamItems]
  split
  · exact tracks
  · have final := loop items (fun _ member => member) (queue, [], [], []) ⟨tracks, bounded⟩
    exact final.1.drainReadyGroups_ofBound final.2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
