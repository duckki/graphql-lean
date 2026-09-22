import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingHealthy
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildLinks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAccounting

/-! Healthy owner existence through single-pass release and recursive draining. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Healthy registered owners survive the whole contributor pass and recursive drain.
`settled` already includes the current task outcome; `groups` still owe its decrements.
Witness: all-owner decrement debt justifies each successful flush, while supported caches
and canonical metadata justify failed drain closures. No active-root health is assumed.
-/
theorem State.HealthyRegisteredTaskAccounting.successGroupFold_drain
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    {parents : Nat → Keys}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (unique : queue.GroupKeysUnique)
    (supported : queue.CachedFailuresSupported work failed)
    (tasksMatch : queue.RegisteredTasksMatch work)
    (generated : ExecutedWork work)
    (links : queue.ChildLinksCanonical parents)
    (matching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (groups : List Execution.DeliveryNode)
    (uniqueOwners : (groups.map Execution.DeliveryNode.key).Nodup)
    (debt
      : queue.PendingDebtBound (fun _ => True) settled
          (groups.map Execution.DeliveryNode.key))
    : let released := groups.foldl successGroupStep (queue, [], {})
      (released.1.startNewWork
        released.2.2).drainReadyGroups.1.HealthyRegisteredTaskAccounting
        work settled failed := by
  let invariant (current : State) :=
    current.GroupKeysUnique ∧ current.HealthyRegisteredTaskAccounting work settled failed
      ∧ current.CachedFailuresSupported work failed ∧ current.ChildLinksCanonical parents
      ∧ current.GroupNodesMatchWork work ∧ current.RegisteredTasksMatch work
  have initial : invariant queue :=
    ⟨unique, accounted, supported, links, matching, tasksMatch⟩
  have preserved := successGroupFold_preservesBound (fun _ => True) settled invariant
    (fun _ valid => valid.1) (by intros; trivial)
    (by
      intro current node prior found
      have member := List.mem_of_find?_eq_some found
      exact ⟨prior.1.putGroupNode _,
        prior.2.1.putGroupNodeSameTasks prior.1 node member _ rfl rfl,
        prior.2.2.1.putGroupNode _ (prior.2.2.1 node member),
        prior.2.2.2.1.putGroupNode _ (prior.2.2.2.1 node member),
        prior.2.2.2.2.1.putGroupNode _ (prior.2.2.2.2.1 node member),
        prior.2.2.2.2.2.putGroupNode _⟩)
    (by
      intro current node remaining prior counts member active zero all
      exact ⟨prior.1.finishGroupSuccess node,
        prior.2.1.finishSettledGroupSuccess prior.1 node member all,
        prior.2.2.1.finishGroupSuccess node, prior.2.2.2.1.finishGroupSuccess node,
        prior.2.2.2.2.1.finishGroupSuccess node,
        prior.2.2.2.2.2.finishGroupSuccess node⟩)
    groups uniqueOwners (queue, [], {}) initial debt
  let released := groups.foldl successGroupStep (queue, [], {})
  have counts : released.1.PendingBound (fun _ => True) settled := preserved.2
  have activated := counts.startNewWork released.2.2
  apply (preserved.1.2.1.startNewWork released.2.2).drainReadyGroups
    (unique := preserved.1.1.startNewWork _)
    (supported := preserved.1.2.2.1.startNewWork _)
    (tasksMatch := preserved.1.2.2.2.2.2.startNewWork _) (generated := generated)
    (links := preserved.1.2.2.2.1.startNewWork _)
    (matching := preserved.1.2.2.2.2.1.startNewWork _) (canonical := canonical)
  exact activated

/-- A successful started task preserves every healthy registered owner's existence and
membership through the actual handler, including its final recursive drain.
Witness: all-group lower bounds establish safe decrement debt; integration availability
covers new tasks, and source-matched metadata supports success/failure closures. Rejected
settlements remove only the now-settled task's memberships and integrate no child work.
Availability is an internal queue invariant still to be derived along generated replay.
-/
theorem State.HealthyRegisteredTaskAccounting.taskSuccess_ofPendingAccounting
    {queue : State} {work : Execution.Work} {settled failed : List Occurrence}
    {parents : Nat → Keys}
    (accounted : queue.HealthyRegisteredTaskAccounting work settled failed)
    (pending : queue.PendingAccounting work settled)
    (supported : queue.CachedFailuresSupported work failed)
    (cancelled : queue.CancelledRecordsSupported work failed)
    (links : queue.ChildLinksCanonical parents)
    (groupMatching : queue.GroupNodesMatchWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (generated : ExecutedWork work)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ settled)
    (available : queue.ChildGroupsAvailable work failed result.work)
    : (queue.taskSuccess occurrence result).1.HealthyRegisteredTaskAccounting
        work (occurrence :: settled) failed := by
  rw [queue.taskSuccess_eq occurrence result taskNode found]
  split
  · exact (accounted.weakenSettled (after := occurrence :: settled)
      (by intro task member; simp [member])).removeSettledTask occurrence (by simp)
  let stored := queue.putTaskNode { taskNode with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedKeys : stored.GroupKeysUnique := pending.keys
  have storedCovered : stored.TaskGroupsRegistered := pending.taskGroups
  have storedCounts : stored.PendingBound (fun _ => True) settled := pending.pending
  have storedMembers : stored.TaskMembershipsUnique := pending.memberships
  have storedSound : stored.GroupMembershipSound := pending.sound
  have storedMatch : stored.RegisteredTasksMatch work := pending.matching
  have storedSupport : stored.CachedFailuresSupported work failed := supported
  have storedLinks : stored.ChildLinksCanonical parents := links
  have storedGroups : stored.GroupNodesMatchWork work := groupMatching
  have integratedLinks := (pending.links.putTaskNode _).maybeIntegrateWork
    storedKeys storedCovered result.work (some occurrence)
  have integratedCounts := storedCounts.maybeIntegrateWork result.work (some occurrence)
  have integratedMembers := storedMembers.maybeIntegrateWork result.work (some occurrence)
  have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
  have integratedMatch := storedMatch.maybeIntegrateWork result.work (by
    intro task member
    obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
    exact ⟨⟨address, payload, some occurrence, same, known⟩,
      matching.childTask_groupsExact member⟩) (some occurrence)
  have registered := pending.started taskNode (List.mem_of_find?_eq_some found)
  have taskMember : taskNode.task ∈ integrated.tasks := by
    rw [State.maybeIntegrateWork_tasks_append]
    exact List.mem_append_left _ registered
  have same : taskNode.task.occurrence = occurrence :=
    (occurrence_beq_iff_eq _ _).mp (List.find?_some
      (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
  have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch taskMember
    (same.symm ▸ fresh)
  rw [same] at owned
  have debt : integrated.PendingDebtBound (fun _ => True) (occurrence :: settled)
      (taskNode.task.groups.map Execution.DeliveryNode.key) :=
    integratedCounts.beginSettlement
      integratedMembers (fun node member _ => owned node member) fresh
  have integratedOwners := (accounted.putTaskNode _).maybeIntegrateWork storedKeys
    result.work (some occurrence) matching.childTasksCovered available cancelled
    generated (by
      intro task member
      obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
      exact ⟨⟨address, payload, some occurrence, same, known⟩,
        matching.childTask_groupsExact member⟩)
    (by
      intro group member
      obtain ⟨dependencies, known⟩ := matching.taskChildGroups_recordAt member
      exact ⟨dependencies, known,
        (matching.taskChildGroups_parentCanonical canonical member).trans
          (congrArg List.head? (canonical _ _ known)).symm⟩)
  have settledOwners := integratedOwners.weakenSettled (after := occurrence :: settled)
    (by intro task member; simp [member])
  apply settledOwners.successGroupFold_drain
    (unique := storedKeys.maybeIntegrateWork result.work (some occurrence))
    (supported := storedSupport.maybeIntegrateWork result.work (some occurrence))
    (tasksMatch := integratedMatch) (generated := generated)
    (links := storedLinks.maybeIntegrateWork result.work
      (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
      (some occurrence))
    (matching := storedGroups.maybeIntegrateWork result.work
      (fun _ member => matching.taskChildGroups_recordAt member) (some occurrence))
    (canonical := canonical) (groups := taskNode.task.groups)
    (uniqueOwners := pending.matching.contributorsNodup generated registered)
    (debt := debt)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
