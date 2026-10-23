import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerRelease

/-! Successful contributor accounting using actual cancellation markers and consumed successes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- The successful contributor pass preserves uncancelled owner links and pending bounds.
Witness: all-owner decrement debt licenses each successful flush, independently of
failure-notification consumption.
-/
theorem State.UncancelledTaskAccounting.successGroupFold
    {queue : State} {settled : List Occurrence}
    (accounted : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    (uniqueOwners : (groups.map Execution.DeliveryNode.ref).Nodup)
    (debt
      : queue.PendingDebtBound (fun _ => True) settled
          (groups.map Execution.DeliveryNode.ref))
    : let released := groups.foldl successGroupStep (queue, [], {})
      released.1.UncancelledTaskAccounting settled
      ∧ released.1.PendingBound (fun _ => True) settled
      ∧ released.1.GroupRefsUnique := by
  let invariant (current : State) :=
    current.GroupRefsUnique ∧ current.UncancelledTaskAccounting settled
  have preserved := successGroupFold_preservesBound (fun _ => True) settled invariant
    (fun _ valid => valid.1) (by intros; trivial)
    (by
      intro current node prior found
      exact ⟨prior.1.putGroupNode _, prior.2.putGroupNodeSameTasks prior.1 node
        (List.mem_of_find?_eq_some found) _ rfl rfl⟩)
    (by
      intro current node remaining prior counts member active zero all
      exact ⟨prior.1.finishGroupSuccess node,
        prior.2.finishSettledGroupSuccess prior.1 node member all⟩)
    groups uniqueOwners (queue, [], {}) ⟨unique, accounted⟩ debt
  exact ⟨preserved.1.2, preserved.2, preserved.1.1⟩

/-- Successful settlement, startup and draining preserve the same success-only coordinate. -/
theorem State.UncancelledTaskAccounting.successGroupFold_drain
    {queue : State} {settled : List Occurrence}
    (accounted : queue.UncancelledTaskAccounting settled) (unique : queue.GroupRefsUnique)
    (groups : List Execution.DeliveryNode)
    (uniqueOwners : (groups.map Execution.DeliveryNode.ref).Nodup)
    (debt
      : queue.PendingDebtBound (fun _ => True) settled
          (groups.map Execution.DeliveryNode.ref))
    (available : List (Occurrence × Nat) := [])
    : let released := groups.foldl successGroupStep (queue, [], {})
      ((released.1.startNewWork released.2.2 available).1.drainReadyGroups
        available).1.UncancelledTaskAccounting
        settled := by
  have preserved := accounted.successGroupFold unique groups uniqueOwners debt
  let released := groups.foldl successGroupStep (queue, [], {})
  exact (preserved.1.startNewWork released.2.2 available).drainReadyGroups
    (preserved.2.2.startNewWork _ available)
    (preserved.2.1.startNewWork _ available) available

/-- Integration reserves the successful producer's exact remaining decrement budget.
Witness: registration retains the producer descriptor and complete live memberships;
source freshness turns the all-owner lower bound into one token owed per contributor.
-/
theorem State.PendingAccounting.taskSuccess_integratedDebt
    {queue : State} {work : Execution.Work} {settled : List Occurrence}
    (pending : queue.PendingAccounting work settled)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ settled)
    : let stored := queue.putTaskNode { taskNode with value := some result.value }
      (stored.maybeIntegrateWork result.work (some occurrence)).1.PendingDebtBound
        (fun _ => True) (occurrence :: settled)
        (taskNode.task.groups.map Execution.DeliveryNode.ref) := by
  let stored := queue.putTaskNode { taskNode with value := some result.value }
  let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
  have storedRefs : stored.GroupRefsUnique := pending.refs
  have storedCovered : stored.TaskGroupsRegistered := pending.taskGroups
  have storedCounts : stored.PendingBound (fun _ => True) settled := pending.pending
  have storedMembers : stored.TaskMembershipsUnique := pending.memberships
  have storedSound : stored.GroupMembershipSound := pending.sound
  have storedMatch : stored.RegisteredTasksMatch work := pending.matching
  have integratedLinks := (pending.links.putTaskNode _).maybeIntegrateWork
    storedRefs storedCovered result.work (some occurrence)
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
      (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
    integratedCounts.beginSettlement
      integratedMembers (fun node member _ => owned node member) fresh
  exact debt

/-- A successful started task preserves uncancelled owners through its actual handler.
The success-only pending ledger supplies safe decrement debt; child availability is the
local registration certificate, independent of cached failure-notification consumption.
-/
theorem State.UncancelledTaskAccounting.taskSuccess_ofPendingAccounting
    {queue : State} {work : Execution.Work} {settled : List Occurrence}
    (accounted : queue.UncancelledTaskAccounting settled)
    (pending : queue.PendingAccounting work settled) (generated : ExecutedWork work)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (taskNode : TaskNode) (found : queue.taskNode? occurrence = some taskNode)
    (fresh : occurrence ∉ settled)
    (available
      : ∀ task ∈ result.work.tasks,
        ∀ ref ∈ task.groups.map Execution.DeliveryNode.ref,
          let stored := queue.putTaskNode {taskNode with value := some result.value}
          ref ∉ (stored.addGroups result.work.groups).1.cancelledGroups
          → ref
            ∈ (stored.addGroups result.work.groups).1.groupNodes.map
                (fun node => node.group.node.ref))
    (failuresAvailable : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result failuresAvailable).1.UncancelledTaskAccounting
        (occurrence :: settled) := by
  rw [queue.taskSuccess_eq occurrence result taskNode found failuresAvailable]
  have storedRefs : (queue.putTaskNode
      { taskNode with value := some result.value }).GroupRefsUnique := pending.refs
  have registered := pending.started taskNode (List.mem_of_find?_eq_some found)
  have debt := pending.taskSuccess_integratedDebt occurrence result matching taskNode found fresh
  have integratedOwners := (accounted.putTaskNode
    { taskNode with value := some result.value }).maybeIntegrateWork_of_present storedRefs
    result.work (some occurrence) available
  have settledOwners := integratedOwners.weakenSettled (after := occurrence :: settled)
    (by intro task member; simp [member])
  exact settledOwners.successGroupFold_drain
    (storedRefs.maybeIntegrateWork result.work (some occurrence)) taskNode.task.groups
    (pending.matching.contributorsNodup generated registered) debt failuresAvailable

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
