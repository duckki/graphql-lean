import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulHealthFold
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAncestorHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay

/-! Source-valid task success preserves health through the single-pass owner fold. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
namespace ReleaseHealth

/-- Actual successful task handling preserves the joint health frame and its output.
Witness: valid fixed outcomes separate successful settlements from failures; the successful
pending ledger bounds all flushed memberships. Registration, owner settlement, activation,
and rejection draining retain their actual order.
-/
theorem HealthFrame.taskSuccess {queue work parents failed before occurrence result}
    (prior : HealthFrame queue work parents failed)
    (ledger : queue.PendingAccounting work (GraphEvent.groupSettlements before))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before)
    (included : failed.Subset (GraphEvent.failureSettlements before))
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (available : List (Occurrence × Nat) := [])
    : HealthFrame (queue.taskSuccess occurrence result available).1 work parents failed
      ∧ SuccessfulGroupsHealthy work failed
          (queue.taskSuccess occurrence result available).2.1
      ∧ GroupNoticeAncestorsHealthy work failed
          (queue.taskSuccess occurrence result available).2.1
      ∧ GroupFailureAncestorsHealthy work failed
          (queue.taskSuccess occurrence result available).2.1 := by
  have failedKnown : ∀ task ∈ failed, ∃ owners producer payload,
      TaskAt work task owners producer payload ∧ payload.failure.isSome = true := by
    intro task member
    obtain ⟨owners, producer, path, errors, known⟩ :=
      valid.failureSettlements_known task (included member)
    exact ⟨owners, producer, _, known, rfl⟩
  cases found : queue.taskNode? occurrence with
  | none =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [State.taskSuccess, found] using prior
      · simpa only [State.taskSuccess, found] using SuccessfulGroupsHealthy.nil work failed
      · simp [State.taskSuccess, found, GroupNoticeAncestorsHealthy]
      · exact .of_noFailures (by simp [State.taskSuccess, found])
  | some taskNode =>
      have nodeMember := List.mem_of_find?_eq_some found
      have unsettled : occurrence ∉ GraphEvent.groupSettlements before := by
        intro member
        exact fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.groupSettlements_subsetIdentities before member)
      have notFailed : occurrence ∉ failed := by
        intro member
        exact valid.succeeds_not_failureSettlements
          (matching.successes_succeed (by simp [GraphEvent.successes])) (included member)
      have safe : ∀ task ∈ occurrence :: GraphEvent.groupSettlements before, task ∉ failed := by
        intro task member recorded
        rcases List.mem_cons.mp member with rfl | earlier
        · exact notFailed recorded
        · exact valid.succeeds_not_failureSettlements (valid.groupSettlements_succeed earlier)
            (included recorded)
      have children : ∀ task ∈ result.work.tasks, TaskMatches work task := by
        intro task member
        obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          matching.childTask_groupsExact member⟩
      let stored := queue.putTaskNode { taskNode with value := some result.value }
      let integrated := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have storedFrame : HealthFrame stored work parents failed :=
        ⟨prior.groups, prior.links, prior.counts.putTaskNode found _ rfl (fun rejected => rejected),
          prior.retired, prior.roots, prior.refs, prior.sound, prior.tasks, prior.live⟩
      have prepared := storedFrame.maybeIntegrateWork result.work
        (fun _ member => matching.taskChildGroups_recordAt member)
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member)
        children (some occurrence) generated canonical
        ((ledger.registration.children taskNode.task (ledger.started taskNode nodeMember)).sourceChild
          (State.taskNode?_some found).2 matching).parentRefs
      have storedRefs : stored.GroupRefsUnique := ledger.refs
      have storedMembers : stored.TaskMembershipsUnique := ledger.memberships
      have storedCounts : stored.PendingBound (fun _ => True)
          (GraphEvent.groupSettlements before) := ledger.pending
      have storedCovered : stored.TaskGroupsRegistered := ledger.taskGroups
      have storedSound : stored.GroupMembershipSound := ledger.sound
      have storedMatch : stored.RegisteredTasksMatch work := ledger.matching
      have integratedLinks : integrated.UnsettledTaskLinks (GraphEvent.groupSettlements before) :=
        (ledger.links.putTaskNode _).maybeIntegrateWork storedRefs storedCovered result.work
          (some occurrence)
      have integratedCounts := storedCounts.maybeIntegrateWork result.work (some occurrence)
      have integratedMembers := storedMembers.maybeIntegrateWork result.work (some occurrence)
      have integratedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
      have integratedMatch := storedMatch.maybeIntegrateWork result.work children (some occurrence)
      have registered : taskNode.task ∈ integrated.tasks := by
        rw [State.maybeIntegrateWork_tasks_append]
        exact List.mem_append_left _ (ledger.started taskNode nodeMember)
      have same : taskNode.task.occurrence = occurrence :=
        (occurrence_beq_iff_eq _ _).mp (List.find?_some
          (p := fun candidate : TaskNode => candidate.task.occurrence == occurrence) found)
      have owned := integratedLinks.ownedExactlyBy integratedSound integratedMatch registered
        (same.symm ▸ unsettled)
      rw [same] at owned
      have debt : integrated.PendingDebtBound (fun _ => True)
          (occurrence :: GraphEvent.groupSettlements before)
          (taskNode.task.groups.map Execution.DeliveryNode.ref) :=
        integratedCounts.beginSettlement integratedMembers
          (fun node member _ => owned node member) unsettled
      have ownersUnique := ledger.matching.contributorsNodup generated
        (ledger.started taskNode nodeMember)
      have folded := prepared.successGroupFold generated canonical failedKnown safe
        taskNode.task.groups ownersUnique debt
      have active := folded.1.startNewWork _ folded.2.1 available
      have bounded := folded.2.2.2.startNewWork
        (taskNode.task.groups.foldl successGroupStep (integrated, [], {})).2.2 available
      have drained := active.drainReadyGroups generated canonical failedKnown bounded safe available
      rw [queue.taskSuccess_eq occurrence result taskNode found available]
      exact ⟨
        drained.1,
        folded.2.2.1.append drained.2,
        (State.successGroupFold_noticeAncestorHealth folded.2.1).append
          (active.drainReadyGroups_noticeHealth generated canonical failedKnown bounded
            safe available),
        (GroupFailureAncestorsHealthy.successGroupFold taskNode.task.groups
          (_, [], {}) (.of_noFailures (by simp))).append
          (active.drainReadyGroups_failureAncestorHealth generated canonical failedKnown
            available)
      ⟩

end ReleaseHealth
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
