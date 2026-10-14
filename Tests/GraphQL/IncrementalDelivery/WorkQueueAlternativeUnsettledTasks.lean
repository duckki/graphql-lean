import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningTaskProgress

/-! Unstarted tasks retain their live memberships or receive actual last-owner aborts.
The universal local proof roots are audited separately from these small executable checks.
-/

namespace AlternativeUnsettledTaskChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

private def occurrence : WorkQueueSemantics.Occurrence := .executionGroup [0]
private def node : Execution.DeliveryNode := { ref := 0, path := [] }

private def owner : ReferenceWorkQueue.GroupNode :=
  { group := { node }, tasks := [occurrence], pending := 1 }

private def closing : ReferenceWorkQueue.GroupNode :=
  { group := { node := { ref := 1, path := [] } }, childGroups := [0] }

private def queue : ReferenceWorkQueue.State :=
  {
    groupNodes := [owner, closing],
    rootGroups := [1],
    tasks := [{ occurrence, groups := [node] }]
  }

example : queue.taskNode? occurrence = none := by rfl

-- The linked unstarted task prevents its owner's empty-shell pruning.
example
    : 0
      ∈ (queue.pruneEmptyGroups [node]).1.groupNodes.map
          (fun group => group.group.node.ref) := by
  cbv
  exact List.mem_cons_self

-- Publishing a taskless parent does not remove the child's unfinished membership.
example
    : 0
      ∈ (queue.finishGroupSuccess closing).1.groupNodes.map
          (fun group => group.group.node.ref) := by
  cbv
  exact List.mem_cons_self

-- Actual failed removal aborts the last-owner task without starting it.
example : (({ queue } : State).removeGroup node.ref).2 = [.task occurrence] := by
  cbv

example
    : (({ queue } : State).finishGroupFailure owner 1).2.2.flatMap CleanupTarget.effects
      = [.abortTask occurrence] := by
  cbv

#print axioms pruneEmptyGroups_linkedOwner_present
#print axioms finishGroupSuccess_linkedOwner_present
#print axioms drain_unsettledTask_ownerCut
#print axioms PruningGroups.linkedOwnerOrAbort
#print axioms failureFrontier_task

end AlternativeUnsettledTaskChecks
