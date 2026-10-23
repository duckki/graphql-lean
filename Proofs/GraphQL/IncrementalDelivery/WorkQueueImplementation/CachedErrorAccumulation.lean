import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureOutput

/-! Failure processing retains selected task rejections without accumulating group errors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Owner cleanup leaves every surviving rejected computation unchanged.
Witness: the failure-owner fold only filters task nodes.
-/
theorem failureGroupFold_taskRejections_unchanged (errors : Nat)
    (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
    {node : TaskNode}
    (member : node ∈ (groups.foldl (failureGroupStep errors) acc).1.taskNodes)
    : node ∈ acc.1.taskNodes :=
  failureGroupFold_taskNodes_subset errors groups acc member

/-- A surviving node is old or the selected task with its rejection replaced exactly.
Witness: task lookup, the single rejection update, and deletion-only owner processing.
No error count is added to another computation or stored on a group.
-/
theorem State.taskFailure_startedOldOrRejected (queue : State) (occurrence : Occurrence)
    (errors : Nat) {node : TaskNode}
    (member : node ∈ (queue.taskFailure occurrence errors).1.taskNodes)
    : node ∈ queue.taskNodes
      ∨ ∃ old ∈ queue.taskNodes, node = { old with rejection := some errors } := by
  cases found : queue.taskNode? occurrence with
  | none => exact Or.inl (by simpa [State.taskFailure, found] using member)
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found] at member
      have updated := failureGroupFold_taskNodes_subset errors task.task.groups
        (queue.putTaskNode { task with rejection := some errors }, []) member
      obtain ⟨old, live, same⟩ := List.mem_map.mp updated
      split at same
      · exact Or.inr ⟨task, List.mem_of_find?_eq_some found, same.symm⟩
      · exact Or.inl (same ▸ live)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
