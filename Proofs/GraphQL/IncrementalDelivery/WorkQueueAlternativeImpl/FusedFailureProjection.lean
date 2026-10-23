import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFusedRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalGuards

/-! The actual failed-task owner fold projects to the reference failure handler. The input
task is settled before visiting owners; last-owner cleanup is returned by those actual
removals, independently of the wire-event projection.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

theorem fusedFailureGroupStep_projection {work : Work} {parents : Nat → NodeRefs}
    (errors : Nat) (acc : State × List WorkQueueEvent × List CleanupTarget)
    (frame : acc.1.queue.TaskOwnerFrame work) (forest : acc.1.queue.RemovalForest parents)
    (group : Execution.DeliveryNode)
    : let next := fusedFailureGroupStep errors acc group
      (next.1.queue, next.2.1)
        = ReferenceWorkQueue.failureGroupStep errors (acc.1.queue, acc.2.1) group
      ∧ next.1.queue.TaskOwnerFrame work
      ∧ next.1.queue.RemovalForest parents := by
  unfold fusedFailureGroupStep ReferenceWorkQueue.failureGroupStep
  dsimp only
  cases found : acc.1.queue.groupNode? group.ref with
  | none => exact ⟨rfl, frame, forest⟩
  | some node =>
      simp only
      split
      · have same := FusedRemovalProjection_holds acc.1 work parents node.group.node.ref acc.2.2
          frame.matching frame.sound forest frame.removalTaskFrame
        refine ⟨?_, ?_, ?_⟩
        · change ((acc.1.removeGroup node.group.node.ref acc.2.2).1.queue, _) = _
          rw [same]
          rfl
        · change (acc.1.removeGroup node.group.node.ref acc.2.2).1.queue.TaskOwnerFrame work
          rw [same]
          exact frame.removeGroup node.group.node.ref
        · change (acc.1.removeGroup node.group.node.ref acc.2.2).1.queue.RemovalForest parents
          rw [same]
          exact forest.removeGroup node.group.node.ref
      · exact ⟨rfl, frame, forest⟩

theorem fusedFailureGroupFold_projection {work : Work} {parents : Nat → NodeRefs}
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (frame : acc.1.queue.TaskOwnerFrame work) (forest : acc.1.queue.RemovalForest parents)
    : let final := groups.foldl (fusedFailureGroupStep errors) acc
      (final.1.queue, final.2.1)
      = groups.foldl (ReferenceWorkQueue.failureGroupStep errors)
          (acc.1.queue, acc.2.1) := by
  induction groups generalizing acc with
  | nil => rfl
  | cons group rest ih =>
      have step := fusedFailureGroupStep_projection errors acc frame forest group
      have next := ih (fusedFailureGroupStep errors acc group) step.2.1 step.2.2
      rw [step.1] at next
      exact next

/-- Exact actual failure-handler kernel/wire projection; targets and effects remain the
new inline cleanup observations, not a reintroduced reference observer algorithm.
-/
theorem State.taskFailure_projection {state : State} {work : Work}
    {parents : Nat → NodeRefs} (frame : state.queue.TaskOwnerFrame work)
    (forest : state.queue.RemovalForest parents) (occurrence : Occurrence) (errors : Nat)
    (targets : List CleanupTarget := [])
    : (
        (state.taskFailure occurrence errors targets).1.queue,
        (state.taskFailure occurrence errors targets).2.1
      )
      = state.queue.taskFailure occurrence errors := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskFailure, ReferenceWorkQueue.State.taskFailure, found]
  | some node =>
      rw [ReferenceWorkQueue.State.taskFailure_eq occurrence errors node found]
      simp only [State.taskFailure, found]
      exact fusedFailureGroupFold_projection errors node.task.groups
        ({ state with queue := state.queue.putTaskNode { node with rejection := some errors } }, [], targets)
        (frame.putExistingTaskNode node (List.mem_of_find?_eq_some found)
          { node with rejection := some errors } rfl)
        ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
