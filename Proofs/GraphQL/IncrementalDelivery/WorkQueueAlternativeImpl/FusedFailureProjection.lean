import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFusedRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalGuards

/-! The actual failed-task owner fold projects to the reference failure handler. The input
task is settled before visiting owners; last-owner cleanup is returned by those actual
removals, independently of the wire-event projection.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (NodeRefs Occurrence)
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)

def fusedFailureGroupStep (errors : Nat)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : State × List WorkQueueEvent × List CleanupTarget :=
  match acc.1.queue.groupNode? group.ref with
  | none => acc
  | some node =>
      if acc.1.queue.rootGroups.contains group.ref then
        let reduced := acc.1.finishGroupFailure node errors acc.2.2
        (reduced.1, acc.2.1 ++ [reduced.2.1], reduced.2.2)
      else
        let updated :=
          {
            node with
              pending := node.pending - 1
              failure := some (node.failure.getD 0 + errors)
          }
        ({ acc.1 with queue := acc.1.queue.putGroupNode updated }, acc.2.1, acc.2.2)

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
      · exact ⟨rfl, frame.putGroupNodeSameTasks node (List.mem_of_find?_eq_some found) _ rfl rfl,
          forest.putCounters frame.keys found (node.pending - 1) (some (node.failure.getD 0 + errors))⟩

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
    : (
        (state.taskFailure occurrence errors).1.queue,
        (state.taskFailure occurrence errors).2.1
      )
      = state.queue.taskFailure occurrence errors := by
  cases found : state.queue.taskNode? occurrence with
  | none => simp only [State.taskFailure, ReferenceWorkQueue.State.taskFailure, found]
  | some node =>
      rw [ReferenceWorkQueue.State.taskFailure_eq occurrence errors node found]
      simp only [State.taskFailure, found]
      split
      · rfl
      · exact fusedFailureGroupFold_projection errors node.task.groups
          ({ state with queue := state.queue.removeTask occurrence }, [], [])
          (frame.removeTask occurrence) (forest.removeTask occurrence)

private theorem fusedFailureGroupStep_stopped (errors : Nat)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : (fusedFailureGroupStep errors acc group).1.stopped = acc.1.stopped := by
  unfold fusedFailureGroupStep
  split
  · rfl
  · split
    · exact acc.1.removeGroup_stopped _ _
    · rfl

theorem State.taskFailure_stopped (state : State) (occurrence : Occurrence) (errors : Nat)
    : (state.taskFailure occurrence errors).1.stopped = state.stopped := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × List CleanupTarget)
      : (groups.foldl (fusedFailureGroupStep errors) acc).1.stopped = acc.1.stopped := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        exact (ih _).trans (fusedFailureGroupStep_stopped errors acc group)
  unfold State.taskFailure
  split
  · rfl
  · dsimp only
    split
    · rfl
    · exact loop _ _

private theorem fusedFailureGroupStep_terminated (errors : Nat)
    (acc : State × List WorkQueueEvent × List CleanupTarget)
    (group : Execution.DeliveryNode)
    : (fusedFailureGroupStep errors acc group).1.queue.terminated
      = acc.1.queue.terminated := by
  unfold fusedFailureGroupStep
  split
  · rfl
  · split
    · exact acc.1.removeGroup_terminated _ _
    · rfl

theorem State.taskFailure_terminated (state : State) (occurrence : Occurrence)
    (errors : Nat)
    : (state.taskFailure occurrence errors).1.queue.terminated
      = state.queue.terminated := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × List CleanupTarget)
      : (groups.foldl (fusedFailureGroupStep errors) acc).1.queue.terminated
        = acc.1.queue.terminated := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        exact (ih _).trans (fusedFailureGroupStep_terminated errors acc group)
  unfold State.taskFailure
  split
  · rfl
  · dsimp only
    split
    · rfl
    · exact loop _ _

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
