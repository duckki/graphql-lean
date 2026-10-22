import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskRemoval
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedCleanupTargets

/-! Actual failed-owner folds preserve unrejected task ownership or request cleanup. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (NodeRefs Occurrence)

theorem failureFold_targets (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    : acc.2.2.Subset (groups.foldl (fusedFailureGroupStep errors) acc).2.2 := by
  induction groups generalizing acc with
  | nil => exact List.Subset.refl _
  | cons group rest ih =>
      apply List.Subset.trans (l₂ := (fusedFailureGroupStep errors acc group).2.2) ?_ (ih _)
      unfold fusedFailureGroupStep
      split
      · exact List.Subset.refl _
      · split
        · exact (FusedRemovalSafety_holds acc.1 _ acc.2.2).1
        · exact List.Subset.refl _

theorem failureFold_unsettledTask {work : Work} {parents : Nat → NodeRefs}
    (errors : Nat) (groups : List Execution.DeliveryNode)
    (acc : State × List Execution.WorkQueueEvent × List CleanupTarget)
    (frame : acc.1.queue.TaskOwnerFrame work) (forest : acc.1.queue.RemovalForest parents)
    (task : ReferenceWorkQueue.Task)
    (catalogue : acc.1.queue.task? task.occurrence = some task)
    (links
      : acc.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref))
    (owned
      : ∃ owner ∈ task.groups, ∃ group, acc.1.queue.groupNode? owner.ref = some group)
    (unique : acc.2.2.Nodup)
    (unrejected
      : acc.1.queue.TaskRejectionsSatisfy (fun rejected _ => rejected ≠ task.occurrence))
    : let next := groups.foldl (fusedFailureGroupStep errors) acc
      (next.1.queue.TaskLinkedOn task.occurrence
          (task.groups.map Execution.DeliveryNode.ref)
        ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
      ∨ .task task.occurrence ∈ next.2.2 := by
  induction groups generalizing acc with
  | nil => exact .inl ⟨links, owned⟩
  | cons group rest ih =>
      let next := fusedFailureGroupStep errors acc group
      have projected := fusedFailureGroupStep_projection errors acc frame forest group
      have nextUnique := fusedFailureGroupStep_targets errors acc group unique
      have nextCatalogue : next.1.queue.task? task.occurrence = some task := by
        rw [show next.1.queue = (ReferenceWorkQueue.failureGroupStep errors (acc.1.queue, acc.2.1) group).1
          from congrArg Prod.fst projected.1]
        unfold ReferenceWorkQueue.failureGroupStep
        dsimp only
        split
        · exact catalogue
        · split <;> exact catalogue
      have nextUnrejected : next.1.queue.TaskRejectionsSatisfy
          (fun rejected _ => rejected ≠ task.occurrence) := by
        rw [show next.1.queue =
          (ReferenceWorkQueue.failureGroupStep errors (acc.1.queue, acc.2.1) group).1
            from congrArg Prod.fst projected.1]
        unfold ReferenceWorkQueue.failureGroupStep
        dsimp only
        split
        · exact unrejected
        · split
          · exact unrejected.removeGroup _
          · exact unrejected
      have step : (next.1.queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.ref)
          ∧ ∃ owner ∈ task.groups, ∃ group, next.1.queue.groupNode? owner.ref = some group)
          ∨ .task task.occurrence ∈ next.2.2 := by
        unfold next fusedFailureGroupStep
        cases found : acc.1.queue.groupNode? group.ref with
        | none => exact .inl ⟨links, owned⟩
        | some node =>
            simp only
            split
            · rcases FusedRemovalTaskProgress_holds acc.1 node.group.node.ref task acc.2.2
                  unique catalogue links owned unrejected with kept | aborted
              · exact .inl kept
              · have listed : CleanupTarget.task task.occurrence ∈
                    ((acc.1.removeGroup node.group.node.ref acc.2.2).2.flatMap
                      CleanupTarget.effects).filterMap HostEffect.cleanupStart? :=
                  List.mem_filterMap.mpr ⟨HostEffect.abortTask task.occurrence, aborted, rfl⟩
                rw [cleanupEffects_starts] at listed
                exact .inr listed
            · exact .inl ⟨links, owned⟩
      rw [List.foldl_cons]
      rcases step with kept | requested
      · exact ih next projected.2.1 projected.2.2 nextCatalogue kept.1 kept.2 nextUnique nextUnrejected
      · exact .inr (failureFold_targets errors rest next requested)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
