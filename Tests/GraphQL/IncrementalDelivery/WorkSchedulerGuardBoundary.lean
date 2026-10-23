import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration

/-! Parent-first traversal cancels descendants of a cancelled missing parent. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerGuardBoundary
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : Group := ⟨⟨1, [], none⟩, some 0⟩
private def child : Group := ⟨⟨2, [], none⟩, some 1⟩

private def queue : State :=
  (({ registeredGroups := [0], cancelledGroups := [0] } : State).addGroups
    [child, parent]).1

/-- Candidate encounter order still installs the parent first and cancels both records.
Witness: recursive registration visits the parent before considering the child. -/
theorem child_first_state
    : queue.groupNodes = []
      ∧ queue.cancelledGroups = [0, 1, 2]
      ∧ queue.groupNode? parent.node.ref = none := by cbv

/-- A refused parent is retired and carries its inherited cancellation marker. -/
theorem new_retirement_marked
    : queue.RetiredGroup parent.node.ref ∧ parent.node.ref ∈ queue.cancelledGroups := by
  unfold State.RetiredGroup
  decide

/-- Refusing the parent also refuses its child, retaining both cancellation markers. -/
theorem child_parent_cancelled
    : queue.groupNode? child.node.ref = none
      ∧ parent.node.ref ∈ queue.cancelledGroups
      ∧ child.node.ref ∈ queue.cancelledGroups := by
  decide

/-- No child shell survives below the refused parent; the missing-parent boundary holds. -/
theorem missing_parent_boundary (work : Execution.Work) (failed : List Occurrence)
    : queue.MissingParentAncestorsHealthy work failed := by
  apply State.MissingParentAncestorsHealthy.of_presentOrCancelledParents
  intro node member
  rw [child_first_state.1] at member
  cases member

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerGuardBoundary
