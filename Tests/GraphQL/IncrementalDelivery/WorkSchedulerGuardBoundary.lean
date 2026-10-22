import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorGuardHealth
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementIntegration

/-! Child-first registration can retain a live shell below a cancelled missing parent. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerGuardBoundary
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def parent : Group := ⟨⟨1, [], none⟩, some 0⟩
private def child : Group := ⟨⟨2, [], none⟩, some 1⟩

private def queue : State :=
  (({ registeredGroups := [0], cancelledGroups := [0] } : State).addGroups
    [child, parent]).1

/-- Registering the child first retains its shell but records the missing parent's
cancellation. Witness: evaluate group registration and the subsequent link-installation
pass. This is a raw registration-order test, not an execution-generated work claim. -/
theorem child_first_state
    : queue.groupNodes = [⟨child, [], [], 0⟩]
      ∧ queue.cancelledGroups = [0, 1]
      ∧ queue.groupNode? parent.node.ref = none := by cbv

/-- A newly refused parent is retired because registration recorded its cancellation.
Witness: the general registration reflection theorem excludes old retirement here and
supplies the new marker. Unqualified retirement equivalence would be false for this case.
-/
theorem new_retirement_marked
    : queue.RetiredGroup parent.node.ref ∧ parent.node.ref ∈ queue.cancelledGroups := by
  have retired : queue.RetiredGroup parent.node.ref := by
    change (1 : Nat) ∈ [0, 2, 1] ∧ (1 : Nat) ∉ [2]
    decide
  refine ⟨retired, ?_⟩
  have reflected :=
    ({ registeredGroups := [0], cancelledGroups := [0] } : State).addGroups_retired_or_cancelled
      [child, parent] parent.node.ref retired
  exact reflected.resolve_left
    (by
      change ¬((1 : Nat) ∈ [0] ∧ (1 : Nat) ∉ [])
      decide)

/-- The retained child names the cancelled parent in its registration metadata. -/
theorem child_parent_cancelled
    : (queue.groupNode? child.node.ref).map (fun node => node.group.parent)
        = some (some 1)
      ∧ 1 ∈ queue.cancelledGroups := by
  cbv; exact List.mem_cons_of_mem _ List.mem_cons_self

/-- This state satisfies the corrected boundary without asserting cancelled ancestry is
healthy. Witness: every live record's parent is recorded as cancelled, so no accepting
missing-parent branch needs historical evidence, for any work or failure inventory. -/
theorem missing_parent_boundary (work : Execution.Work) (failed : List Occurrence)
    : queue.MissingParentAncestorsHealthy work failed := by
  apply State.MissingParentAncestorsHealthy.of_presentOrCancelledParents
  intro node member ref same
  rw [child_first_state.1] at member
  obtain rfl := List.mem_singleton.mp member
  have refEq : ref = 1 := (Option.some.inj same).symm
  exact Or.inr (by rw [refEq, child_first_state.2.1]; simp)

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerGuardBoundary
