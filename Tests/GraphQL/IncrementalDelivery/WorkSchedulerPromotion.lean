import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Promotion provenance survives stale links and removal of empty intermediate groups. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerPromotion
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

private def root : DeliveryNode := { ref := 0, path := [] }
private def shell : DeliveryNode := { ref := 1, path := [] }
private def leaf : DeliveryNode := { ref := 2, path := [] }

private def rootNode : GroupNode :=
  { group := ⟨root, none⟩, childGroups := [99, shell.ref] }

private def queue : State :=
  {
    rootGroups := [root.ref],
    groupNodes :=
      [
        rootNode,
        { group := ⟨shell, some root.ref⟩, childGroups := [98, leaf.ref] },
        { group := ⟨leaf, some shell.ref⟩, pending := 1, tasks := [.executionGroup [2]] }
      ]
  }

-----------------------------------------------------------------------------------------
-- Raw structural coverage, without claiming this fixture is generated execution
-----------------------------------------------------------------------------------------

/-- Pruning skips stale refs and removes both empty shells, retaining the live leaf.
Witness: evaluate pruning on this deliberately raw queue, not a generated-work claim. -/
theorem pruning_skips_stale_shells
    : (queue.pruneEmptyGroups [root]).2 = [leaf]
      ∧ (queue.pruneEmptyGroups [root]).1.groupNode? root.ref = none
      ∧ (queue.pruneEmptyGroups [root]).1.groupNode? shell.ref = none := by
  cbv

/-- The retained leaf still has a path in the original queue, despite removed ancestors.
Witness: instantiate general pruning provenance, using only the computed retained leaf. -/
theorem pruning_retains_original_path : queue.LiveDescendant root.ref leaf.ref := by
  have retained : leaf ∈ (queue.pruneEmptyGroups [root]).2 := by
    rw [pruning_skips_stale_shells.1]
    exact List.mem_cons_self
  obtain ⟨candidate, member, path⟩ :=
    (queue.pruneEmptyGroups_descendants [root]).2 leaf retained
  have same := List.mem_singleton.mp member
  exact same ▸ path

/-- Completing the root releases the same leaf through the empty intermediate shell.
Witness: evaluate the actual group-success handler, including its child pruning. -/
theorem completion_releases_leaf
    : (queue.finishGroupSuccess rootNode).2.2.newGroups = [leaf] := by
  cbv

/-- The complete group-success handler's release has a stored original ancestor path.
Witness: the general release theorem, not a separately constructed path for the fixture. -/
theorem completion_retains_original_path : queue.LiveDescendant root.ref leaf.ref := by
  apply State.finishGroupSuccess_released_descendant (queue := queue)
    (group := rootNode) (by cbv)
  rw [completion_releases_leaf]
  exact List.mem_cons_self

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerPromotion
