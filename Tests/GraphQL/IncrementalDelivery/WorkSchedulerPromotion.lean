import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Promotion provenance survives stale links and removal of empty intermediate groups. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerPromotion
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

private def root : DeliveryNode := { key := 0, path := [] }
private def shell : DeliveryNode := { key := 1, path := [] }
private def leaf : DeliveryNode := { key := 2, path := [] }

private def rootNode : GroupNode :=
  { group := ⟨root, none⟩, childGroups := [99, shell.key] }

private def queue : State :=
  {
    rootGroups := [root.key],
    groupNodes :=
      [
        rootNode,
        { group := ⟨shell, some root.key⟩, childGroups := [98, leaf.key] },
        { group := ⟨leaf, some shell.key⟩, pending := 1, tasks := [.executionGroup [2]] }
      ]
  }

-----------------------------------------------------------------------------------------
-- Raw structural coverage, without claiming this fixture is generated execution
-----------------------------------------------------------------------------------------

/-- Pruning skips stale keys and removes both empty shells, retaining the live leaf.
Witness: evaluate pruning on this deliberately raw queue, not a generated-work claim. -/
theorem pruning_skips_stale_shells
    : (queue.pruneEmptyGroups [root]).2 = [leaf]
      ∧ (queue.pruneEmptyGroups [root]).1.groupNode? root.key = none
      ∧ (queue.pruneEmptyGroups [root]).1.groupNode? shell.key = none := by
  cbv

/-- The retained leaf still has a path in the original queue, despite removed ancestors.
Witness: instantiate general pruning provenance, using only the computed retained leaf. -/
theorem pruning_retains_original_path : queue.LiveDescendant root.key leaf.key := by
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
theorem completion_retains_original_path : queue.LiveDescendant root.key leaf.key := by
  apply State.finishGroupSuccess_released_descendant (queue := queue)
    (group := rootNode) (by cbv)
  rw [completion_releases_leaf]
  exact List.mem_cons_self

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerPromotion
