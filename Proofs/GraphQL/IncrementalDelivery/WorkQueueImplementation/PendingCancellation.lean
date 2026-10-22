import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyPending

/-! Safe pending bounds and healthy exact counters after an ignored settlement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- All live groups keep the safety bound needed by zero-counter draining
-----------------------------------------------------------------------------------------

/-- Enlarging the settled ledger preserves every selected group's pending lower bound.
Witness: additional settlement tokens only reduce the unsettled-membership count.
-/
theorem State.PendingBound.weakenSettled {queue : State} {eligible before after}
    (bounded : queue.PendingBound eligible before) (included : before.Subset after)
    : queue.PendingBound eligible after := by
  intro node member relevant
  exact Nat.le_trans (unsettledCount_antitone node.tasks included)
    (bounded node member relevant)

/-- Removing an ignored task preserves the lower bound without decrementing counters.
Witness: first record the settlement in the proof ledger, then remove its membership.
The pending counter may overcount in failed groups, but cannot undercount live work.
-/
theorem State.PendingBound.ignoreTask {queue : State} {eligible settled}
    (bounded : queue.PendingBound eligible settled) (occurrence : Occurrence)
    : (queue.removeTask occurrence).PendingBound eligible (occurrence :: settled) :=
  (bounded.weakenSettled
    (by intro task member; exact List.mem_cons_of_mem _ member)).removeTask
    occurrence (by simp)

-----------------------------------------------------------------------------------------
-- Healthy groups still have exact counters
-----------------------------------------------------------------------------------------

/-- Ignoring a task absent from every healthy group preserves their exact counters.
Witness: neither removing nor recording an absent occurrence changes the group's count.
Failed-group counters need only the bound above, not an incorrect exactness assertion.
-/
theorem State.HealthyPendingTracks.ignoreTask {queue : State} {work settled failed}
    (tracks : queue.HealthyPendingTracks work settled failed) (occurrence : Occurrence)
    (absent
      : ∀ node ∈ queue.groupNodes,
          ¬GroupInvalidated work failed node.group.node.ref → occurrence ∉ node.tasks)
    : (queue.removeTask occurrence).HealthyPendingTracks work (occurrence :: settled)
        failed := by
  intro node member healthy
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  change old.pending = unsettledCount (old.tasks.filter (· != occurrence)) (occurrence :: settled)
  rw [unsettledCount_remove_settled _ _ _ (by simp),
    unsettledCount_settle_absent _ _ _ (absent old oldMember healthy)]
  exact tracks old oldMember healthy

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
