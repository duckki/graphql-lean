import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.SettlementPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.TaskReadiness

/-! Accepted failures retain an unfinished owner before the new settlement. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Prior cancellation cannot justify accepting a new settlement
-----------------------------------------------------------------------------------------

/-- A licensed failure has a healthy unfinished owner relative to its earlier settlements.
Witness: the task is neither cancelled by its licensing predecessors nor publishable with
its fixed failing payload. The earlier explained prefix therefore supplies an outstanding
owner. That owner may be latent; unlike singleton ownership, this does not assert openness.
-/
theorem Explains.failure_outstanding_owner
    {work groups streams events matching before cut occurrence after owners producer
      payload}
    (explained
      : Explains work groups streams events matching
          (before ++ (cut, occurrence) :: after))
    (known : TaskAt work occurrence owners producer payload)
    : ∃ ref ∈ owners,
        ¬NodeFailed work matching (events.take cut) before ref
        ∧ ref ∉ completedRefs (events.take cut) := by
  have licensed := explained.2.1 before cut occurrence after rfl
  have earlier := explained.before_settlement
  have nonempty : owners ≠ [] := by
    obtain ⟨ref, member, _⟩ := explained.2.1.announced_owner (cut := cut) (by simp) known
    intro empty
    simp [empty] at member
  apply earlier.outstanding_owner known nonempty
  rintro (cancelled | published)
  · exact licensed.2.2.2 cancelled
  · apply explained.failed_unpublished (occurrence := occurrence)
      (mem_failedBefore (occurrence := occurrence) (by simp) (Nat.le_refl cut))
    simpa only [List.take_append_drop] using published.append (events.drop cut)

/-- If all announced owners have closed, a licensed shared failure retains a latent owner.
Witness: the preceding outstanding-owner theorem supplies a healthy uncompleted ref;
the closure premise excludes prior announcement of that ref. No notice is invented.
-/
theorem Explains.failure_latent_owner
    {work groups streams events matching before cut occurrence after owners producer
      payload}
    (explained
      : Explains work groups streams events matching
          (before ++ (cut, occurrence) :: after))
    (known : TaskAt work occurrence owners producer payload)
    (closed
      : ∀ ref ∈ owners,
          ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) (events.take cut)
          → ref ∈ completedRefs (events.take cut))
    : ∃ ref ∈ owners,
        ¬NodeFailed work matching (events.take cut) before ref
        ∧ ref ∉ completedRefs (events.take cut)
        ∧ ref
          ∉ announcedRefs ((groups ++ streams).map DeliveryNode.ref)
              (events.take cut) := by
  obtain ⟨ref, member, healthy, unfinished⟩ := explained.failure_outstanding_owner known
  exact ⟨ref, member, healthy, unfinished, fun announced => unfinished (closed ref member announced)⟩

end GraphQL.IncrementalDelivery.WorkQueueSemantics
