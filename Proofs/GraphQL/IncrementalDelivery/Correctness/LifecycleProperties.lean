import Proofs.GraphQL.IncrementalDelivery.Correctness.IDUsageProperties

/-! Consequences of the simplified wire-lifecycle checker.
These conditional wire facts do not assert that every admitted scheduler run is valid.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Complete delivery contains the very same ID-safety check; witness: Boolean conjunction
projection.
-/
theorem idUsageValid_of_deliveryComplete (result : QueryResult)
    (h : result.deliveryComplete = true)
    : result.idUsageValid := by
  cases result with
  | single response => trivial
  | incremental initial subsequent =>
      simp only [QueryResult.deliveryComplete, Bool.and_eq_true, and_assoc] at h
      exact ⟨of_decide_eq_true h.2.1, h.2.2.1⟩

/-- Complete delivery has unique announcements, by its safety witness and ID-usage
uniqueness.
-/
theorem idsUnique_of_deliveryComplete (result : QueryResult)
    (h : result.deliveryComplete = true)
    : result.idsUnique :=
  idsUnique_of_idUsageValid result (idUsageValid_of_deliveryComplete result h)

/-- Complete delivery's patches are causally announced, by the ID-usage reference witness.
-/
theorem patchesAnnounced_of_deliveryComplete (result : QueryResult)
    (h : result.deliveryComplete = true)
    : result.patchesAnnounced :=
  patchesAnnounced_of_idUsageValid result (idUsageValid_of_deliveryComplete result h)

/-- Global closure is causal under ID safety: a fresh announcement cannot have completed
earlier. Witness: induction tracks prior completions as known IDs, excluding them by
freshness.
-/
theorem idUsageValid_announcementsEventuallyComplete (seen active past : List String)
    (updates : List IncrementalStreamUpdateResult)
    (safe : DeliveryTrace.idUsageValid seen active updates = true)
    (supported : ∀ id ∈ active, id ∈ seen)
    (known : ∀ id ∈ past, id ∈ seen)
    (closes
      : ∀ id ∈ DeliveryTrace.pendingIDs updates,
          id ∈ past ++ DeliveryTrace.completedIDs updates)
    : DeliveryTrace.announcementsEventuallyComplete updates := by
  induction updates generalizing seen active past with
  | nil => trivial
  | cons update rest ih =>
      rw [idUsageValid_cons_iff] at safe
      obtain ⟨fresh, _, _, completed, _, tail⟩ := safe
      have available : ∀ id ∈ active ++ update.pending.map IncrementalPendingNotice.id,
          id ∈ seen ++ update.pending.map IncrementalPendingNotice.id := by
        intro id member
        rcases List.mem_append.mp member with prior | new
        · exact List.mem_append_left _ (supported id prior)
        · exact List.mem_append_right _ new
      refine ⟨?_, ih _ _ (past ++ update.completed.map IncrementalCompletionNotice.id)
        tail ?_ ?_ ?_⟩
      · intro id member
        rcases List.mem_append.mp (closes id (List.mem_append_left _ member)) with old | future
        · exact False.elim (fresh id member (known id old))
        · exact future
      · intro id member
        exact available id (List.mem_filter.mp member).1
      · intro id member
        rcases List.mem_append.mp member with old | new
        · exact List.mem_append_left _ (known id old)
        · exact available id (completed id new)
      · intro id member
        have h := closes id (List.mem_append_right _ member)
        simpa only [DeliveryTrace.completedIDs, List.flatMap_cons, List.append_assoc] using h

/-- Under safety, causal liveness is equivalent to total announcement closure. Witness:
the induction above supplies causality; the reverse direction forgets update order.
-/
theorem idsEventuallyComplete_iff_allCompleted (initial : InitialIncrementalStreamResult)
    (updates : List IncrementalStreamUpdateResult)
    (safe : (QueryResult.incremental initial updates).idUsageValid)
    : (QueryResult.incremental initial updates).idsEventuallyComplete
      ↔ ∀ id ∈
          initial.pending.map IncrementalPendingNotice.id
          ++ DeliveryTrace.pendingIDs updates,
          id ∈ DeliveryTrace.completedIDs updates := by
  constructor
  · intro live id member
    rcases List.mem_append.mp member with first | later
    · exact live.1 id first
    · exact announcementsEventuallyComplete_pendingIDs updates live.2 id later
  · intro closes
    refine ⟨fun id member => closes id (List.mem_append_left _ member), ?_⟩
    apply idUsageValid_announcementsEventuallyComplete _ _ [] updates safe.2
      (by intros; assumption) (by simp)
    intro id member
    simpa using closes id (List.mem_append_right _ member)

/-- Complete delivery closes IDs causally, not merely somewhere in the trace, by safety
plus closure.
-/
theorem idsEventuallyComplete_of_deliveryComplete (result : QueryResult)
    (h : result.deliveryComplete = true)
    : result.idsEventuallyComplete := by
  have safe := idUsageValid_of_deliveryComplete result h
  cases result with
  | single response => trivial
  | incremental initial subsequent =>
      apply (idsEventuallyComplete_iff_allCompleted initial subsequent safe).mpr
      simp only [QueryResult.deliveryComplete, Bool.and_eq_true, and_assoc] at h
      simpa only [List.all_eq_true, List.contains_iff_mem] using h.2.2.2.1

/-- Complete delivery completes each announcement exactly once; combine safety with causal
liveness.
-/
theorem idsCompleteExactlyOnce_of_deliveryComplete (result : QueryResult)
    (h : result.deliveryComplete = true)
    : result.idsCompleteExactlyOnce :=
  idsCompleteExactlyOnce_of_idUsageValid_of_liveness result
    (idUsageValid_of_deliveryComplete result h)
    (idsEventuallyComplete_of_deliveryComplete result h)

end GraphQL.IncrementalDelivery.Correctness
