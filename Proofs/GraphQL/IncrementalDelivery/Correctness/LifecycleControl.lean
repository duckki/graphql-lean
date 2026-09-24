import Proofs.GraphQL.IncrementalDelivery.Correctness.LifecycleProperties

/-! Separate wire control flow and closure from open-ID safety.
These proof-only predicates decompose the public checker, without adding scheduler assumptions.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Nonempty incremental delivery, causal ID closure, and accurate continuation flags. -/
def QueryControl : ExecutionObservation → Prop
  | .single _ => True
  | .incremental initial subsequent =>
      initial.pending ≠ []
      ∧ (ExecutionObservation.incremental initial subsequent).idsEventuallyComplete
      ∧ initial.hasNext = !subsequent.isEmpty
      ∧ DeliveryTrace.hasNextValid subsequent = true

/-- The complete checker is exactly safety plus closure/control, using safety to recover
causality.
-/
theorem deliveryComplete_iff_idUsageValid_control (result : ExecutionObservation)
    : result.deliveryComplete = true ↔ result.idUsageValid ∧ QueryControl result := by
  cases result with
  | single response =>
      simp [ExecutionObservation.deliveryComplete, ExecutionObservation.idUsageValid, QueryControl]
  | incremental initial subsequent =>
      constructor
      · intro h
        have safe := idUsageValid_of_deliveryComplete _ h
        have live := idsEventuallyComplete_of_deliveryComplete _ h
        simp only [ExecutionObservation.deliveryComplete, Bool.and_eq_true, and_assoc] at h
        refine ⟨safe, ?_, live, beq_iff_eq.mp h.2.2.2.2.1, h.2.2.2.2.2⟩
        simpa using h.1
      · rintro ⟨safe, nonempty, live, initialNext, subsequentNext⟩
        have closes := (idsEventuallyComplete_iff_allCompleted initial subsequent safe).mp live
        simp only [ExecutionObservation.deliveryComplete, Bool.and_eq_true, and_assoc]
        refine ⟨?_, decide_eq_true safe.1, safe.2, ?_,
          beq_iff_eq.mpr initialNext, subsequentNext⟩
        · simpa using nonempty
        · simpa only [List.all_eq_true, List.contains_iff_mem] using closes

end GraphQL.IncrementalDelivery.Correctness
