import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Causality

/-! Historical failure and cancellation require an actual recorded failure cut. -/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A snapshot node failure needs an actual failed occurrence.
Witness: mutual causal induction rules out self-supporting cycles.
-/
theorem Causality.NodeFailed.nonempty {work failed published key}
    (failure : Causality.NodeFailed work failed published key)
    : failed ≠ [] := by
  induction failure
    using Causality.NodeFailed.rec (motive_2 := fun _ _ => failed ≠ []) with
  | task _ _ member =>
      intro empty; simp [empty] at member
  | groupDependency _ _ _ ih => exact ih
  | streamDependencies _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producers known noRoot _ _ ih =>
      obtain ⟨birth, known⟩ := known
      cases birth with
      | none => exact False.elim (noRoot known)
      | some producerOccurrence =>
          intro empty
          exact ih producerOccurrence known (by simp [empty]) empty
  | owners _ _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producerFailed _ _ member =>
      intro empty; simp [empty] at member
  | producerCancelled _ _ _ ih => exact ih

/-- Snapshot cancellation needs an actual failed occurrence.
Witness: the same mutual causal induction through owners and producers.
-/
theorem Causality.TaskCancelled.nonempty {work failed published occurrence}
    (cancelled : Causality.TaskCancelled work failed published occurrence)
    : failed ≠ [] := by
  induction cancelled
    using Causality.TaskCancelled.rec (motive_1 := fun _ _ => failed ≠ []) with
  | task _ _ member =>
      intro empty; simp [empty] at member
  | groupDependency _ _ _ ih => exact ih
  | streamDependencies _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producers known noRoot _ _ ih =>
      obtain ⟨birth, known⟩ := known
      cases birth with
      | none => exact False.elim (noRoot known)
      | some producerOccurrence =>
          intro empty
          exact ih producerOccurrence known (by simp [empty]) empty
  | owners _ _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producerFailed _ _ member =>
      intro empty; simp [empty] at member
  | producerCancelled _ _ _ ih => exact ih

/-- Node failure requires a nonempty list of failure cuts.
Witness: the cut retained by its public causal predicate.
-/
theorem NodeFailed.nonempty {work matching events failures key}
    (failure : NodeFailed work matching events failures key)
    : failures ≠ [] := by
  obtain ⟨cut, member, _⟩ := failure
  intro empty
  simp [empty] at member

/-- Task cancellation requires a nonempty list of failure cuts.
Witness: the cut retained by its public causal predicate.
-/
theorem TaskCancelled.nonempty {work matching events failures occurrence}
    (cancelled : TaskCancelled work matching events failures occurrence)
    : failures ≠ [] := by
  obtain ⟨cut, member, _⟩ := cancelled
  intro empty
  simp [empty] at member

end GraphQL.IncrementalDelivery.WorkQueueSemantics
