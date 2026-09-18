import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Causality

/-! Failure evidence must ultimately contain an actual failed occurrence. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- Failure cannot be manufactured from cyclic ancestry/cancellation; witness: mutual
causal induction.
-/
theorem NodeFailed.nonempty {work failed key} (h : NodeFailed work failed key)
    : failed ≠ [] := by
  induction h using Causality.NodeFailed.rec (motive_2 := fun _ _ => failed ≠ []) with
  | task _ _ member =>
      intro empty; simp [empty] at member
  | groupParent _ _ _ ih => exact ih
  | streamParents _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producers known noRoot _ ih =>
      obtain ⟨birth, known⟩ := known
      cases birth with
      | none => exact False.elim (noRoot known)
      | some parent =>
          intro empty
          exact ih parent known (by simp [empty]) empty
  | owners _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producerFailed _ member =>
      intro empty; simp [empty] at member
  | producerCancelled _ _ ih => exact ih

/-- Cancellation also requires an actual failure root, by the same mutual causal
induction.
-/
theorem TaskCancelled.nonempty {work failed occurrence}
    (h : TaskCancelled work failed occurrence)
    : failed ≠ [] := by
  induction h using Causality.TaskCancelled.rec (motive_1 := fun _ _ => failed ≠ []) with
  | task _ _ member =>
      intro empty; simp [empty] at member
  | groupParent _ _ _ ih => exact ih
  | streamParents _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producers known noRoot _ ih =>
      obtain ⟨birth, known⟩ := known
      cases birth with
      | none => exact False.elim (noRoot known)
      | some parent =>
          intro empty
          exact ih parent known (by simp [empty]) empty
  | owners _ nonempty _ ih =>
      obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil _ nonempty
      exact ih key member
  | producerFailed _ member =>
      intro empty; simp [empty] at member
  | producerCancelled _ _ ih => exact ih

end GraphQL.IncrementalDelivery.WorkScheduler
