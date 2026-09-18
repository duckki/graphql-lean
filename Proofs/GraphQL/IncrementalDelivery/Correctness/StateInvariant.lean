import GraphQL.IncrementalDelivery.WorkScheduler

/-! Small proof-only invariant combinators for the pure state computations. -/

namespace GraphQL.IncrementalDelivery.Correctness

def StateInvariant (invariant : σ → Prop) (action : StateM σ α) : Prop :=
  ∀ state, invariant state → invariant (action.run state).2

/-- Pure computations preserve the invariant because they retain the state. -/
theorem StateInvariant.pure (invariant : σ → Prop) (value : α)
    : StateInvariant invariant (pure value) :=
  fun _ h => h

/-- Sequential invariant-preserving actions preserve it, by composing their witnesses. -/
theorem StateInvariant.bind {invariant : σ → Prop} {action : StateM σ α}
    {next : α → StateM σ β} (head : StateInvariant invariant action)
    (tail : ∀ value, StateInvariant invariant (next value))
    : StateInvariant invariant (action >>= next) := by
  intro state h
  exact tail (action.run state).1 (action.run state).2 (head state h)

/-- Mapping preserves the state invariant, by induction on the input list. -/
theorem StateInvariant.mapM {invariant : σ → Prop} {action : α → StateM σ β}
    (h : ∀ value, StateInvariant invariant (action value)) (values : List α)
    : StateInvariant invariant (values.mapM action) := by
  induction values with
  | nil => exact .pure _ _
  | cons value rest ih =>
      rw [List.mapM_cons]
      exact (h value).bind fun _ => ih.bind fun _ => .pure _ _

/-- Iteration preserves the invariant, by induction and both loop-control cases. -/
theorem StateInvariant.forIn {invariant : σ → Prop}
    {action : α → β → StateM σ (ForInStep β)}
    (h : ∀ value acc, StateInvariant invariant (action value acc))
    (values : List α) (initial : β)
    : StateInvariant invariant (forIn values initial action) := by
  induction values generalizing initial with
  | nil => exact .pure _ _
  | cons value rest ih =>
      rw [List.forIn_cons]
      apply (h value initial).bind
      intro step
      cases step with
      | done _ => exact .pure _ _
      | yield _ => exact ih _

end GraphQL.IncrementalDelivery.Correctness
