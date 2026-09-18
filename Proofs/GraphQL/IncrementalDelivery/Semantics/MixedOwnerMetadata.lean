import Proofs.GraphQL.IncrementalDelivery.Semantics.OwnerMetadata

/-! Absolute path assignments for mixed deferred and streamed work.  Stream item
indices are already present in the paths of generated child work; this invariant
does not itself identify those indices with a wire decoder's cursor.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedOwnerPaths

open GraphQL.IncrementalDelivery.Execution
open OwnerPaths

def WorkAt (paths : Assignment) (bound : Nat) : Work → Prop
  | .empty => True
  | .append left right => WorkAt paths bound left ∧ WorkAt paths bound right
  | .deferred groups path _ children =>
      MapAt paths bound path groups ∧ WorkAt paths bound children
  | .stream node items =>
      Assigned paths bound node ∧ ∀ item ∈ items, WorkAt paths bound item.2
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def ItemsAt (paths : Assignment) (bound : Nat)
    (items : List (GraphQL.Execution.Result ResponseValue × Work))
    : Prop :=
  ∀ item ∈ items, WorkAt paths bound item.2

def Output (paths : Assignment) (start : Nat) (work : Work) (finish : Nat) : Prop :=
  start ≤ finish ∧ ∃ next, Extends start paths next ∧ WorkAt next finish work

def Completed (paths : Assignment) (start : Nat) (output : Completion α × Nat) : Prop :=
  Output paths start output.1.work output.2

def ItemsOutput (paths : Assignment) (start : Nat)
    (output : List (GraphQL.Execution.Result ResponseValue × Work) × Nat)
    : Prop :=
  start ≤ output.2 ∧ ∃ next, Extends start paths next ∧ ItemsAt next output.2 output.1

theorem WorkAt.extend {paths next : Assignment} {start finish : Nat} {work : Work}
    (h : WorkAt paths start work) (he : Extends start paths next) (hle : start ≤ finish)
    : WorkAt next finish work := by
  cases work with
  | empty => simp [WorkAt]
  | append left right =>
      simp only [WorkAt] at h ⊢
      exact ⟨h.1.extend he hle, h.2.extend he hle⟩
  | deferred groups path result children =>
      simp only [WorkAt] at h ⊢
      exact ⟨h.1.extend he hle, h.2.extend he hle⟩
  | stream node items =>
      simp only [WorkAt] at h ⊢
      refine ⟨h.1.extend he hle, fun item hi => ?_⟩
      exact (h.2 item hi).extend he hle
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem hi
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem ItemsAt.extend {paths next : Assignment} {start finish : Nat}
    {items : List (GraphQL.Execution.Result ResponseValue × Work)}
    (h : ItemsAt paths start items) (he : Extends start paths next) (hle : start ≤ finish)
    : ItemsAt next finish items :=
  fun item hi => (h item hi).extend he hle

theorem output_empty (paths : Assignment) (state : Nat)
    : Output paths state .empty state :=
  ⟨Nat.le_refl _, paths, Extends.refl _ _, by simp [WorkAt]⟩

theorem workAt_combine (paths : Assignment) (bound : Nat) (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : WorkAt paths bound left.work) (hr : WorkAt paths bound right.work)
    : WorkAt paths bound (Completion.combine f left right).work := by
  cases hlr : left.result <;> cases hrr : right.result <;>
    simp [Completion.combine, GraphQL.Execution.Result.combine, hlr, hrr,
      Completion.error, WorkAt, hl, hr]

theorem workAt_map (paths : Assignment) (bound : Nat) (f : α → β)
    (completed : Completion α) (h : WorkAt paths bound completed.work)
    : WorkAt paths bound (completed.map f).work := by
  cases he : completed.result <;> simp [Completion.map, he, Completion.error, WorkAt, h]

theorem workAt_catchNull (paths : Assignment) (bound : Nat) (f : α → ResponseValue)
    (completed : Completion α) (h : WorkAt paths bound completed.work)
    : WorkAt paths bound (completed.catchNull f).work := by
  cases he : completed.result <;> simp [Completion.catchNull, he, WorkAt, h]

theorem workAt_nonNull (paths : Assignment) (bound : Nat)
    (completed : Completion ResponseValue) (h : WorkAt paths bound completed.work)
    : WorkAt paths bound completed.nonNull.work := by
  unfold Completion.nonNull
  split <;> simp [Completion.error, WorkAt, h]

theorem assigned_fresh (paths : Assignment) (state : Nat) (node : DeliveryNode)
    (hk : node.key = state)
    : let next := fun key => if key = state then node.path else paths key
      Extends state paths next ∧ Assigned next (state + 1) node := by
  refine ⟨?_, ?_⟩
  · intro key hh
    simp [show key ≠ state by omega]
  · simp [Assigned, hk]

end GraphQL.IncrementalDelivery.Semantics.MixedOwnerPaths
