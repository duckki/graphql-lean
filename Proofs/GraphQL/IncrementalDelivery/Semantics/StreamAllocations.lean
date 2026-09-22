import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedSupply

/-! Stream-node allocation occurrences, including every hidden item's work.
These keys count stream nodes once, not the repeated pulls of their delivery cursors.
Disjoint allocation intervals establish uniqueness across sibling computations.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution

def streamAllocationKeys : Work → List Nat
  | .empty => []
  | .combine left right => streamAllocationKeys left ++ streamAllocationKeys right
  | .executionGroup _ _ _ children => streamAllocationKeys children
  | .stream node items =>
      node.key :: items.flatMap (fun item => streamAllocationKeys item.2)
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

structure KeysAllocated (start : Nat) (keys : List Nat) (finish : Nat) : Prop where
  monotone : start ≤ finish
  bounds : ∀ key ∈ keys, start ≤ key ∧ key < finish
  unique : keys.Nodup

def StreamAllocated (start : Nat) (work : Work) (finish : Nat) : Prop :=
  KeysAllocated start (streamAllocationKeys work) finish

def StreamsCompleted (start : Nat) (output : Completion α × Nat) : Prop :=
  StreamAllocated start output.1.work output.2

def itemAllocationKeys (items : List (Result ResponseValue × Work)) : List Nat :=
  items.flatMap (fun item => streamAllocationKeys item.2)

theorem KeysAllocated.empty {start finish : Nat} (h : start ≤ finish)
    : KeysAllocated start [] finish :=
  ⟨h, by simp, by simp⟩

theorem KeysAllocated.widen {start finish lower upper : Nat} {keys : List Nat}
    (h : KeysAllocated start keys finish) (hl : lower ≤ start) (hu : finish ≤ upper)
    : KeysAllocated lower keys upper :=
  ⟨
    Nat.le_trans hl (Nat.le_trans h.monotone hu),
    fun key hk =>
      ⟨Nat.le_trans hl (h.bounds key hk).1, Nat.lt_of_lt_of_le (h.bounds key hk).2 hu⟩,
    h.unique
  ⟩

theorem KeysAllocated.disjoint {start middle finish : Nat} {left right : List Nat}
    (hl : KeysAllocated start left middle) (hr : KeysAllocated middle right finish)
    : ∀ key ∈ left, key ∉ right := by
  intro key hleft hright
  have := (hl.bounds key hleft).2
  have := (hr.bounds key hright).1
  omega

theorem KeysAllocated.append {start middle finish : Nat} {left right : List Nat}
    (hl : KeysAllocated start left middle) (hr : KeysAllocated middle right finish)
    : KeysAllocated start (left ++ right) finish := by
  refine ⟨Nat.le_trans hl.monotone hr.monotone, ?_,
    List.nodup_append.mpr ⟨hl.unique, hr.unique,
      fun key hk other ho he => hl.disjoint hr key hk (he ▸ ho)⟩⟩
  intro key hk
  rcases List.mem_append.mp hk with hk | hk
  · exact ⟨(hl.bounds key hk).1, Nat.lt_of_lt_of_le (hl.bounds key hk).2 hr.monotone⟩
  · exact ⟨Nat.le_trans hl.monotone (hr.bounds key hk).1, (hr.bounds key hk).2⟩

theorem KeysAllocated.fresh {start finish : Nat} {keys : List Nat}
    (h : KeysAllocated (start + 1) keys finish)
    : KeysAllocated start (start :: keys) finish := by
  refine ⟨by have := h.monotone; omega, ?_, List.nodup_cons.mpr ⟨?_, h.unique⟩⟩
  · intro key hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨Nat.le_refl _, h.monotone⟩
    · exact ⟨Nat.le_trans (Nat.le_succ _) (h.bounds key hk).1, (h.bounds key hk).2⟩
  · intro hk
    have := (h.bounds start hk).1
    omega

theorem streams_empty_of_le {start finish : Nat} (h : start ≤ finish)
    : StreamAllocated start .empty finish := by
  simpa only [StreamAllocated, streamAllocationKeys] using KeysAllocated.empty h

theorem streams_empty (state : Nat) : StreamAllocated state .empty state :=
  streams_empty_of_le (Nat.le_refl _)

theorem streams_combine {start middle finish : Nat} {left right : Work}
    (hl : StreamAllocated start left middle) (hr : StreamAllocated middle right finish)
    : StreamAllocated start (.combine left right) finish := by
  rw [StreamAllocated, streamAllocationKeys]
  exact hl.append hr

theorem streams_completionCombine {start middle finish : Nat} (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : StreamAllocated start left.work middle)
    (hr : StreamAllocated middle right.work finish)
    : StreamAllocated start (Completion.combine f left right).work finish := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine, Completion.error]
  · exact streams_empty_of_le (Nat.le_trans hl.monotone hr.monotone)
  · exact streams_empty_of_le (Nat.le_trans hl.monotone hr.monotone)
  · exact streams_empty_of_le (Nat.le_trans hl.monotone hr.monotone)
  · exact streams_combine hl hr

theorem streams_map {start finish : Nat} (f : α → β) (completed : Completion α)
    (h : StreamAllocated start completed.work finish)
    : StreamAllocated start (completed.map f).work finish := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · exact streams_empty_of_le h.monotone
  · exact h

theorem streams_catchNull {start finish : Nat} (f : α → ResponseValue)
    (completed : Completion α) (h : StreamAllocated start completed.work finish)
    : StreamAllocated start (completed.catchNull f).work finish := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · exact streams_empty_of_le h.monotone
  · exact h

theorem streams_nonNull {start finish : Nat} (completed : Completion ResponseValue)
    (h : StreamAllocated start completed.work finish)
    : StreamAllocated start completed.nonNull.work finish := by
  unfold Completion.nonNull
  split
  · exact streams_empty_of_le h.monotone
  · exact h

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
