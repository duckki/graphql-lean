import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedSupply

/-! Stream-node allocation occurrences, including every hidden item's work.
These refs count stream nodes once, not the repeated pulls of their delivery cursors.
Disjoint allocation intervals establish uniqueness across sibling computations.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution

def streamAllocationRefs : Work → List Nat
  | .empty => []
  | .combine left right => streamAllocationRefs left ++ streamAllocationRefs right
  | .executionGroup _ _ _ children => streamAllocationRefs children
  | .stream node items =>
      node.ref :: items.flatMap (fun item => streamAllocationRefs item.2)
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

structure RefsAllocated (start : Nat) (refs : List Nat) (finish : Nat) : Prop where
  monotone : start ≤ finish
  bounds : ∀ ref ∈ refs, start ≤ ref ∧ ref < finish
  unique : refs.Nodup

def StreamAllocated (start : Nat) (work : Work) (finish : Nat) : Prop :=
  RefsAllocated start (streamAllocationRefs work) finish

def StreamsCompleted (start : Nat) (output : Completion α × Nat) : Prop :=
  StreamAllocated start output.1.work output.2

def itemAllocationRefs (items : List (Result ResponseValue × Work)) : List Nat :=
  items.flatMap (fun item => streamAllocationRefs item.2)

theorem RefsAllocated.empty {start finish : Nat} (h : start ≤ finish)
    : RefsAllocated start [] finish :=
  ⟨h, by simp, by simp⟩

theorem RefsAllocated.widen {start finish lower upper : Nat} {refs : List Nat}
    (h : RefsAllocated start refs finish) (hl : lower ≤ start) (hu : finish ≤ upper)
    : RefsAllocated lower refs upper :=
  ⟨
    Nat.le_trans hl (Nat.le_trans h.monotone hu),
    fun ref hk =>
      ⟨Nat.le_trans hl (h.bounds ref hk).1, Nat.lt_of_lt_of_le (h.bounds ref hk).2 hu⟩,
    h.unique
  ⟩

theorem RefsAllocated.disjoint {start middle finish : Nat} {left right : List Nat}
    (hl : RefsAllocated start left middle) (hr : RefsAllocated middle right finish)
    : ∀ ref ∈ left, ref ∉ right := by
  intro ref hleft hright
  have := (hl.bounds ref hleft).2
  have := (hr.bounds ref hright).1
  omega

theorem RefsAllocated.append {start middle finish : Nat} {left right : List Nat}
    (hl : RefsAllocated start left middle) (hr : RefsAllocated middle right finish)
    : RefsAllocated start (left ++ right) finish := by
  refine ⟨Nat.le_trans hl.monotone hr.monotone, ?_,
    List.nodup_append.mpr ⟨hl.unique, hr.unique,
      fun ref hk other ho he => hl.disjoint hr ref hk (he ▸ ho)⟩⟩
  intro ref hk
  rcases List.mem_append.mp hk with hk | hk
  · exact ⟨(hl.bounds ref hk).1, Nat.lt_of_lt_of_le (hl.bounds ref hk).2 hr.monotone⟩
  · exact ⟨Nat.le_trans hl.monotone (hr.bounds ref hk).1, (hr.bounds ref hk).2⟩

theorem RefsAllocated.fresh {start finish : Nat} {refs : List Nat}
    (h : RefsAllocated (start + 1) refs finish)
    : RefsAllocated start (start :: refs) finish := by
  refine ⟨by have := h.monotone; omega, ?_, List.nodup_cons.mpr ⟨?_, h.unique⟩⟩
  · intro ref hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact ⟨Nat.le_refl _, h.monotone⟩
    · exact ⟨Nat.le_trans (Nat.le_succ _) (h.bounds ref hk).1, (h.bounds ref hk).2⟩
  · intro hk
    have := (h.bounds start hk).1
    omega

theorem streams_empty_of_le {start finish : Nat} (h : start ≤ finish)
    : StreamAllocated start .empty finish := by
  simpa only [StreamAllocated, streamAllocationRefs] using RefsAllocated.empty h

theorem streams_empty (state : Nat) : StreamAllocated state .empty state :=
  streams_empty_of_le (Nat.le_refl _)

theorem streams_combine {start middle finish : Nat} {left right : Work}
    (hl : StreamAllocated start left middle) (hr : StreamAllocated middle right finish)
    : StreamAllocated start (.combine left right) finish := by
  rw [StreamAllocated, streamAllocationRefs]
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
