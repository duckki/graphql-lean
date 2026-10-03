import Proofs.GraphQL.IncrementalDelivery.Semantics.DeferRefs
import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryMetadata
import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Stream owner refs precede the stream nodes registered under them.
Only streams reached through combine nodes inherit the current owner list; deferred
tasks establish their own owner list when their children are registered.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution

def OwnersBefore (owners : List Nat) : Work → Prop
  | .empty => True
  | .combine left right => OwnersBefore owners left ∧ OwnersBefore owners right
  | .executionGroup .. => True
  | .stream node _ => ∀ owner ∈ owners, owner < node.ref

def StreamOwnersOrdered : Work → Prop
  | .empty => True
  | .combine left right => StreamOwnersOrdered left ∧ StreamOwnersOrdered right
  | .executionGroup groups _ _ children =>
      OwnersBefore (groups.map (·.node.ref)) children ∧ StreamOwnersOrdered children
  | .stream _ items => ∀ item ∈ items, StreamOwnersOrdered item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def StreamRefsFrom (start : Nat) : Work → Prop
  | .empty => True
  | .combine left right => StreamRefsFrom start left ∧ StreamRefsFrom start right
  | .executionGroup _ _ _ children => StreamRefsFrom start children
  | .stream node items => start ≤ node.ref ∧ ∀ item ∈ items, StreamRefsFrom start item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem StreamRefsFrom.mono {start next : Nat} {work : Work}
    (h : StreamRefsFrom start work) (hle : next ≤ start)
    : StreamRefsFrom next work := by
  cases work <;> simp only [StreamRefsFrom] at h ⊢
  case combine left right => exact ⟨h.1.mono hle, h.2.mono hle⟩
  case executionGroup groups path result children => exact h.mono hle
  case stream node items => exact ⟨Nat.le_trans hle h.1, fun item hi => (h.2 item hi).mono hle⟩
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem hi
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem StreamRefsFrom.ownersBefore {start : Nat} {work : Work}
    (h : StreamRefsFrom start work) {owners : List Nat}
    (ho : ∀ owner ∈ owners, owner < start)
    : OwnersBefore owners work := by
  cases work with
  | empty => trivial
  | combine left right =>
      rw [StreamRefsFrom] at h
      exact ⟨h.1.ownersBefore ho, h.2.ownersBefore ho⟩
  | executionGroup groups path result children => trivial
  | stream node items =>
      rw [StreamRefsFrom] at h
      exact fun owner hm => Nat.lt_of_lt_of_le (ho owner hm) h.1
termination_by sizeOf work

theorem ownersBefore_nil (work : Work) : OwnersBefore [] work := by
  cases work with
  | empty => trivial
  | combine left right => exact ⟨ownersBefore_nil left, ownersBefore_nil right⟩
  | executionGroup groups path result children => trivial
  | stream node items => simp [OwnersBefore]
termination_by sizeOf work

def StreamRefOutput (start : Nat) (work : Work) (finish : Nat) : Prop :=
  start ≤ finish ∧ StreamRefsFrom start work ∧ StreamOwnersOrdered work

def StreamRefCompleted (start : Nat) (output : Completion α × Nat) : Prop :=
  StreamRefOutput start output.1.work output.2

theorem streamRefOutput_empty (state : Nat) : StreamRefOutput state .empty state :=
  ⟨Nat.le_refl _, by simp [StreamRefsFrom], by simp [StreamOwnersOrdered]⟩

theorem streamRefs_combine {start : Nat} {left right : Work}
    (hl : StreamRefsFrom start left ∧ StreamOwnersOrdered left)
    (hr : StreamRefsFrom start right ∧ StreamOwnersOrdered right)
    : StreamRefsFrom start (.combine left right)
      ∧ StreamOwnersOrdered (.combine left right) := by
  simp only [StreamRefsFrom, StreamOwnersOrdered]
  exact ⟨⟨hl.1, hr.1⟩, hl.2, hr.2⟩

theorem streamRefs_completionCombine (start : Nat) (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : StreamRefsFrom start left.work ∧ StreamOwnersOrdered left.work)
    (hr : StreamRefsFrom start right.work ∧ StreamOwnersOrdered right.work)
    : StreamRefsFrom start (Completion.combine f left right).work
      ∧ StreamOwnersOrdered (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine]
  all_goals first
  | exact streamRefs_combine hl hr
  | simp [Completion.error, StreamRefsFrom, StreamOwnersOrdered]

theorem streamRefs_map (start : Nat) (f : α → β) (completed : Completion α)
    (h : StreamRefsFrom start completed.work ∧ StreamOwnersOrdered completed.work)
    : StreamRefsFrom start (completed.map f).work
      ∧ StreamOwnersOrdered (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · simp [Completion.error, StreamRefsFrom, StreamOwnersOrdered]
  · exact h

theorem streamRefs_catchNull (start : Nat) (f : α → ResponseValue)
    (completed : Completion α)
    (h : StreamRefsFrom start completed.work ∧ StreamOwnersOrdered completed.work)
    : StreamRefsFrom start (completed.catchNull f).work
      ∧ StreamOwnersOrdered (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · simp [StreamRefsFrom, StreamOwnersOrdered]
  · exact h

theorem streamRefs_nonNull (start : Nat) (completed : Completion ResponseValue)
    (h : StreamRefsFrom start completed.work ∧ StreamOwnersOrdered completed.work)
    : StreamRefsFrom start completed.nonNull.work
      ∧ StreamOwnersOrdered completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · simp [Completion.error, StreamRefsFrom, StreamOwnersOrdered]
  · exact h

def DeferMapBefore (state : Nat) (deferMap : DeferMap) : Prop :=
  ∀ fragment ∈ deferMap, fragment.node.ref < state

theorem DeferMapBefore.mono {state next : Nat} {deferMap : DeferMap}
    (h : DeferMapBefore state deferMap) (hle : state ≤ next)
    : DeferMapBefore next deferMap :=
  fun fragment hf => Nat.lt_of_lt_of_le (h fragment hf) hle

theorem deferMapBefore_new {start finish : Nat} {deferMap : DeferMap}
    (h : DeferMapBefore start deferMap) (hle : start ≤ finish) (usages : List DeferUsage)
    (hu : ∀ usage ∈ usages, usage.ref < finish) (path : ResponsePath)
    : DeferMapBefore finish (getNewDeferMap usages path deferMap) := by
  intro fragment hf
  have hk : fragment.node.ref ∈ Ancestry.mapRefs (getNewDeferMap usages path deferMap) :=
    List.mem_map.mpr ⟨fragment, hf, rfl⟩
  rw [Ancestry.getNewDeferMap_refs] at hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨old, ho, he⟩ := List.mem_map.mp hk
    simpa only [he] using Nat.lt_of_lt_of_le (h old ho) hle
  · obtain ⟨usage, hm, he⟩ := List.mem_map.mp hk
    simpa only [he] using hu usage hm

theorem streamRefs_deferred (state : Nat) (deferMap : DeferMap) (refs : List Nat)
    (path : ResponsePath) (result : Result (List (Name × ResponseValue)))
    (children : Work) (hm : DeferMapBefore state deferMap)
    (hc : StreamRefsFrom state children ∧ StreamOwnersOrdered children)
    : StreamRefsFrom state
        (.executionGroup (refs.filterMap (lookupDeferredFragment? deferMap)) path result
          children)
      ∧ StreamOwnersOrdered
          (.executionGroup (refs.filterMap (lookupDeferredFragment? deferMap)) path result
            children) := by
  simp only [StreamRefsFrom, StreamOwnersOrdered]
  refine ⟨hc.1, hc.1.ownersBefore ?_, hc.2⟩
  intro ref hk
  obtain ⟨group, hg, rfl⟩ := List.mem_map.mp hk
  obtain ⟨_, _, hf⟩ := List.mem_filterMap.mp hg
  exact hm group (List.mem_of_find?_eq_some hf)

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
