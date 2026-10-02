import Proofs.GraphQL.IncrementalDelivery.Semantics.DeferKeys
import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryMetadata
import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning

/-! Stream owner keys precede the stream nodes registered under them.
Only streams reached through combine nodes inherit the current owner list; deferred
tasks establish their own owner list when their children are registered.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution

def OwnersBefore (owners : List Nat) : Work → Prop
  | .empty => True
  | .combine left right => OwnersBefore owners left ∧ OwnersBefore owners right
  | .executionGroup .. => True
  | .stream node _ => ∀ owner ∈ owners, owner < node.key

def StreamOwnersOrdered : Work → Prop
  | .empty => True
  | .combine left right => StreamOwnersOrdered left ∧ StreamOwnersOrdered right
  | .executionGroup groups _ _ children =>
      OwnersBefore (groups.map (·.node.key)) children ∧ StreamOwnersOrdered children
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

def StreamKeysFrom (start : Nat) : Work → Prop
  | .empty => True
  | .combine left right => StreamKeysFrom start left ∧ StreamKeysFrom start right
  | .executionGroup _ _ _ children => StreamKeysFrom start children
  | .stream node items => start ≤ node.key ∧ ∀ item ∈ items, StreamKeysFrom start item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem StreamKeysFrom.mono {start next : Nat} {work : Work}
    (h : StreamKeysFrom start work) (hle : next ≤ start)
    : StreamKeysFrom next work := by
  cases work <;> simp only [StreamKeysFrom] at h ⊢
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

theorem StreamKeysFrom.ownersBefore {start : Nat} {work : Work}
    (h : StreamKeysFrom start work) {owners : List Nat}
    (ho : ∀ owner ∈ owners, owner < start)
    : OwnersBefore owners work := by
  cases work with
  | empty => trivial
  | combine left right =>
      rw [StreamKeysFrom] at h
      exact ⟨h.1.ownersBefore ho, h.2.ownersBefore ho⟩
  | executionGroup groups path result children => trivial
  | stream node items =>
      rw [StreamKeysFrom] at h
      exact fun owner hm => Nat.lt_of_lt_of_le (ho owner hm) h.1
termination_by sizeOf work

theorem ownersBefore_nil (work : Work) : OwnersBefore [] work := by
  cases work with
  | empty => trivial
  | combine left right => exact ⟨ownersBefore_nil left, ownersBefore_nil right⟩
  | executionGroup groups path result children => trivial
  | stream node items => simp [OwnersBefore]
termination_by sizeOf work

def StreamKeyOutput (start : Nat) (work : Work) (finish : Nat) : Prop :=
  start ≤ finish ∧ StreamKeysFrom start work ∧ StreamOwnersOrdered work

def StreamKeyCompleted (start : Nat) (output : Completion α × Nat) : Prop :=
  StreamKeyOutput start output.1.work output.2

theorem streamKeyOutput_empty (state : Nat) : StreamKeyOutput state .empty state :=
  ⟨Nat.le_refl _, by simp [StreamKeysFrom], by simp [StreamOwnersOrdered]⟩

theorem streamKeys_combine {start : Nat} {left right : Work}
    (hl : StreamKeysFrom start left ∧ StreamOwnersOrdered left)
    (hr : StreamKeysFrom start right ∧ StreamOwnersOrdered right)
    : StreamKeysFrom start (.combine left right)
      ∧ StreamOwnersOrdered (.combine left right) := by
  simp only [StreamKeysFrom, StreamOwnersOrdered]
  exact ⟨⟨hl.1, hr.1⟩, hl.2, hr.2⟩

theorem streamKeys_completionCombine (start : Nat) (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : StreamKeysFrom start left.work ∧ StreamOwnersOrdered left.work)
    (hr : StreamKeysFrom start right.work ∧ StreamOwnersOrdered right.work)
    : StreamKeysFrom start (Completion.combine f left right).work
      ∧ StreamOwnersOrdered (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine]
  all_goals first
  | exact streamKeys_combine hl hr
  | simp [Completion.error, StreamKeysFrom, StreamOwnersOrdered]

theorem streamKeys_map (start : Nat) (f : α → β) (completed : Completion α)
    (h : StreamKeysFrom start completed.work ∧ StreamOwnersOrdered completed.work)
    : StreamKeysFrom start (completed.map f).work
      ∧ StreamOwnersOrdered (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · simp [Completion.error, StreamKeysFrom, StreamOwnersOrdered]
  · exact h

theorem streamKeys_catchNull (start : Nat) (f : α → ResponseValue)
    (completed : Completion α)
    (h : StreamKeysFrom start completed.work ∧ StreamOwnersOrdered completed.work)
    : StreamKeysFrom start (completed.catchNull f).work
      ∧ StreamOwnersOrdered (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · simp [StreamKeysFrom, StreamOwnersOrdered]
  · exact h

theorem streamKeys_nonNull (start : Nat) (completed : Completion ResponseValue)
    (h : StreamKeysFrom start completed.work ∧ StreamOwnersOrdered completed.work)
    : StreamKeysFrom start completed.nonNull.work
      ∧ StreamOwnersOrdered completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · simp [Completion.error, StreamKeysFrom, StreamOwnersOrdered]
  · exact h

def DeferMapBefore (state : Nat) (deferMap : DeferMap) : Prop :=
  ∀ fragment ∈ deferMap, fragment.node.key < state

theorem DeferMapBefore.mono {state next : Nat} {deferMap : DeferMap}
    (h : DeferMapBefore state deferMap) (hle : state ≤ next)
    : DeferMapBefore next deferMap :=
  fun fragment hf => Nat.lt_of_lt_of_le (h fragment hf) hle

theorem deferMapBefore_new {start finish : Nat} {deferMap : DeferMap}
    (h : DeferMapBefore start deferMap) (hle : start ≤ finish) (usages : List DeferUsage)
    (hu : ∀ usage ∈ usages, usage.key < finish) (path : ResponsePath)
    : DeferMapBefore finish (getNewDeferMap usages path deferMap) := by
  intro fragment hf
  have hk : fragment.node.key ∈ Ancestry.mapKeys (getNewDeferMap usages path deferMap) :=
    List.mem_map.mpr ⟨fragment, hf, rfl⟩
  rw [Ancestry.getNewDeferMap_keys] at hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨old, ho, he⟩ := List.mem_map.mp hk
    simpa only [he] using Nat.lt_of_lt_of_le (h old ho) hle
  · obtain ⟨usage, hm, he⟩ := List.mem_map.mp hk
    simpa only [he] using hu usage hm

theorem streamKeys_deferred (state : Nat) (deferMap : DeferMap) (keys : List Nat)
    (path : ResponsePath) (result : Result (List (Name × ResponseValue)))
    (children : Work) (hm : DeferMapBefore state deferMap)
    (hc : StreamKeysFrom state children ∧ StreamOwnersOrdered children)
    : StreamKeysFrom state
        (.executionGroup (keys.filterMap (lookupDeferredFragment? deferMap)) path result
          children)
      ∧ StreamOwnersOrdered
          (.executionGroup (keys.filterMap (lookupDeferredFragment? deferMap)) path result
            children) := by
  simp only [StreamKeysFrom, StreamOwnersOrdered]
  refine ⟨hc.1, hc.1.ownersBefore ?_, hc.2⟩
  intro key hk
  obtain ⟨group, hg, rfl⟩ := List.mem_map.mp hk
  obtain ⟨_, _, hf⟩ := List.mem_filterMap.mp hg
  exact hm group (List.mem_of_find?_eq_some hf)

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
