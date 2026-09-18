import Proofs.GraphQL.IncrementalDelivery.Semantics.MixedWorkKeys

/-! Deferred dependency continuity stops at stream-item boundaries.
Every deferred child key reuses an enclosing task key or descends from one. Stream
items restart defer context, so their internal continuity is checked separately.
-/

namespace GraphQL.IncrementalDelivery.Semantics.GeneralScheduling

open GraphQL.IncrementalDelivery.Execution
open Ancestry

def DeferUnder (parents : Assignment) (owners : List Nat) : Work → Prop
  | .empty => True
  | .append left right => DeferUnder parents owners left ∧ DeferUnder parents owners right
  | .deferred groups _ _ children =>
      (∀ group ∈ groups, Descends parents owners group.node.key)
      ∧ DeferUnder parents owners children
  | .stream .. => True

def DeferContinuous (parents : Assignment) : Work → Prop
  | .empty => True
  | .append left right => DeferContinuous parents left ∧ DeferContinuous parents right
  | .deferred groups _ _ children =>
      DeferUnder parents (mapKeys groups) children ∧ DeferContinuous parents children
  | .stream _ items => ∀ item ∈ items, DeferContinuous parents item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

/-- Deferred task keys in this defer context, excluding stream nodes and their items. -/
def deferRegionKeys : Work → List Nat
  | .empty => []
  | .append left right => deferRegionKeys left ++ deferRegionKeys right
  | .deferred groups _ _ children => mapKeys groups ++ deferRegionKeys children
  | .stream .. => []

theorem DeferUnder.key_supported {parents : Assignment} {owners : List Nat} {work : Work}
    (h : DeferUnder parents owners work) {key : Nat} (hk : key ∈ deferRegionKeys work)
    : Descends parents owners key := by
  cases work with
  | empty => exact False.elim (List.not_mem_nil hk)
  | append left right =>
      rcases List.mem_append.mp hk with hk | hk
      · exact h.1.key_supported hk
      · exact h.2.key_supported hk
  | deferred groups path result children =>
      rcases List.mem_append.mp hk with hk | hk
      · obtain ⟨group, hg, he⟩ := List.mem_map.mp hk
        simpa only [he] using h.1 group hg
      · exact h.2.key_supported hk
  | stream node items => exact False.elim (List.not_mem_nil hk)
termination_by sizeOf work

theorem DeferContinuous.child_key_supported {parents : Assignment}
    {groups : List DeferredFragment} {path : ResponsePath}
    {result : Result (List (Name × ResponseValue))} {children : Work}
    (h : DeferContinuous parents (.deferred groups path result children))
    {key : Nat} (hk : key ∈ deferRegionKeys children)
    : ∃ owner ∈ mapKeys groups, owner = key ∨ owner ∈ parents key := by
  rw [DeferContinuous] at h
  exact h.1.key_supported hk

theorem DeferUnder.extend {parents next : Assignment} {lower start finish : Nat}
    {owners : List Nat} {work : Work} (h : DeferUnder parents owners work)
    (hw : MixedKeys.WorkAt parents lower start work) (he : Extends start parents next)
    (hle : start ≤ finish)
    : DeferUnder next owners work := by
  cases work with
  | empty => trivial
  | append left right =>
      rw [MixedKeys.WorkAt] at hw
      exact ⟨h.1.extend hw.1 he hle, h.2.extend hw.2 he hle⟩
  | deferred groups path result children =>
      rw [MixedKeys.WorkAt] at hw
      refine ⟨?_, h.2.extend hw.2.2 he hle⟩
      intro group hg
      simpa only [Descends, he group.node.key (hw.2.1 group hg).2.1] using h.1 group hg
  | stream node items => trivial
termination_by sizeOf work

theorem DeferUnder.mono {parents : Assignment} {lower bound : Nat}
    {inner outer : List Nat} {work : Work} (h : DeferUnder parents inner work)
    (hw : MixedKeys.WorkAt parents lower bound work) (hv : Valid parents bound)
    (hs : ∀ owner ∈ inner, Descends parents outer owner)
    : DeferUnder parents outer work := by
  cases work with
  | empty => trivial
  | append left right =>
      rw [MixedKeys.WorkAt] at hw
      exact ⟨h.1.mono hw.1 hv hs, h.2.mono hw.2 hv hs⟩
  | deferred groups path result children =>
      rw [MixedKeys.WorkAt] at hw
      exact ⟨fun group hg => descends_trans hv (hw.2.1 group hg).2.1 (h.1 group hg) hs,
        h.2.mono hw.2.2 hv hs⟩
  | stream node items => trivial
termination_by sizeOf work

theorem DeferContinuous.extend {parents next : Assignment} {lower start finish : Nat}
    {work : Work} (h : DeferContinuous parents work)
    (hw : MixedKeys.WorkAt parents lower start work) (he : Extends start parents next)
    (hle : start ≤ finish)
    : DeferContinuous next work := by
  cases work <;> simp only [DeferContinuous, MixedKeys.WorkAt] at h hw ⊢
  case append left right => exact ⟨h.1.extend hw.1 he hle, h.2.extend hw.2 he hle⟩
  case deferred groups path result children => exact ⟨h.1.extend hw.2.2 he hle, h.2.extend hw.2.2 he hle⟩
  case stream node items => exact fun item hi => (h item hi).extend (hw.2.2 item hi) he hle
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem hi
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def DeferScoped (parents : Assignment) (owners : List Nat) (work : Work) : Prop :=
  owners = [] ∨ DeferUnder parents owners work

theorem DeferScoped.extend {parents next : Assignment} {lower start finish : Nat}
    {owners : List Nat} {work : Work} (h : DeferScoped parents owners work)
    (hw : MixedKeys.WorkAt parents lower start work) (he : Extends start parents next)
    (hle : start ≤ finish)
    : DeferScoped next owners work :=
  h.imp_right (fun hh => hh.extend hw he hle)

def ContinuousWork (parents : Assignment) (lower bound : Nat) (owners : List Nat)
    (work : Work)
    : Prop :=
  MixedKeys.WorkAt parents lower bound work
  ∧ DeferContinuous parents work
  ∧ DeferScoped parents owners work

theorem ContinuousWork.extend {parents next : Assignment} {lower start finish : Nat}
    {owners : List Nat} {work : Work} (h : ContinuousWork parents lower start owners work)
    (he : Extends start parents next) (hle : start ≤ finish)
    : ContinuousWork next lower finish owners work :=
  ⟨h.1.extend he hle, h.2.1.extend h.1 he hle, h.2.2.extend h.1 he hle⟩

def ContinuityOutput (parents : Assignment) (lower start : Nat) (owners : List Nat)
    (work : Work) (finish : Nat)
    : Prop :=
  start ≤ finish
  ∧ ∃ next,
      Extends start parents next
      ∧ Valid next finish
      ∧ ContinuousWork next lower finish owners work

def ContinuityCompleted (parents : Assignment) (lower start : Nat) (owners : List Nat)
    (output : Completion α × Nat)
    : Prop :=
  ContinuityOutput parents lower start owners output.1.work output.2

theorem continuous_empty (parents : Assignment) (lower bound : Nat) (owners : List Nat)
    : ContinuousWork parents lower bound owners .empty :=
  ⟨by simp [MixedKeys.WorkAt], by simp [DeferContinuous], Or.inr trivial⟩

theorem continuityOutput_empty (parents : Assignment) (lower state : Nat)
    (owners : List Nat) (hv : Valid parents state)
    : ContinuityOutput parents lower state owners .empty state :=
  ⟨
    Nat.le_refl _,
    parents,
    Extends.refl _ _,
    hv,
    continuous_empty parents lower state owners
  ⟩

theorem continuous_append {parents : Assignment} {lower bound : Nat} {owners : List Nat}
    {left right : Work} (hl : ContinuousWork parents lower bound owners left)
    (hr : ContinuousWork parents lower bound owners right)
    : ContinuousWork parents lower bound owners (.append left right) := by
  refine ⟨MixedKeys.workAt_append hl.1 hr.1, ?_, ?_⟩
  · rw [DeferContinuous]; exact ⟨hl.2.1, hr.2.1⟩
  · rcases hl.2.2 with he | hl
    · exact Or.inl he
    rcases hr.2.2 with he | hr
    · exact Or.inl he
    exact Or.inr ⟨hl, hr⟩

theorem continuous_combine (parents : Assignment) (lower bound : Nat) (owners : List Nat)
    (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : ContinuousWork parents lower bound owners left.work)
    (hr : ContinuousWork parents lower bound owners right.work)
    : ContinuousWork parents lower bound owners
        (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine]
  all_goals first | exact continuous_append hl hr | exact continuous_empty _ _ _ _

theorem continuous_map (parents : Assignment) (lower bound : Nat) (owners : List Nat)
    (f : α → β) (completed : Completion α)
    (h : ContinuousWork parents lower bound owners completed.work)
    : ContinuousWork parents lower bound owners (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · exact continuous_empty _ _ _ _
  · exact h

theorem continuous_catchNull (parents : Assignment) (lower bound : Nat)
    (owners : List Nat) (f : α → ResponseValue) (completed : Completion α)
    (h : ContinuousWork parents lower bound owners completed.work)
    : ContinuousWork parents lower bound owners (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · exact continuous_empty _ _ _ _
  · exact h

theorem continuous_nonNull (parents : Assignment) (lower bound : Nat) (owners : List Nat)
    (completed : Completion ResponseValue)
    (h : ContinuousWork parents lower bound owners completed.work)
    : ContinuousWork parents lower bound owners completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · exact continuous_empty _ _ _ _
  · exact h

theorem continuous_deferred (parents : Assignment) (lower bound : Nat)
    (deferMap : DeferMap) (keys owners : List Nat) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
    (hv : Valid parents bound) (hm : MapAt parents bound deferMap)
    (hl : MixedKeys.MapLower lower deferMap) (hne : keys ≠ [])
    (hk : keys.Subset (mapKeys deferMap))
    (hs : owners = [] ∨ ∀ key ∈ keys, Descends parents owners key)
    (hc : ContinuousWork parents lower bound keys children)
    : ContinuousWork parents lower bound owners
        (.deferred (keys.filterMap (lookupDeferredFragment? deferMap)) path result
          children) := by
  have hkeys := filterMap_fragment_keys deferMap keys hk
  have hchildren := hc.2.2.resolve_left hne
  refine ⟨MixedKeys.deferred_workAt parents lower bound deferMap keys path result children hm hl hne hk hc.1, ?_, ?_⟩
  · rw [DeferContinuous, hkeys]
    exact ⟨hchildren, hc.2.1⟩
  · rcases hs with hs | hs
    · exact Or.inl hs
    · refine Or.inr ⟨?_, hchildren.mono hc.1 hv hs⟩
      intro group hg
      obtain ⟨key, hk, he⟩ := List.mem_filterMap.mp hg
      simpa only [lookup_key he] using hs key hk

theorem continuous_stream (parents : Assignment) (lower bound : Nat) (owners : List Nat)
    (node : DeliveryNode) (items : List (Result ResponseValue × Work))
    (hl : lower ≤ node.key) (hb : node.key < bound)
    (hi
      : ∀ item ∈ items,
          MixedKeys.WorkAt parents (node.key + 1) bound item.2
          ∧ DeferContinuous parents item.2)
    : ContinuousWork parents lower bound owners (.stream node items) := by
  refine ⟨?_, ?_, Or.inr trivial⟩
  · rw [MixedKeys.WorkAt]; exact ⟨hl, hb, fun item hm => (hi item hm).1⟩
  · rw [DeferContinuous]; exact fun item hm => (hi item hm).2

end GraphQL.IncrementalDelivery.Semantics.GeneralScheduling
