import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryPlanning
import Proofs.GraphQL.IncrementalDelivery.Semantics.DeferRefs

/-! Ref bounds for generated work with both defer and stream tasks.
Deferred fragments retain their coherent ancestry; every stream item starts a fresh
ref region strictly after its owning stream node, including nested stream work.
-/

namespace GraphQL.IncrementalDelivery.Semantics.MixedRefs

open GraphQL.IncrementalDelivery.Execution
open Ancestry

def MapLower (lower : Nat) (deferMap : DeferMap) : Prop :=
  ∀ ref ∈ mapRefs deferMap, lower ≤ ref

def WorkAt (parents : Assignment) (lower bound : Nat) : Work → Prop
  | .empty => True
  | .combine left right =>
      WorkAt parents lower bound left ∧ WorkAt parents lower bound right
  | .executionGroup groups _ _ children =>
      groups ≠ []
      ∧ (∀ group ∈ groups, lower ≤ group.node.ref ∧ FragmentAt parents bound group)
      ∧ WorkAt parents lower bound children
  | .stream node items =>
      lower ≤ node.ref
      ∧ node.ref < bound
      ∧ ∀ item ∈ items, WorkAt parents (node.ref + 1) bound item.2
termination_by work => sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem WorkAt.extend {parents next : Assignment} {lower start finish : Nat} {work : Work}
    (h : WorkAt parents lower start work) (he : Extends start parents next)
    (hle : start ≤ finish)
    : WorkAt next lower finish work := by
  cases work <;> simp only [WorkAt] at h ⊢
  case combine left right => exact ⟨h.1.extend he hle, h.2.extend he hle⟩
  case executionGroup groups path result children =>
    exact ⟨h.1, fun g hg => ⟨(h.2.1 g hg).1, (h.2.1 g hg).2.extend he hle⟩,
      h.2.2.extend he hle⟩
  case stream node items =>
    exact ⟨h.1, Nat.lt_of_lt_of_le h.2.1 hle,
      fun item hi => (h.2.2 item hi).extend he hle⟩
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem hi
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem WorkAt.lower {parents : Assignment} {lower next bound : Nat} {work : Work}
    (h : WorkAt parents lower bound work) (hle : next ≤ lower)
    : WorkAt parents next bound work := by
  cases work <;> simp only [WorkAt] at h ⊢
  case combine left right => exact ⟨h.1.lower hle, h.2.lower hle⟩
  case executionGroup groups path result children =>
    exact ⟨h.1, fun g hg => ⟨Nat.le_trans hle (h.2.1 g hg).1, (h.2.1 g hg).2⟩,
      h.2.2.lower hle⟩
  case stream node items => exact ⟨Nat.le_trans hle h.1, h.2⟩
termination_by sizeOf work

def Output (parents : Assignment) (lower start : Nat) (work : Work) (finish : Nat)
    : Prop :=
  start ≤ finish
  ∧ ∃ next, Extends start parents next ∧ Valid next finish ∧ WorkAt next lower finish work

def Completed (parents : Assignment) (lower start : Nat) (output : Completion α × Nat)
    : Prop :=
  Output parents lower start output.1.work output.2

theorem workAt_combine {parents : Assignment} {lower bound : Nat} {left right : Work}
    (hl : WorkAt parents lower bound left) (hr : WorkAt parents lower bound right)
    : WorkAt parents lower bound (.combine left right) := by
  rw [WorkAt]
  exact ⟨hl, hr⟩

theorem output_empty (parents : Assignment) (lower state : Nat) (hv : Valid parents state)
    : Output parents lower state .empty state :=
  ⟨Nat.le_refl _, parents, Extends.refl _ _, hv, by simp only [WorkAt]⟩

theorem workAt_completionCombine (parents : Assignment) (lower bound : Nat)
    (f : α → β → γ)
    (left : Completion α) (right : Completion β)
    (hl : WorkAt parents lower bound left.work)
    (hr : WorkAt parents lower bound right.work)
    : WorkAt parents lower bound (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine, Completion.error, WorkAt]
  exact ⟨hl, hr⟩

theorem workAt_map (parents : Assignment) (lower bound : Nat)
    (f : α → β) (completed : Completion α) (h : WorkAt parents lower bound completed.work)
    : WorkAt parents lower bound (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · simp only [Completion.error, WorkAt]
  · exact h

theorem workAt_catchNull (parents : Assignment) (lower bound : Nat)
    (f : α → ResponseValue) (completed : Completion α)
    (h : WorkAt parents lower bound completed.work)
    : WorkAt parents lower bound (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · simp only [WorkAt]
  · exact h

theorem workAt_nonNull (parents : Assignment) (lower bound : Nat)
    (completed : Completion ResponseValue) (h : WorkAt parents lower bound completed.work)
    : WorkAt parents lower bound completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · simp only [Completion.error, WorkAt]
  · exact h

theorem deferred_workAt (parents : Assignment) (lower bound : Nat) (deferMap : DeferMap)
    (refs : List Nat) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
    (hm : MapAt parents bound deferMap) (hl : MapLower lower deferMap) (hne : refs ≠ [])
    (hk : refs.Subset (mapRefs deferMap)) (hc : WorkAt parents lower bound children)
    : WorkAt parents lower bound
        (.executionGroup (refs.filterMap (lookupDeferredFragment? deferMap)) path result
          children) := by
  rw [WorkAt]
  refine ⟨?_, ?_, hc⟩
  · intro he
    have hrefs := filterMap_fragment_refs deferMap refs hk
    simp only [he, mapRefs, List.map_nil] at hrefs
    exact hne hrefs.symm
  · intro group hg
    obtain ⟨ref, href, hlookup⟩ := List.mem_filterMap.mp hg
    exact ⟨by simpa only [lookup_ref hlookup] using hl ref (hk href),
      (hm group (List.mem_of_find?_eq_some hlookup)).1⟩

theorem optionalUsageAt_before {parents : Assignment} {state : Nat} {deferMap : DeferMap}
    {usage : Option DeferUsage} (hv : Valid parents state)
    (hu : OptionalUsageAt parents state deferMap usage)
    : UsageBefore state usage := by
  intro actual ha
  have hh := hu actual ha
  exact ⟨hh.1, fun ancestor hm => (hv actual.ref hh.1 ancestor (hh.2.1.symm ▸ hm)).1⟩

theorem mapLower_new (lower state : Nat) (deferMap : DeferMap) (usages : List DeferUsage)
    (path : ResponsePath) (hl : MapLower lower deferMap) (hle : lower ≤ state)
    (hu : ∀ usage ∈ usages, state ≤ usage.ref)
    : MapLower lower (getNewDeferMap usages path deferMap) := by
  intro ref hk
  rw [getNewDeferMap_refs] at hk
  rcases List.mem_append.mp hk with hk | hk
  · exact hl ref hk
  · obtain ⟨usage, hm, rfl⟩ := List.mem_map.mp hk
    exact Nat.le_trans hle (hu usage hm)

/-- Task refs anywhere in the work tree, including not-yet-registered stream items.
Ancestor placeholders are metadata, not additional task-ref occurrences.
-/
inductive TaskRef (ref : NodeRef) : Work → Prop where
  | combine_left {left right : Work}
    : TaskRef ref left → TaskRef ref (.combine left right)
  | combine_right {left right : Work}
    : TaskRef ref right → TaskRef ref (.combine left right)
  | deferred_here {groups : List DeferredFragment} {path : ResponsePath}
    {result : Result (List (Name × ResponseValue))} {children : Work}
    {group : DeferredFragment}
    : group ∈ groups → group.node.ref = ref
      → TaskRef ref (.executionGroup groups path result children)
  | deferred_child {groups : List DeferredFragment} {path : ResponsePath}
    {result : Result (List (Name × ResponseValue))} {children : Work}
    : TaskRef ref children → TaskRef ref (.executionGroup groups path result children)
  | stream_here {node : DeliveryNode} {items : List (Result ResponseValue × Work)}
    : node.ref = ref → TaskRef ref (.stream node items)
  | stream_child {node : DeliveryNode} {items : List (Result ResponseValue × Work)}
    {item : Result ResponseValue × Work}
    : item ∈ items → TaskRef ref item.2 → TaskRef ref (.stream node items)

theorem WorkAt.ref_bounds {parents : Assignment} {lower bound : Nat} {ref : NodeRef}
    {work : Work}
    (h : WorkAt parents lower bound work) (hk : TaskRef ref work)
    : lower ≤ ref ∧ ref < bound := by
  induction hk generalizing lower with
  | combine_left _ ih =>
      rw [WorkAt] at h; exact ih h.1
  | combine_right _ ih =>
      rw [WorkAt] at h; exact ih h.2
  | deferred_here hg he =>
      rw [WorkAt] at h
      rw [← he]
      exact ⟨(h.2.1 _ hg).1, (h.2.1 _ hg).2.1⟩
  | deferred_child _ ih =>
      rw [WorkAt] at h; exact ih h.2.2
  | stream_here he =>
      rw [WorkAt] at h; rw [← he]; exact ⟨h.1, h.2.1⟩
  | stream_child hi _ ih =>
      rw [WorkAt] at h
      have hh := ih (h.2.2 _ hi)
      exact ⟨Nat.le_trans h.1 (Nat.le_trans (Nat.le_succ _) hh.1), hh.2⟩

theorem WorkAt.stream_child_fresh {parents : Assignment} {lower bound : Nat}
    {node : DeliveryNode} {items : List (Result ResponseValue × Work)}
    (h : WorkAt parents lower bound (.stream node items))
    {item : Result ResponseValue × Work} (hi : item ∈ items) {ref : NodeRef}
    (hk : TaskRef ref item.2)
    : node.ref < ref := by
  rw [WorkAt] at h
  exact (h.2.2 item hi).ref_bounds hk |>.1

theorem WorkAt.fragment_ancestors_ordered {parents : Assignment} {lower bound : Nat}
    {groups : List DeferredFragment} {path : ResponsePath}
    {result : Result (List (Name × ResponseValue))} {children : Work}
    (h : WorkAt parents lower bound (.executionGroup groups path result children))
    (hv : Valid parents bound) {group : DeferredFragment} (hg : group ∈ groups)
    {ancestor : DeliveryNode} (ha : ancestor ∈ group.ancestors)
    : ancestor.ref < group.node.ref := by
  rw [WorkAt] at h
  have hf := (h.2.1 group hg).2
  exact (hv group.node.ref hf.1 ancestor.ref (hf.2 ▸ List.mem_map.mpr ⟨ancestor, ha, rfl⟩)).1

end GraphQL.IncrementalDelivery.Semantics.MixedRefs
