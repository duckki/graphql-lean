import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamAllocations

/-! Execution refs have disjoint stream and defer-metadata roles.
Defer metadata includes ancestor placeholders, not just contributing task refs.
Bounds allow role assignments to extend only at fresh execution allocations.
-/

namespace GraphQL.IncrementalDelivery.Semantics.RefRoles

open GraphQL.IncrementalDelivery.Execution
open GeneralScheduling

abbrev Assignment := Nat → Bool

def Extends (bound : Nat) (old next : Assignment) : Prop :=
  ∀ ref < bound, next ref = old ref

def fragmentRefs (fragment : DeferredFragment) : List Nat :=
  fragment.node.ref :: fragment.ancestors.map DeliveryNode.ref

def deferMetadataRefs : Work → List Nat
  | .empty => []
  | .combine left right => deferMetadataRefs left ++ deferMetadataRefs right
  | .executionGroup groups _ _ children =>
      groups.flatMap fragmentRefs ++ deferMetadataRefs children
  | .stream _ items => items.flatMap (fun item => deferMetadataRefs item.2)
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def WorkRoles (roles : Assignment) : Work → Prop
  | .empty => True
  | .combine left right => WorkRoles roles left ∧ WorkRoles roles right
  | .executionGroup groups _ _ children =>
      (∀ group ∈ groups,
        roles group.node.ref = false
        ∧ ∀ ancestor ∈ group.ancestors, roles ancestor.ref = false)
      ∧ WorkRoles roles children
  | .stream node items => roles node.ref = true ∧ ∀ item ∈ items, WorkRoles roles item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def RefsAt (roles : Assignment) (bound : Nat) (role : Bool) (refs : List Nat) : Prop :=
  ∀ ref ∈ refs, ref < bound ∧ roles ref = role

def MapAt (roles : Assignment) (bound : Nat) (deferMap : DeferMap) : Prop :=
  RefsAt roles bound false (deferMap.flatMap fragmentRefs)

def WorkAt (roles : Assignment) (bound : Nat) (work : Work) : Prop :=
  RefsAt roles bound true (streamAllocationRefs work)
  ∧ RefsAt roles bound false (deferMetadataRefs work)

theorem Extends.refl (roles : Assignment) (bound : Nat) : Extends bound roles roles :=
  fun _ _ => rfl

theorem Extends.trans {first middle last : Assignment} {start finish : Nat}
    (h : Extends start first middle) (hn : Extends finish middle last)
    (hle : start ≤ finish)
    : Extends start first last :=
  fun ref hk => (hn ref (Nat.lt_of_lt_of_le hk hle)).trans (h ref hk)

theorem RefsAt.extend {roles next : Assignment} {start finish : Nat} {role : Bool}
    {refs : List Nat} (h : RefsAt roles start role refs) (he : Extends start roles next)
    (hle : start ≤ finish)
    : RefsAt next finish role refs := by
  intro ref hk
  have hh := h ref hk
  exact ⟨Nat.lt_of_lt_of_le hh.1 hle, (he ref hh.1).trans hh.2⟩

theorem RefsAt.append {roles : Assignment} {bound : Nat} {role : Bool}
    {left right : List Nat} (hl : RefsAt roles bound role left)
    (hr : RefsAt roles bound role right)
    : RefsAt roles bound role (left ++ right) := by
  intro ref hk
  exact (List.mem_append.mp hk).elim (hl ref) (hr ref)

theorem MapAt.extend {roles next : Assignment} {start finish : Nat} {deferMap : DeferMap}
    (h : MapAt roles start deferMap) (he : Extends start roles next)
    (hle : start ≤ finish)
    : MapAt next finish deferMap :=
  RefsAt.extend h he hle

theorem MapAt.fragment {roles : Assignment} {bound : Nat} {deferMap : DeferMap}
    (h : MapAt roles bound deferMap) {fragment : DeferredFragment}
    (hf : fragment ∈ deferMap)
    : RefsAt roles bound false (fragmentRefs fragment) :=
  fun ref hk => h ref (List.mem_flatMap.mpr ⟨fragment, hf, hk⟩)

theorem WorkAt.extend {roles next : Assignment} {start finish : Nat} {work : Work}
    (h : WorkAt roles start work) (he : Extends start roles next) (hle : start ≤ finish)
    : WorkAt next finish work :=
  ⟨h.1.extend he hle, h.2.extend he hle⟩

def markDefer (roles : Assignment) (start : Nat) : Assignment :=
  fun ref => if ref < start then roles ref else false

theorem markDefer_extends (roles : Assignment) (start : Nat)
    : Extends start roles (markDefer roles start) := by
  intro ref hk
  simp [markDefer, hk]

def markStream (roles : Assignment) (state : Nat) : Assignment :=
  fun ref => if ref = state then true else roles ref

theorem markStream_extends (roles : Assignment) (state : Nat)
    : Extends state roles (markStream roles state) := by
  intro ref hk
  simp [markStream, Nat.ne_of_lt hk]

theorem mapAt_new (roles : Assignment) (bound : Nat) (deferMap : DeferMap)
    (usages : List DeferUsage) (path : ResponsePath) (hm : MapAt roles bound deferMap)
    (hu : ∀ usage ∈ usages, usage.ref < bound ∧ roles usage.ref = false)
    : MapAt roles bound (getNewDeferMap usages path deferMap) := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => exact hm
  | cons usage rest ih =>
      apply ih
      · simp only [MapAt, List.flatMap_append]
        apply RefsAt.append hm
        intro ref hk
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, fragmentRefs, List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact hu usage (by simp)
        · obtain ⟨ancestor, ha, rfl⟩ := List.mem_map.mp hk
          obtain ⟨oldRef, _, hlookup⟩ := List.mem_filterMap.mp ha
          cases hl : lookupDeferredFragment? deferMap oldRef with
          | none => simp [hl] at hlookup
          | some fragment =>
              have he : fragment.node = ancestor := by simpa [hl] using hlookup
              subst ancestor
              exact hm.fragment (List.mem_of_find?_eq_some hl) _ (by simp [fragmentRefs])
      · exact fun u hu' => hu u (List.mem_cons_of_mem usage hu')

theorem mapAt_collection {roles : Assignment} {start finish : Nat} {deferMap : DeferMap}
    (hm : MapAt roles start deferMap) (hle : start ≤ finish) (usages : List DeferUsage)
    (hu : ∀ usage ∈ usages, start ≤ usage.ref ∧ usage.ref < finish) (path : ResponsePath)
    : MapAt (markDefer roles start) finish (getNewDeferMap usages path deferMap) := by
  apply mapAt_new _ _ _ _ _ (hm.extend (markDefer_extends roles start) hle)
  intro usage husage
  have hh := hu usage husage
  exact ⟨hh.2, by simp [markDefer, Nat.not_lt.mpr hh.1]⟩

def Output (roles : Assignment) (start : Nat) (work : Work) (finish : Nat) : Prop :=
  start ≤ finish ∧ ∃ next, Extends start roles next ∧ WorkAt next finish work

def Completed (roles : Assignment) (start : Nat) (output : Completion α × Nat) : Prop :=
  Output roles start output.1.work output.2

theorem workAt_empty (roles : Assignment) (bound : Nat) : WorkAt roles bound .empty := by
  simp [WorkAt, RefsAt, streamAllocationRefs, deferMetadataRefs]

theorem output_empty (roles : Assignment) (state : Nat)
    : Output roles state .empty state :=
  ⟨Nat.le_refl _, roles, Extends.refl _ _, workAt_empty _ _⟩

theorem workAt_combine {roles : Assignment} {bound : Nat} {left right : Work}
    (hl : WorkAt roles bound left) (hr : WorkAt roles bound right)
    : WorkAt roles bound (.combine left right) := by
  simpa only [WorkAt, streamAllocationRefs, deferMetadataRefs]
    using And.intro (hl.1.append hr.1) (hl.2.append hr.2)

theorem workAt_completionCombine (roles : Assignment) (bound : Nat) (f : α → β → γ)
    (left : Completion α) (right : Completion β) (hl : WorkAt roles bound left.work)
    (hr : WorkAt roles bound right.work)
    : WorkAt roles bound (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine]
  all_goals first | exact workAt_combine hl hr | exact workAt_empty _ _

theorem workAt_map (roles : Assignment) (bound : Nat) (f : α → β)
    (completed : Completion α) (h : WorkAt roles bound completed.work)
    : WorkAt roles bound (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · exact workAt_empty _ _
  · exact h

theorem workAt_catchNull (roles : Assignment) (bound : Nat) (f : α → ResponseValue)
    (completed : Completion α) (h : WorkAt roles bound completed.work)
    : WorkAt roles bound (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · exact workAt_empty _ _
  · exact h

theorem workAt_nonNull (roles : Assignment) (bound : Nat)
    (completed : Completion ResponseValue) (h : WorkAt roles bound completed.work)
    : WorkAt roles bound completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · exact workAt_empty _ _
  · exact h

theorem workAt_deferred (roles : Assignment) (bound : Nat) (deferMap : DeferMap)
    (refs : List Nat) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
    (hm : MapAt roles bound deferMap) (hc : WorkAt roles bound children)
    : WorkAt roles bound
        (.executionGroup (refs.filterMap (lookupDeferredFragment? deferMap)) path result
          children) := by
  refine ⟨by simpa only [streamAllocationRefs] using hc.1, ?_⟩
  rw [deferMetadataRefs]
  apply RefsAt.append _ hc.2
  intro ref hk
  obtain ⟨fragment, hf, href⟩ := List.mem_flatMap.mp hk
  obtain ⟨_, _, hl⟩ := List.mem_filterMap.mp hf
  exact hm.fragment (List.mem_of_find?_eq_some hl) ref href

theorem workAt_stream (roles : Assignment) (bound : Nat) (node : DeliveryNode)
    (items : List (Result ResponseValue × Work))
    (hn : node.ref < bound ∧ roles node.ref = true)
    (hi : ∀ item ∈ items, WorkAt roles bound item.2)
    : WorkAt roles bound (.stream node items) := by
  constructor
  · intro ref hk
    rw [streamAllocationRefs] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hn
    · obtain ⟨item, hm, hk⟩ := List.mem_flatMap.mp hk
      exact (hi item hm).1 ref hk
  · intro ref hk
    rw [deferMetadataRefs] at hk
    obtain ⟨item, hm, hk⟩ := List.mem_flatMap.mp hk
    exact (hi item hm).2 ref hk

theorem WorkAt.roles {roles : Assignment} {bound : Nat} {work : Work}
    (h : WorkAt roles bound work)
    : WorkRoles roles work := by
  cases work with
  | empty => simp [WorkRoles]
  | combine left right =>
      rw [WorkRoles]
      have hl : WorkAt roles bound left := ⟨
        fun ref hk => h.1 ref (by rw [streamAllocationRefs]; exact List.mem_append_left _ hk),
        fun ref hk => h.2 ref (by rw [deferMetadataRefs]; exact List.mem_append_left _ hk)⟩
      have hr : WorkAt roles bound right := ⟨
        fun ref hk => h.1 ref (by rw [streamAllocationRefs]; exact List.mem_append_right _ hk),
        fun ref hk => h.2 ref (by rw [deferMetadataRefs]; exact List.mem_append_right _ hk)⟩
      exact ⟨hl.roles, hr.roles⟩
  | executionGroup groups path result children =>
      rw [WorkRoles]
      have hg (group : DeferredFragment) (hm : group ∈ groups) : RefsAt roles bound false (fragmentRefs group) := by
        intro ref hk
        apply h.2 ref
        rw [deferMetadataRefs]
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨group, hm, hk⟩)
      have hc : WorkAt roles bound children := ⟨by simpa only [streamAllocationRefs] using h.1,
        fun ref hk => h.2 ref (by rw [deferMetadataRefs]; exact List.mem_append_right _ hk)⟩
      refine ⟨?_, hc.roles⟩
      intro group hm
      refine ⟨(hg group hm _ (by simp [fragmentRefs])).2, ?_⟩
      intro ancestor ha
      exact (hg group hm ancestor.ref
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ancestor, ha, rfl⟩))).2
  | stream node items =>
      rw [WorkRoles]
      refine ⟨
        (h.1 node.ref (by rw [streamAllocationRefs]; exact List.mem_cons_self)).2,
        ?_
      ⟩
      intro item hi
      have hc : WorkAt roles bound item.2 := ⟨
        fun ref hk => h.1 ref (by rw [streamAllocationRefs]; exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨item, hi, hk⟩)),
        fun ref hk => h.2 ref (by rw [deferMetadataRefs]; exact List.mem_flatMap.mpr ⟨item, hi, hk⟩)⟩
      exact hc.roles
termination_by sizeOf work
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem hi
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

theorem WorkAt.separate {roles : Assignment} {bound : Nat} {work : Work}
    (h : WorkAt roles bound work) {ref : NodeRef} (hs : ref ∈ streamAllocationRefs work)
    : ref ∉ deferMetadataRefs work := by
  intro hd
  have ht := (h.1 ref hs).2
  have hf := (h.2 ref hd).2
  simp [ht] at hf

end GraphQL.IncrementalDelivery.Semantics.RefRoles
