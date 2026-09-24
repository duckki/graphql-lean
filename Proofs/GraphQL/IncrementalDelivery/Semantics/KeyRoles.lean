import Proofs.GraphQL.IncrementalDelivery.Semantics.StreamAllocations

/-! Execution keys have disjoint stream and defer-metadata roles.
Defer metadata includes ancestor placeholders, not just contributing task keys.
Bounds allow role assignments to extend only at fresh execution allocations.
-/

namespace GraphQL.IncrementalDelivery.Semantics.KeyRoles

open GraphQL.IncrementalDelivery.Execution
open GeneralScheduling

abbrev Assignment := Nat → Bool

def Extends (bound : Nat) (old next : Assignment) : Prop :=
  ∀ key < bound, next key = old key

def fragmentKeys (fragment : DeferredFragment) : List Nat :=
  fragment.node.key :: fragment.ancestors.map DeliveryNode.key

def deferMetadataKeys : Work → List Nat
  | .empty => []
  | .combine left right => deferMetadataKeys left ++ deferMetadataKeys right
  | .executionGroup groups _ _ children =>
      groups.flatMap fragmentKeys ++ deferMetadataKeys children
  | .stream _ items => items.flatMap (fun item => deferMetadataKeys item.2)
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
        roles group.node.key = false
        ∧ ∀ ancestor ∈ group.ancestors, roles ancestor.key = false)
      ∧ WorkRoles roles children
  | .stream node items => roles node.key = true ∧ ∀ item ∈ items, WorkRoles roles item.2
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have hh := List.sizeOf_lt_of_mem ‹item ∈ items›
  rcases item with ⟨result, work⟩
  simp only [Prod.mk.sizeOf_spec] at hh
  dsimp only
  omega

def KeysAt (roles : Assignment) (bound : Nat) (role : Bool) (keys : List Nat) : Prop :=
  ∀ key ∈ keys, key < bound ∧ roles key = role

def MapAt (roles : Assignment) (bound : Nat) (deferMap : DeferMap) : Prop :=
  KeysAt roles bound false (deferMap.flatMap fragmentKeys)

def WorkAt (roles : Assignment) (bound : Nat) (work : Work) : Prop :=
  KeysAt roles bound true (streamAllocationKeys work)
  ∧ KeysAt roles bound false (deferMetadataKeys work)

theorem Extends.refl (roles : Assignment) (bound : Nat) : Extends bound roles roles :=
  fun _ _ => rfl

theorem Extends.trans {first middle last : Assignment} {start finish : Nat}
    (h : Extends start first middle) (hn : Extends finish middle last)
    (hle : start ≤ finish)
    : Extends start first last :=
  fun key hk => (hn key (Nat.lt_of_lt_of_le hk hle)).trans (h key hk)

theorem KeysAt.extend {roles next : Assignment} {start finish : Nat} {role : Bool}
    {keys : List Nat} (h : KeysAt roles start role keys) (he : Extends start roles next)
    (hle : start ≤ finish)
    : KeysAt next finish role keys := by
  intro key hk
  have hh := h key hk
  exact ⟨Nat.lt_of_lt_of_le hh.1 hle, (he key hh.1).trans hh.2⟩

theorem KeysAt.append {roles : Assignment} {bound : Nat} {role : Bool}
    {left right : List Nat} (hl : KeysAt roles bound role left)
    (hr : KeysAt roles bound role right)
    : KeysAt roles bound role (left ++ right) := by
  intro key hk
  exact (List.mem_append.mp hk).elim (hl key) (hr key)

theorem MapAt.extend {roles next : Assignment} {start finish : Nat} {deferMap : DeferMap}
    (h : MapAt roles start deferMap) (he : Extends start roles next)
    (hle : start ≤ finish)
    : MapAt next finish deferMap :=
  KeysAt.extend h he hle

theorem MapAt.fragment {roles : Assignment} {bound : Nat} {deferMap : DeferMap}
    (h : MapAt roles bound deferMap) {fragment : DeferredFragment}
    (hf : fragment ∈ deferMap)
    : KeysAt roles bound false (fragmentKeys fragment) :=
  fun key hk => h key (List.mem_flatMap.mpr ⟨fragment, hf, hk⟩)

theorem WorkAt.extend {roles next : Assignment} {start finish : Nat} {work : Work}
    (h : WorkAt roles start work) (he : Extends start roles next) (hle : start ≤ finish)
    : WorkAt next finish work :=
  ⟨h.1.extend he hle, h.2.extend he hle⟩

def markDefer (roles : Assignment) (start : Nat) : Assignment :=
  fun key => if key < start then roles key else false

theorem markDefer_extends (roles : Assignment) (start : Nat)
    : Extends start roles (markDefer roles start) := by
  intro key hk
  simp [markDefer, hk]

def markStream (roles : Assignment) (state : Nat) : Assignment :=
  fun key => if key = state then true else roles key

theorem markStream_extends (roles : Assignment) (state : Nat)
    : Extends state roles (markStream roles state) := by
  intro key hk
  simp [markStream, Nat.ne_of_lt hk]

theorem mapAt_new (roles : Assignment) (bound : Nat) (deferMap : DeferMap)
    (usages : List DeferUsage) (path : ResponsePath) (hm : MapAt roles bound deferMap)
    (hu : ∀ usage ∈ usages, usage.key < bound ∧ roles usage.key = false)
    : MapAt roles bound (getNewDeferMap usages path deferMap) := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => exact hm
  | cons usage rest ih =>
      apply ih
      · simp only [MapAt, List.flatMap_append]
        apply KeysAt.append hm
        intro key hk
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, fragmentKeys, List.mem_cons] at hk
        rcases hk with rfl | hk
        · exact hu usage (by simp)
        · obtain ⟨ancestor, ha, rfl⟩ := List.mem_map.mp hk
          obtain ⟨oldKey, _, hlookup⟩ := List.mem_filterMap.mp ha
          cases hl : lookupDeferredFragment? deferMap oldKey with
          | none => simp [hl] at hlookup
          | some fragment =>
              have he : fragment.node = ancestor := by simpa [hl] using hlookup
              subst ancestor
              exact hm.fragment (List.mem_of_find?_eq_some hl) _ (by simp [fragmentKeys])
      · exact fun u hu' => hu u (List.mem_cons_of_mem usage hu')

theorem mapAt_collection {roles : Assignment} {start finish : Nat} {deferMap : DeferMap}
    (hm : MapAt roles start deferMap) (hle : start ≤ finish) (usages : List DeferUsage)
    (hu : ∀ usage ∈ usages, start ≤ usage.key ∧ usage.key < finish) (path : ResponsePath)
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
  simp [WorkAt, KeysAt, streamAllocationKeys, deferMetadataKeys]

theorem output_empty (roles : Assignment) (state : Nat)
    : Output roles state .empty state :=
  ⟨Nat.le_refl _, roles, Extends.refl _ _, workAt_empty _ _⟩

theorem workAt_combine {roles : Assignment} {bound : Nat} {left right : Work}
    (hl : WorkAt roles bound left) (hr : WorkAt roles bound right)
    : WorkAt roles bound (.combine left right) := by
  simpa only [WorkAt, streamAllocationKeys, deferMetadataKeys]
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
    (keys : List Nat) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
    (hm : MapAt roles bound deferMap) (hc : WorkAt roles bound children)
    : WorkAt roles bound
        (.executionGroup (keys.filterMap (lookupDeferredFragment? deferMap)) path result
          children) := by
  refine ⟨by simpa only [streamAllocationKeys] using hc.1, ?_⟩
  rw [deferMetadataKeys]
  apply KeysAt.append _ hc.2
  intro key hk
  obtain ⟨fragment, hf, hkey⟩ := List.mem_flatMap.mp hk
  obtain ⟨_, _, hl⟩ := List.mem_filterMap.mp hf
  exact hm.fragment (List.mem_of_find?_eq_some hl) key hkey

theorem workAt_stream (roles : Assignment) (bound : Nat) (node : DeliveryNode)
    (items : List (Result ResponseValue × Work))
    (hn : node.key < bound ∧ roles node.key = true)
    (hi : ∀ item ∈ items, WorkAt roles bound item.2)
    : WorkAt roles bound (.stream node items) := by
  constructor
  · intro key hk
    rw [streamAllocationKeys] at hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hn
    · obtain ⟨item, hm, hk⟩ := List.mem_flatMap.mp hk
      exact (hi item hm).1 key hk
  · intro key hk
    rw [deferMetadataKeys] at hk
    obtain ⟨item, hm, hk⟩ := List.mem_flatMap.mp hk
    exact (hi item hm).2 key hk

theorem WorkAt.roles {roles : Assignment} {bound : Nat} {work : Work}
    (h : WorkAt roles bound work)
    : WorkRoles roles work := by
  cases work with
  | empty => simp [WorkRoles]
  | combine left right =>
      rw [WorkRoles]
      have hl : WorkAt roles bound left := ⟨
        fun key hk => h.1 key (by rw [streamAllocationKeys]; exact List.mem_append_left _ hk),
        fun key hk => h.2 key (by rw [deferMetadataKeys]; exact List.mem_append_left _ hk)⟩
      have hr : WorkAt roles bound right := ⟨
        fun key hk => h.1 key (by rw [streamAllocationKeys]; exact List.mem_append_right _ hk),
        fun key hk => h.2 key (by rw [deferMetadataKeys]; exact List.mem_append_right _ hk)⟩
      exact ⟨hl.roles, hr.roles⟩
  | executionGroup groups path result children =>
      rw [WorkRoles]
      have hg (group : DeferredFragment) (hm : group ∈ groups) : KeysAt roles bound false (fragmentKeys group) := by
        intro key hk
        apply h.2 key
        rw [deferMetadataKeys]
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨group, hm, hk⟩)
      have hc : WorkAt roles bound children := ⟨by simpa only [streamAllocationKeys] using h.1,
        fun key hk => h.2 key (by rw [deferMetadataKeys]; exact List.mem_append_right _ hk)⟩
      refine ⟨?_, hc.roles⟩
      intro group hm
      refine ⟨(hg group hm _ (by simp [fragmentKeys])).2, ?_⟩
      intro ancestor ha
      exact (hg group hm ancestor.key
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨ancestor, ha, rfl⟩))).2
  | stream node items =>
      rw [WorkRoles]
      refine ⟨
        (h.1 node.key (by rw [streamAllocationKeys]; exact List.mem_cons_self)).2,
        ?_
      ⟩
      intro item hi
      have hc : WorkAt roles bound item.2 := ⟨
        fun key hk => h.1 key (by rw [streamAllocationKeys]; exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨item, hi, hk⟩)),
        fun key hk => h.2 key (by rw [deferMetadataKeys]; exact List.mem_flatMap.mpr ⟨item, hi, hk⟩)⟩
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
    (h : WorkAt roles bound work) {key : Nat} (hs : key ∈ streamAllocationKeys work)
    : key ∉ deferMetadataKeys work := by
  intro hd
  have ht := (h.1 key hs).2
  have hf := (h.2 key hd).2
  simp [ht] at hf

end GraphQL.IncrementalDelivery.Semantics.KeyRoles
