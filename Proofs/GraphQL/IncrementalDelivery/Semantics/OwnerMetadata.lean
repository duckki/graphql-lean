import Proofs.GraphQL.IncrementalDelivery.Semantics.PathOwnership
import Proofs.GraphQL.IncrementalDelivery.Semantics.DeferKeys

/-! Ghost path assignments for execution keys. Fresh allocations may extend an assignment
above the current supply, but cannot change any previously allocated key's attachment.
The assignment is proof-only and does not change execution or queue representation.
-/

namespace GraphQL.IncrementalDelivery.Semantics.OwnerPaths

open GraphQL.IncrementalDelivery.Execution

abbrev Assignment := Nat → ResponsePath

def Extends (bound : Nat) (old next : Assignment) : Prop :=
  ∀ key < bound, next key = old key

def Assigned (paths : Assignment) (bound : Nat) (node : DeliveryNode) : Prop :=
  node.key < bound ∧ paths node.key = node.path

def fragmentNodes (fragment : DeferredFragment) : List DeliveryNode :=
  fragment.node :: fragment.ancestors

def mapNodes (deferMap : DeferMap) : List DeliveryNode :=
  deferMap.flatMap fragmentNodes

def MapAt (paths : Assignment) (bound : Nat) (path : ResponsePath) (deferMap : DeferMap)
    : Prop :=
  ∀ node ∈ mapNodes deferMap, Assigned paths bound node ∧ Below node.path path

def WorkAt (paths : Assignment) (bound : Nat) : Work → Prop
  | .empty => True
  | .append left right => WorkAt paths bound left ∧ WorkAt paths bound right
  | .deferred groups path _ children =>
      MapAt paths bound path groups ∧ WorkAt paths bound children
  | .stream .. => False

def Output (paths : Assignment) (start : Nat) (work : Work) (finish : Nat) : Prop :=
  start ≤ finish ∧ ∃ next, Extends start paths next ∧ WorkAt next finish work

def Completed (paths : Assignment) (start : Nat) (output : Completion α × Nat) : Prop :=
  Output paths start output.1.work output.2

theorem Extends.refl (bound : Nat) (paths : Assignment) : Extends bound paths paths := by
  intro key hk
  rfl

theorem Extends.trans {first middle last : Assignment} {start finish : Nat}
    (h : Extends start first middle) (hnext : Extends finish middle last)
    (hle : start ≤ finish)
    : Extends start first last := by
  intro key hk
  exact (hnext key (by omega)).trans (h key hk)

theorem Assigned.extend {paths next : Assignment} {start finish : Nat}
    {node : DeliveryNode} (h : Assigned paths start node) (he : Extends start paths next)
    (hle : start ≤ finish)
    : Assigned next finish node :=
  ⟨by have := h.1; omega, (he node.key h.1).trans h.2⟩

theorem MapAt.extend {paths next : Assignment} {start finish : Nat} {path : ResponsePath}
    {deferMap : DeferMap} (h : MapAt paths start path deferMap)
    (he : Extends start paths next) (hle : start ≤ finish)
    : MapAt next finish path deferMap := by
  intro node hn
  exact ⟨(h node hn).1.extend he hle, (h node hn).2⟩

theorem MapAt.below {paths : Assignment} {bound : Nat} {path next : ResponsePath}
    {deferMap : DeferMap} (h : MapAt paths bound path deferMap) (hp : Below path next)
    : MapAt paths bound next deferMap := by
  intro node hn
  refine ⟨(h node hn).1, ?_⟩
  obtain ⟨left, hl⟩ := (h node hn).2
  obtain ⟨right, hr⟩ := hp
  exact ⟨left ++ right, by simp [hr, hl, List.append_assoc]⟩

theorem WorkAt.extend {paths next : Assignment} {start finish : Nat} {work : Work}
    (h : WorkAt paths start work) (he : Extends start paths next) (hle : start ≤ finish)
    : WorkAt next finish work := by
  cases work with
  | empty => trivial
  | append left right => exact ⟨h.1.extend he hle, h.2.extend he hle⟩
  | deferred groups path result children => exact ⟨h.1.extend he hle, h.2.extend he hle⟩
  | stream node items => exact False.elim h
termination_by sizeOf work

theorem mapAt_lookup {paths : Assignment} {bound : Nat} {path : ResponsePath}
    {deferMap : DeferMap} (h : MapAt paths bound path deferMap) (key : Nat)
    (fragment : DeferredFragment)
    (hf : lookupDeferredFragment? deferMap key = some fragment)
    : MapAt paths bound path [fragment] := by
  have hm := List.mem_of_find?_eq_some hf
  intro node hn
  apply h node
  simp only [mapNodes, List.mem_flatMap] at hn ⊢
  obtain ⟨f, hf, hn⟩ := hn
  simp only [List.mem_singleton] at hf
  subst f
  exact ⟨fragment, hm, hn⟩

theorem mapAt_filterMap {paths : Assignment} {bound : Nat} {path : ResponsePath}
    {deferMap : DeferMap} (h : MapAt paths bound path deferMap) (keys : List Nat)
    : MapAt paths bound path (keys.filterMap (lookupDeferredFragment? deferMap)) := by
  intro node hn
  obtain ⟨fragment, hf, hn⟩ := List.mem_flatMap.mp hn
  obtain ⟨key, _, hk⟩ := List.mem_filterMap.mp hf
  exact mapAt_lookup h key fragment hk node (by simp [mapNodes, hn])

theorem mapAt_new (paths : Assignment) (start finish : Nat) (path : ResponsePath)
    (deferMap : DeferMap) (usages : List DeferUsage)
    (h : MapAt paths start path deferMap) (hle : start ≤ finish)
    (hu : ∀ usage ∈ usages, start ≤ usage.key ∧ usage.key < finish)
    : let next := fun key => if start ≤ key then path else paths key
      Extends start paths next
      ∧ MapAt next finish path (getNewDeferMap usages path deferMap) := by
  let next : Assignment := fun key => if start ≤ key then path else paths key
  have he : Extends start paths next := by intro key hk; simp [next, Nat.not_le.mpr hk]
  refine ⟨he, ?_⟩
  have hm := h.extend he hle
  clear h
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => exact hm
  | cons usage rest ih =>
      rw [List.foldl_cons]
      apply ih _ (fun u hh => hu u (List.mem_cons_of_mem usage hh))
      · intro node hn
        simp only [mapNodes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.mem_append, fragmentNodes, List.mem_cons] at hn
        rcases hn with hn | rfl | hn
        · exact hm node hn
        · exact ⟨⟨(hu usage (by simp)).2, by simp [next, (hu usage (by simp)).1]⟩,
            ⟨[], by simp⟩⟩
        · obtain ⟨key, _, hk⟩ := List.mem_filterMap.mp hn
          obtain ⟨fragment, hf, hn⟩ := Option.map_eq_some_iff.mp hk
          subst node
          exact mapAt_lookup hm key fragment hf fragment.node (by simp [mapNodes, fragmentNodes])

theorem output_empty (paths : Assignment) (state : Nat)
    : Output paths state .empty state :=
  ⟨Nat.le_refl _, paths, Extends.refl _ _, trivial⟩

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

end GraphQL.IncrementalDelivery.Semantics.OwnerPaths
