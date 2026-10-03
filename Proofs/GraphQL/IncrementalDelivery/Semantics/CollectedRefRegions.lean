import Proofs.GraphQL.IncrementalDelivery.Semantics.RefRoles

/-! A collected defer map inherits only old metadata refs and freshly allocated
usage refs. Ancestor placeholders are looked up in the same growing map, so they
do not introduce refs from a different region. -/

namespace GraphQL.IncrementalDelivery.Semantics.RefRegions

open GraphQL.IncrementalDelivery.Execution

theorem mapRefs_new_property (property : Nat → Prop) (deferMap : DeferMap)
    (usages : List DeferUsage) (path : ResponsePath)
    (hm : ∀ ref ∈ deferMap.flatMap RefRoles.fragmentRefs, property ref)
    (hu : ∀ usage ∈ usages, property usage.ref)
    : ∀ ref ∈ (getNewDeferMap usages path deferMap).flatMap RefRoles.fragmentRefs,
        property ref := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => exact hm
  | cons usage rest ih =>
      apply ih
      · intro ref hk
        simp only [List.flatMap_append, List.mem_append] at hk
        rcases hk with hk | hk
        · exact hm ref hk
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            RefRoles.fragmentRefs, List.mem_cons] at hk
          rcases hk with rfl | hk
          · exact hu usage (by simp)
          · obtain ⟨ancestor, ha, rfl⟩ := List.mem_map.mp hk
            obtain ⟨oldRef, _, hlookup⟩ := List.mem_filterMap.mp ha
            cases hl : lookupDeferredFragment? deferMap oldRef with
            | none => simp [hl] at hlookup
            | some fragment =>
                have he : fragment.node = ancestor := by simpa [hl] using hlookup
                subst ancestor
                exact hm _
                  (List.mem_flatMap.mpr
                    ⟨
                      fragment,
                      List.mem_of_find?_eq_some hl,
                      by simp [RefRoles.fragmentRefs]
                    ⟩)
      · exact fun u hu' => hu u (List.mem_cons_of_mem usage hu')

theorem mapRefs_new_bound (deferMap : DeferMap) (usages : List DeferUsage)
    (path : ResponsePath) (bound : Nat)
    (hm : ∀ ref ∈ deferMap.flatMap RefRoles.fragmentRefs, ref < bound)
    (hu : ∀ usage ∈ usages, usage.ref < bound)
    : ∀ ref ∈ (getNewDeferMap usages path deferMap).flatMap RefRoles.fragmentRefs,
        ref < bound :=
  mapRefs_new_property _ deferMap usages path hm hu

theorem mapRefs_new_root (deferMap : DeferMap) (usages : List DeferUsage)
    (path : ResponsePath) (start : Nat) (hu : ∀ usage ∈ usages, start ≤ usage.ref)
    : ∀ ref ∈ (getNewDeferMap usages path deferMap).flatMap RefRoles.fragmentRefs,
        ref ∈ deferMap.flatMap RefRoles.fragmentRefs ∨ start ≤ ref :=
  mapRefs_new_property _ deferMap usages path (fun _ hk => Or.inl hk)
    (fun usage hk => Or.inr (hu usage hk))

theorem mapRefs_filterMap_subset (deferMap : DeferMap) (refs : List Nat)
    : ((refs.filterMap (lookupDeferredFragment? deferMap)).flatMap
        RefRoles.fragmentRefs).Subset
        (deferMap.flatMap RefRoles.fragmentRefs) := by
  intro ref hk
  obtain ⟨fragment, hf, href⟩ := List.mem_flatMap.mp hk
  obtain ⟨_, _, hl⟩ := List.mem_filterMap.mp hf
  exact List.mem_flatMap.mpr ⟨fragment, List.mem_of_find?_eq_some hl, href⟩

end GraphQL.IncrementalDelivery.Semantics.RefRegions
