import Proofs.GraphQL.IncrementalDelivery.Semantics.KeyRoles

/-! A collected defer map inherits only old metadata keys and freshly allocated
usage keys. Ancestor placeholders are looked up in the same growing map, so they
do not introduce keys from a different region. -/

namespace GraphQL.IncrementalDelivery.Semantics.KeyRegions

open GraphQL.IncrementalDelivery.Execution

theorem mapKeys_new_property (property : Nat → Prop) (deferMap : DeferMap)
    (usages : List DeferUsage) (path : ResponsePath)
    (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, property key)
    (hu : ∀ usage ∈ usages, property usage.key)
    : ∀ key ∈ (getNewDeferMap usages path deferMap).flatMap KeyRoles.fragmentKeys,
        property key := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => exact hm
  | cons usage rest ih =>
      apply ih
      · intro key hk
        simp only [List.flatMap_append, List.mem_append] at hk
        rcases hk with hk | hk
        · exact hm key hk
        · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
            KeyRoles.fragmentKeys, List.mem_cons] at hk
          rcases hk with rfl | hk
          · exact hu usage (by simp)
          · obtain ⟨ancestor, ha, rfl⟩ := List.mem_map.mp hk
            obtain ⟨oldKey, _, hlookup⟩ := List.mem_filterMap.mp ha
            cases hl : lookupDeferredFragment? deferMap oldKey with
            | none => simp [hl] at hlookup
            | some fragment =>
                have he : fragment.node = ancestor := by simpa [hl] using hlookup
                subst ancestor
                exact hm _
                  (List.mem_flatMap.mpr
                    ⟨
                      fragment,
                      List.mem_of_find?_eq_some hl,
                      by simp [KeyRoles.fragmentKeys]
                    ⟩)
      · exact fun u hu' => hu u (List.mem_cons_of_mem usage hu')

theorem mapKeys_new_bound (deferMap : DeferMap) (usages : List DeferUsage)
    (path : ResponsePath) (bound : Nat)
    (hm : ∀ key ∈ deferMap.flatMap KeyRoles.fragmentKeys, key < bound)
    (hu : ∀ usage ∈ usages, usage.key < bound)
    : ∀ key ∈ (getNewDeferMap usages path deferMap).flatMap KeyRoles.fragmentKeys,
        key < bound :=
  mapKeys_new_property _ deferMap usages path hm hu

theorem mapKeys_new_root (deferMap : DeferMap) (usages : List DeferUsage)
    (path : ResponsePath) (start : Nat) (hu : ∀ usage ∈ usages, start ≤ usage.key)
    : ∀ key ∈ (getNewDeferMap usages path deferMap).flatMap KeyRoles.fragmentKeys,
        key ∈ deferMap.flatMap KeyRoles.fragmentKeys ∨ start ≤ key :=
  mapKeys_new_property _ deferMap usages path (fun _ hk => Or.inl hk)
    (fun usage hk => Or.inr (hu usage hk))

theorem mapKeys_filterMap_subset (deferMap : DeferMap) (keys : List Nat)
    : ((keys.filterMap (lookupDeferredFragment? deferMap)).flatMap
        KeyRoles.fragmentKeys).Subset
        (deferMap.flatMap KeyRoles.fragmentKeys) := by
  intro key hk
  obtain ⟨fragment, hf, hkey⟩ := List.mem_flatMap.mp hk
  obtain ⟨_, _, hl⟩ := List.mem_filterMap.mp hf
  exact List.mem_flatMap.mpr ⟨fragment, List.mem_of_find?_eq_some hl, hkey⟩

end GraphQL.IncrementalDelivery.Semantics.KeyRegions
