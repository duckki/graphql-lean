import Proofs.GraphQL.IncrementalDelivery.Semantics.AncestryContext
import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedNonempty
import Proofs.GraphQL.IncrementalDelivery.Semantics.DeferKeys

/-! Filtering overlapping defer usages retains an ancestor supporting every field.
Execution partitions therefore have nonempty, known owner keys, and every field
and future nested contribution remains below one of the partition's owners.
-/

namespace GraphQL.IncrementalDelivery.Semantics.Ancestry

open GraphQL.IncrementalDelivery.Execution

theorem filtered_key_source (fields : List ExecutableField) (key : Nat)
    (h : key ∈ getFilteredDeferUsageSet fields)
    : ∃ field ∈ fields, ∃ usage, field.deferUsage = some usage ∧ usage.key = key := by
  unfold getFilteredDeferUsageSet at h
  split at h
  · simp at h
  · have hk := (List.mem_filter.mp h).1
    simp only [List.mem_eraseDups, List.mem_map] at hk
    obtain ⟨usage, hu, he⟩ := hk
    obtain ⟨field, hf, hfu⟩ := List.mem_filterMap.mp hu
    exact ⟨field, hf, usage, hfu, he⟩

theorem filtered_usage_ancestor (parents : Assignment) (bound : Nat)
    (usages : List DeferUsage) (hv : Valid parents bound)
    (hu : ∀ usage ∈ usages, usage.key < bound ∧ parents usage.key = usage.ancestors)
    (key : Nat) (hk : key ∈ (usages.map DeferUsage.key).eraseDups)
    : ∃ owner ∈
        (usages.map DeferUsage.key).eraseDups.filter
          (fun key =>
            !(usages.any
                (fun usage =>
                  usage.key == key
                  && usage.ancestors.any
                      (usages.map DeferUsage.key).eraseDups.contains))),
        owner = key ∨ owner ∈ parents key := by
  induction key using Nat.strongRecOn with
  | ind key ih =>
      by_cases hremove : usages.any (fun usage => usage.key == key
          && usage.ancestors.any (usages.map DeferUsage.key).eraseDups.contains) = true
      · obtain ⟨usage, husage, hbad⟩ := List.any_eq_true.mp hremove
        simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
          List.contains_iff_mem] at hbad
        obtain ⟨hkey, ancestor, ha, hanc⟩ := hbad
        have hvalid := hu usage husage
        have hpa : ancestor ∈ parents key := by simpa only [← hkey, hvalid.2] using ha
        have hlt := hv key (by simpa only [hkey] using hvalid.1) ancestor hpa
        obtain ⟨owner, ho, he⟩ := ih ancestor hlt.1 hanc
        refine ⟨owner, ho, Or.inr ?_⟩
        rcases he with rfl | he
        · exact hpa
        · exact hlt.2 he
      · exact ⟨key, List.mem_filter.mpr ⟨hk, by simpa using hremove⟩, Or.inl rfl⟩

theorem fieldsUnder_filtered (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (fields : List ExecutableField) (hv : Valid parents bound)
    (known : ∀ field ∈ fields, OptionalUsageAt parents bound deferMap field.deferUsage)
    : FieldsUnder (getFilteredDeferUsageSet fields) fields := by
  by_cases himmediate : fields.any (fun field => field.deferUsage.isNone) = true
  · intro field hf
    exact Or.inl (by simp [getFilteredDeferUsageSet, himmediate])
  · intro field hf
    cases husage : field.deferUsage with
    | none =>
        have ht : fields.any (fun field => field.deferUsage.isNone) = true :=
          List.any_eq_true.mpr ⟨field, hf, by simp [husage]⟩
        exact False.elim (himmediate ht)
    | some usage =>
        have hu := known field hf usage husage
        obtain ⟨owner, ho, hh⟩ := filtered_usage_ancestor parents bound
          (fields.filterMap ExecutableField.deferUsage) hv
          (by
            intro actual ha
            obtain ⟨f, hfm, hfu⟩ := List.mem_filterMap.mp ha
            exact ⟨(known f hfm actual hfu).1, (known f hfm actual hfu).2.1⟩)
          usage.key (by
            simp only [List.mem_eraseDups, List.mem_map]
            exact ⟨usage, List.mem_filterMap.mpr ⟨field, hf, husage⟩, rfl⟩)
        refine Or.inr ⟨usage, rfl, owner, ?_, ?_⟩
        · simpa [getFilteredDeferUsageSet, himmediate] using ho
        · simpa only [hu.2.1] using hh

theorem filtered_keys_known (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (fields : List ExecutableField)
    (known : ∀ field ∈ fields, OptionalUsageAt parents bound deferMap field.deferUsage)
    : (getFilteredDeferUsageSet fields).Subset (mapKeys deferMap) := by
  intro key hk
  obtain ⟨field, hf, usage, hfu, he⟩ := filtered_key_source fields key hk
  simpa only [he] using (known field hf usage hfu).2.2

theorem filtered_keys_under (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (owners : List Nat) (fields : List ExecutableField)
    (known : ∀ field ∈ fields, OptionalUsageAt parents bound deferMap field.deferUsage)
    (under : FieldsUnder owners fields)
    : owners = []
      ∨ ∀ key ∈ getFilteredDeferUsageSet fields, Descends parents owners key := by
  by_cases hempty : owners = []
  · exact Or.inl hempty
  · refine Or.inr ?_
    intro key hk
    obtain ⟨field, hf, usage, hfu, he⟩ := filtered_key_source fields key hk
    obtain ⟨actual, ha, owner, ho, hu⟩ := (under field hf).resolve_left hempty
    have heq : actual = usage := Option.some.inj (ha.symm.trans hfu)
    subst actual
    have hparents := (known field hf usage hfu).2.1
    exact ⟨owner, ho, by simpa only [← he, hparents] using hu⟩

theorem filtered_keys_nonempty (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (owners : List Nat) (fields : List ExecutableField) (hv : Valid parents bound)
    (known : ∀ field ∈ fields, OptionalUsageAt parents bound deferMap field.deferUsage)
    (under : FieldsUnder owners fields) (hne : fields ≠ [])
    (hdifferent
      : deferUsageSetsEquivalent (getFilteredDeferUsageSet fields) owners = false)
    : getFilteredDeferUsageSet fields ≠ [] := by
  by_cases ho : owners = []
  · intro he
    simp [he, ho, deferUsageSetsEquivalent] at hdifferent
  · apply filteredDeferUsageSet_nonempty fields hne
    · apply List.any_eq_false.mpr
      intro field hf hi
      obtain ⟨usage, hu, _⟩ := (under field hf).resolve_left ho
      simp [hu] at hi
    · intro field hf usage hu
      have hk := known field hf usage hu
      intro ancestor ha
      exact (hv usage.key hk.1 ancestor (hk.2.1 ▸ ha)).1

theorem equivalent_subsets (left right : List Nat)
    (h : deferUsageSetsEquivalent left right = true)
    : left.Subset right ∧ right.Subset left := by
  simpa only [deferUsageSetsEquivalent, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem, List.Subset]
    using h

theorem OptionalUnder.mono {owners more : List Nat} {usage : Option DeferUsage}
    (h : OptionalUnder owners usage) (hn : owners ≠ []) (hs : owners.Subset more)
    : OptionalUnder more usage := by
  obtain ⟨actual, ha, owner, ho, hu⟩ := h.resolve_left hn
  exact Or.inr ⟨actual, ha, owner, hs ho, hu⟩

theorem partitionsAt_add (parents : Assignment) (deferMap : DeferMap)
    (owners keys : List Nat) (group : Name × List ExecutableField)
    (partitions : List (List Nat × CollectedFieldsMap)) (hk : keys ≠ [])
    (hknown : keys.Subset (mapKeys deferMap)) (hunder : FieldsUnder keys group.2)
    (houter : owners = [] ∨ ∀ key ∈ keys, Descends parents owners key)
    (h : PartitionsAt parents deferMap owners partitions)
    : PartitionsAt parents deferMap owners
        (addExecutionPartition keys group partitions) := by
  induction partitions with
  | nil =>
      intro partition hp
      have he : partition = (keys, [group]) := by simpa only [addExecutionPartition, List.mem_singleton] using hp
      subst partition
      exact ⟨
        hk,
        hknown,
        by
          intro g hg f hf
          obtain rfl := List.mem_singleton.mp hg
          exact hunder f hf,
        houter
      ⟩
  | cons head rest ih =>
      rcases head with ⟨old, groups⟩
      have hh := h (old, groups) (by simp)
      have ht : PartitionsAt parents deferMap owners rest :=
        fun part hp => h part (List.mem_cons_of_mem _ hp)
      simp only [addExecutionPartition]
      split
      · rename_i he
        intro partition hp
        rcases List.mem_cons.mp hp with rfl | hp
        · refine ⟨hh.1, hh.2.1, ?_, hh.2.2.2⟩
          intro g hg field hf
          rcases List.mem_append.mp hg with hg | hg
          · exact hh.2.2.1 g hg field hf
          · obtain rfl := List.mem_singleton.mp hg
            exact (hunder field hf).mono hk (equivalent_subsets old keys he).2
        · exact ht partition hp
      · intro partition hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hh
        · exact ih ht partition hp

theorem buildExecutionPlan_partitionsAt (parents : Assignment) (bound : Nat)
    (deferMap : DeferMap) (owners : List Nat) (groups : CollectedFieldsMap)
    (hv : Valid parents bound) (_hm : MapAt parents bound deferMap)
    (known
      : GroupsSatisfy
          (fun field => OptionalUsageAt parents bound deferMap field.deferUsage) groups)
    (nonempty : GroupsNonempty groups) (under : GroupsUnder owners groups)
    : PartitionsAt parents deferMap owners
        (buildExecutionPlan groups owners).newCollectedFieldsMaps := by
  have aux (initial : ExecutionPlan)
      (hp : PartitionsAt parents deferMap owners initial.newCollectedFieldsMaps)
      : PartitionsAt parents deferMap owners
          (groups.foldl (fun plan group =>
            if deferUsageSetsEquivalent (getFilteredDeferUsageSet group.2) owners then
              { plan with collectedFieldsMap := plan.collectedFieldsMap ++ [group] }
            else { plan with newCollectedFieldsMaps :=
              addExecutionPartition (getFilteredDeferUsageSet group.2) group plan.newCollectedFieldsMaps })
            initial).newCollectedFieldsMaps := by
    induction groups generalizing initial with
    | nil => exact hp
    | cons group rest ih =>
        have hknown := known group (by simp)
        have hnonempty := nonempty group (by simp)
        have hunder := under group (by simp)
        have hkt : GroupsSatisfy (fun field => OptionalUsageAt parents bound deferMap field.deferUsage) rest :=
          fun g hg => known g (List.mem_cons_of_mem group hg)
        have hnt : GroupsNonempty rest := fun g hg => nonempty g (List.mem_cons_of_mem group hg)
        have hut : GroupsUnder owners rest := fun g hg => under g (List.mem_cons_of_mem group hg)
        rw [List.foldl_cons]
        apply ih hkt hnt hut
        split
        · exact hp
        · rename_i hdifferent
          exact partitionsAt_add parents deferMap owners _ group _
            (filtered_keys_nonempty parents bound deferMap owners group.2 hv hknown hunder hnonempty
              (by simpa using hdifferent))
            (filtered_keys_known parents bound deferMap group.2 hknown)
            (fieldsUnder_filtered parents bound deferMap group.2 hv hknown)
            (filtered_keys_under parents bound deferMap owners group.2 hknown hunder) hp
  exact aux {} (by intro partition hp; simp at hp)

end GraphQL.IncrementalDelivery.Semantics.Ancestry
