import Proofs.GraphQL.IncrementalDelivery.Semantics.OwnerMetadata

/-! Coherent full ancestry for fresh defer keys.
The ghost assignment records the transitive ancestor list shared by every occurrence
of a key; local defer maps may omit unrelated allocations but retain every ancestor.
-/

namespace GraphQL.IncrementalDelivery.Semantics.Ancestry

open GraphQL.IncrementalDelivery.Execution

abbrev Assignment := Nat → List Nat

def Extends (bound : Nat) (old next : Assignment) : Prop :=
  ∀ key < bound, next key = old key

def Valid (parents : Assignment) (bound : Nat) : Prop :=
  ∀ key < bound,
  ∀ ancestor ∈ parents key, ancestor < key ∧ (parents ancestor).Subset (parents key)

def mapKeys (deferMap : DeferMap) : List Nat :=
  deferMap.map (fun fragment => fragment.node.key)

def FragmentAt (parents : Assignment) (bound : Nat) (fragment : DeferredFragment)
    : Prop :=
  fragment.node.key < bound
  ∧ fragment.ancestors.map DeliveryNode.key = parents fragment.node.key

def MapAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap) : Prop :=
  ∀ fragment ∈ deferMap,
    FragmentAt parents bound fragment
    ∧ (parents fragment.node.key).Subset (mapKeys deferMap)

def UsageAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (usage : DeferUsage)
    : Prop :=
  usage.key < bound ∧ parents usage.key = usage.ancestors ∧ usage.key ∈ mapKeys deferMap

def OptionalUsageAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (usage : Option DeferUsage)
    : Prop :=
  ∀ actual ∈ usage, UsageAt parents bound deferMap actual

def Descends (parents : Assignment) (owners : List Nat) (key : Nat) : Prop :=
  ∃ owner ∈ owners, owner = key ∨ owner ∈ parents key

def WorkUnder (parents : Assignment) (owners : List Nat) : Work → Prop
  | .empty => True
  | .append left right => WorkUnder parents owners left ∧ WorkUnder parents owners right
  | .deferred groups _ _ children =>
      (∀ group ∈ groups, Descends parents owners group.node.key)
      ∧ WorkUnder parents owners children
  | .stream .. => False

def WorkAt (parents : Assignment) (bound : Nat) : Work → Prop
  | .empty => True
  | .append left right => WorkAt parents bound left ∧ WorkAt parents bound right
  | .deferred groups _ _ children =>
      groups ≠ []
      ∧ (∀ group ∈ groups, FragmentAt parents bound group)
      ∧ WorkUnder parents (mapKeys groups) children
      ∧ WorkAt parents bound children
  | .stream .. => False

theorem Extends.refl (parents : Assignment) (bound : Nat)
    : Extends bound parents parents :=
  fun _ _ => rfl

theorem Extends.trans {first middle last : Assignment} {start finish : Nat}
    (h : Extends start first middle) (hn : Extends finish middle last)
    (hle : start ≤ finish)
    : Extends start first last := by
  intro key hk
  exact (hn key (by omega)).trans (h key hk)

theorem FragmentAt.extend {parents next : Assignment} {start finish : Nat}
    {fragment : DeferredFragment} (h : FragmentAt parents start fragment)
    (he : Extends start parents next) (hle : start ≤ finish)
    : FragmentAt next finish fragment :=
  ⟨Nat.lt_of_lt_of_le h.1 hle, h.2.trans (he fragment.node.key h.1).symm⟩

theorem MapAt.extend {parents next : Assignment} {start finish : Nat}
    {deferMap : DeferMap} (h : MapAt parents start deferMap)
    (he : Extends start parents next) (hle : start ≤ finish)
    : MapAt next finish deferMap := by
  intro fragment hf
  have hh := h fragment hf
  exact ⟨hh.1.extend he hle, by simpa only [he fragment.node.key hh.1.1] using hh.2⟩

theorem UsageAt.extend {parents next : Assignment} {start finish : Nat}
    {deferMap nextMap : DeferMap} {usage : DeferUsage}
    (h : UsageAt parents start deferMap usage) (he : Extends start parents next)
    (hle : start ≤ finish) (hm : (mapKeys deferMap).Subset (mapKeys nextMap))
    : UsageAt next finish nextMap usage :=
  ⟨Nat.lt_of_lt_of_le h.1 hle, (he usage.key h.1).trans h.2.1, hm h.2.2⟩

theorem lookup_key {deferMap : DeferMap} {key : Nat} {fragment : DeferredFragment}
    (h : lookupDeferredFragment? deferMap key = some fragment)
    : fragment.node.key = key := by
  have hf : (fun group : DeferredFragment => group.node.key == key) fragment = true :=
    List.find?_some (p := fun group : DeferredFragment => group.node.key == key) h
  exact beq_iff_eq.mp hf

theorem lookup_exists {deferMap : DeferMap} {key : Nat} (h : key ∈ mapKeys deferMap)
    : ∃ fragment, lookupDeferredFragment? deferMap key = some fragment := by
  obtain ⟨fragment, hf, he⟩ := List.mem_map.mp h
  have hs : (lookupDeferredFragment? deferMap key).isSome = true := by
    apply List.find?_isSome.mpr
    exact ⟨fragment, hf, by simp [he]⟩
  cases he : lookupDeferredFragment? deferMap key with
  | none => simp [he] at hs
  | some fragment => exact ⟨fragment, rfl⟩

theorem usage_ancestors_known {parents : Assignment} {bound : Nat} {deferMap : DeferMap}
    (hm : MapAt parents bound deferMap) {usage : DeferUsage}
    (hu : UsageAt parents bound deferMap usage)
    : usage.ancestors.Subset (mapKeys deferMap) := by
  obtain ⟨fragment, hf⟩ := lookup_exists hu.2.2
  have hh := hm fragment (List.mem_of_find?_eq_some hf)
  simpa only [lookup_key hf, hu.2.1] using hh.2

theorem ancestor_nodes_keys (deferMap : DeferMap) (keys : List Nat)
    (hk : keys.Subset (mapKeys deferMap))
    : (keys.filterMap
        (fun key => (lookupDeferredFragment? deferMap key).map DeferredFragment.node)).map
        DeliveryNode.key
      = keys := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      obtain ⟨fragment, hf⟩ := lookup_exists (hk (by simp : key ∈ key :: rest))
      have hrest : rest.Subset (mapKeys deferMap) := by
        intro next hn
        exact hk (List.mem_cons_of_mem key hn)
      simp [hf, lookup_key hf, ih hrest]

def allocate (parents : Assignment) (state : Nat) (ancestors : List Nat) : Assignment :=
  fun key => if key = state then ancestors else parents key

theorem allocate_extends (parents : Assignment) (state : Nat) (ancestors : List Nat)
    : Extends state parents (allocate parents state ancestors) := by
  intro key hk
  simp [allocate, Nat.ne_of_lt hk]

theorem allocate_valid (parents : Assignment) (state : Nat) (parent : Option DeferUsage)
    (hv : Valid parents state)
    (hu : ∀ usage ∈ parent, usage.key < state ∧ parents usage.key = usage.ancestors)
    : Valid
        (allocate parents state
          ((parent.map (fun usage => usage.key :: usage.ancestors)).getD []))
        (state + 1) := by
  intro key hk ancestor ha
  by_cases he : key = state
  · subst key
    cases parent with
    | none => simp [allocate] at ha
    | some usage =>
        have hh := hu usage rfl
        simp only [allocate, ↓reduceIte, Option.map_some, Option.getD_some, List.mem_cons] at ha
        have hlu : parents usage.key = usage.ancestors := hh.2
        rcases ha with rfl | ha
        · refine ⟨hh.1, ?_⟩
          intro a ham
          simpa [allocate, Nat.ne_of_lt hh.1, hlu] using List.mem_cons_of_mem usage.key ham
        · have han := hv usage.key hh.1 ancestor (hlu ▸ ha)
          refine ⟨Nat.lt_trans han.1 hh.1, ?_⟩
          intro a ham
          have heq : ancestor ≠ state := by omega
          simp only [allocate, heq, ↓reduceIte] at ham
          simp only [allocate, ↓reduceIte, Option.map_some, Option.getD_some]
          exact List.mem_cons_of_mem usage.key (hlu ▸ han.2 ham)
  · have hks : key < state := by omega
    have heq := allocate_extends parents state
      ((parent.map (fun usage => usage.key :: usage.ancestors)).getD []) key hks
    rw [heq] at ha
    have hh := hv key hks ancestor ha
    refine ⟨hh.1, ?_⟩
    intro a ham
    rw [allocate_extends parents state _ ancestor (Nat.lt_trans hh.1 hks)] at ham
    rw [heq]
    exact hh.2 ham

theorem mapAt_allocate (parents : Assignment) (state : Nat) (path : ResponsePath)
    (deferMap : DeferMap) (parent : Option DeferUsage) (label : Option DirectiveLabel)
    (hm : MapAt parents state deferMap)
    (hu : OptionalUsageAt parents state deferMap parent)
    : let ancestors := (parent.map (fun usage => usage.key :: usage.ancestors)).getD []
      let usage : DeferUsage := { key := state, label, ancestors }
      let next := allocate parents state ancestors
      MapAt next (state + 1) (getNewDeferMap [usage] path deferMap)
      ∧ UsageAt next (state + 1) (getNewDeferMap [usage] path deferMap) usage := by
  dsimp only
  let ancestors := (parent.map (fun usage => usage.key :: usage.ancestors)).getD []
  have hanc : ancestors.Subset (mapKeys deferMap) := by
    cases parent with
    | none => intro key hk; simp [ancestors] at hk
    | some usage =>
        have hh := hu usage rfl
        intro key hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hh.2.2
        · exact usage_ancestors_known hm hh hk
  have he := allocate_extends parents state ancestors
  have hme := hm.extend he (Nat.le_succ state)
  let fragment : DeferredFragment := {
    node := { key := state, path, label }
    ancestors := ancestors.filterMap (fun key => (lookupDeferredFragment? deferMap key).map DeferredFragment.node) }
  change MapAt (allocate parents state ancestors) (state + 1) (deferMap ++ [fragment])
    ∧ UsageAt (allocate parents state ancestors) (state + 1) (deferMap ++ [fragment]) _
  constructor
  · intro group hg
    rcases List.mem_append.mp hg with hg | hg
    · have hh := hme group hg
      refine ⟨hh.1, ?_⟩
      intro key hk
      simpa only [mapKeys, List.map_append] using List.mem_append_left
        (mapKeys [fragment]) (hh.2 hk)
    · have hg' := List.mem_singleton.mp hg
      subst group
      refine ⟨⟨Nat.lt_succ_self _, ?_⟩, ?_⟩
      · simpa [fragment, allocate] using ancestor_nodes_keys deferMap ancestors hanc
      · intro key hk
        simp only [fragment, allocate, ↓reduceIte] at hk
        simpa only [mapKeys, List.map_append] using List.mem_append_left
          (mapKeys [fragment]) (hanc hk)
  · refine ⟨Nat.lt_succ_self _, by simp [allocate, ancestors], ?_⟩
    simp [mapKeys, fragment]

theorem getNewDeferMap_append (left right : List DeferUsage) (path : ResponsePath)
    (deferMap : DeferMap)
    : getNewDeferMap (left ++ right) path deferMap
      = getNewDeferMap right path (getNewDeferMap left path deferMap) := by
  exact List.foldl_append

theorem getNewDeferMap_keys (usages : List DeferUsage) (path : ResponsePath)
    (deferMap : DeferMap)
    : mapKeys (getNewDeferMap usages path deferMap)
      = mapKeys deferMap ++ usages.map DeferUsage.key := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => simp
  | cons usage rest ih =>
      rw [List.foldl_cons, ih]
      simp [mapKeys, List.append_assoc]

end GraphQL.IncrementalDelivery.Semantics.Ancestry
