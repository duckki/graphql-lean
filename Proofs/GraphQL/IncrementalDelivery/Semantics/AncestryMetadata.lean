import Proofs.GraphQL.IncrementalDelivery.Semantics.OwnerMetadata

/-! Coherent full ancestry for fresh defer refs.
The ghost assignment records the transitive ancestor list shared by every occurrence
of a ref; local defer maps may omit unrelated allocations but retain every ancestor.
-/

namespace GraphQL.IncrementalDelivery.Semantics.Ancestry

open GraphQL.IncrementalDelivery.Execution

abbrev Assignment := Nat → List Nat

def Extends (bound : Nat) (old next : Assignment) : Prop :=
  ∀ ref < bound, next ref = old ref

def Valid (parents : Assignment) (bound : Nat) : Prop :=
  ∀ ref < bound,
  ∀ ancestor ∈ parents ref, ancestor < ref ∧ (parents ancestor).Subset (parents ref)

def mapRefs (deferMap : DeferMap) : List Nat :=
  deferMap.map (fun fragment => fragment.node.ref)

def FragmentAt (parents : Assignment) (bound : Nat) (fragment : DeferredFragment)
    : Prop :=
  fragment.node.ref < bound
  ∧ fragment.ancestors.map DeliveryNode.ref = parents fragment.node.ref

def MapAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap) : Prop :=
  ∀ fragment ∈ deferMap,
    FragmentAt parents bound fragment
    ∧ (parents fragment.node.ref).Subset (mapRefs deferMap)

def UsageAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (usage : DeferUsage)
    : Prop :=
  usage.ref < bound ∧ parents usage.ref = usage.ancestors ∧ usage.ref ∈ mapRefs deferMap

def OptionalUsageAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (usage : Option DeferUsage)
    : Prop :=
  ∀ actual ∈ usage, UsageAt parents bound deferMap actual

def Descends (parents : Assignment) (owners : List Nat) (ref : NodeRef) : Prop :=
  ∃ owner ∈ owners, owner = ref ∨ owner ∈ parents ref

def WorkUnder (parents : Assignment) (owners : List Nat) : Work → Prop
  | .empty => True
  | .combine left right => WorkUnder parents owners left ∧ WorkUnder parents owners right
  | .executionGroup groups _ _ children =>
      (∀ group ∈ groups, Descends parents owners group.node.ref)
      ∧ WorkUnder parents owners children
  | .stream .. => False

def WorkAt (parents : Assignment) (bound : Nat) : Work → Prop
  | .empty => True
  | .combine left right => WorkAt parents bound left ∧ WorkAt parents bound right
  | .executionGroup groups _ _ children =>
      groups ≠ []
      ∧ (∀ group ∈ groups, FragmentAt parents bound group)
      ∧ WorkUnder parents (mapRefs groups) children
      ∧ WorkAt parents bound children
  | .stream .. => False

theorem Extends.refl (parents : Assignment) (bound : Nat)
    : Extends bound parents parents :=
  fun _ _ => rfl

theorem Extends.trans {first middle last : Assignment} {start finish : Nat}
    (h : Extends start first middle) (hn : Extends finish middle last)
    (hle : start ≤ finish)
    : Extends start first last := by
  intro ref hk
  exact (hn ref (by omega)).trans (h ref hk)

theorem FragmentAt.extend {parents next : Assignment} {start finish : Nat}
    {fragment : DeferredFragment} (h : FragmentAt parents start fragment)
    (he : Extends start parents next) (hle : start ≤ finish)
    : FragmentAt next finish fragment :=
  ⟨Nat.lt_of_lt_of_le h.1 hle, h.2.trans (he fragment.node.ref h.1).symm⟩

theorem MapAt.extend {parents next : Assignment} {start finish : Nat}
    {deferMap : DeferMap} (h : MapAt parents start deferMap)
    (he : Extends start parents next) (hle : start ≤ finish)
    : MapAt next finish deferMap := by
  intro fragment hf
  have hh := h fragment hf
  exact ⟨hh.1.extend he hle, by simpa only [he fragment.node.ref hh.1.1] using hh.2⟩

theorem UsageAt.extend {parents next : Assignment} {start finish : Nat}
    {deferMap nextMap : DeferMap} {usage : DeferUsage}
    (h : UsageAt parents start deferMap usage) (he : Extends start parents next)
    (hle : start ≤ finish) (hm : (mapRefs deferMap).Subset (mapRefs nextMap))
    : UsageAt next finish nextMap usage :=
  ⟨Nat.lt_of_lt_of_le h.1 hle, (he usage.ref h.1).trans h.2.1, hm h.2.2⟩

theorem lookup_ref {deferMap : DeferMap} {ref : NodeRef} {fragment : DeferredFragment}
    (h : lookupDeferredFragment? deferMap ref = some fragment)
    : fragment.node.ref = ref := by
  have hf : (fun group : DeferredFragment => group.node.ref == ref) fragment = true :=
    List.find?_some (p := fun group : DeferredFragment => group.node.ref == ref) h
  exact beq_iff_eq.mp hf

theorem lookup_exists {deferMap : DeferMap} {ref : NodeRef} (h : ref ∈ mapRefs deferMap)
    : ∃ fragment, lookupDeferredFragment? deferMap ref = some fragment := by
  obtain ⟨fragment, hf, he⟩ := List.mem_map.mp h
  have hs : (lookupDeferredFragment? deferMap ref).isSome = true := by
    apply List.find?_isSome.mpr
    exact ⟨fragment, hf, by simp [he]⟩
  cases he : lookupDeferredFragment? deferMap ref with
  | none => simp [he] at hs
  | some fragment => exact ⟨fragment, rfl⟩

theorem usage_ancestors_known {parents : Assignment} {bound : Nat} {deferMap : DeferMap}
    (hm : MapAt parents bound deferMap) {usage : DeferUsage}
    (hu : UsageAt parents bound deferMap usage)
    : usage.ancestors.Subset (mapRefs deferMap) := by
  obtain ⟨fragment, hf⟩ := lookup_exists hu.2.2
  have hh := hm fragment (List.mem_of_find?_eq_some hf)
  simpa only [lookup_ref hf, hu.2.1] using hh.2

theorem ancestor_nodes_refs (deferMap : DeferMap) (refs : List Nat)
    (hk : refs.Subset (mapRefs deferMap))
    : (refs.filterMap
        (fun ref => (lookupDeferredFragment? deferMap ref).map DeferredFragment.node)).map
        DeliveryNode.ref
      = refs := by
  induction refs with
  | nil => rfl
  | cons ref rest ih =>
      obtain ⟨fragment, hf⟩ := lookup_exists (hk (by simp : ref ∈ ref :: rest))
      have hrest : rest.Subset (mapRefs deferMap) := by
        intro next hn
        exact hk (List.mem_cons_of_mem ref hn)
      simp [hf, lookup_ref hf, ih hrest]

def allocate (parents : Assignment) (state : Nat) (ancestors : List Nat) : Assignment :=
  fun ref => if ref = state then ancestors else parents ref

theorem allocate_extends (parents : Assignment) (state : Nat) (ancestors : List Nat)
    : Extends state parents (allocate parents state ancestors) := by
  intro ref hk
  simp [allocate, Nat.ne_of_lt hk]

theorem allocate_valid (parents : Assignment) (state : Nat) (parent : Option DeferUsage)
    (hv : Valid parents state)
    (hu : ∀ usage ∈ parent, usage.ref < state ∧ parents usage.ref = usage.ancestors)
    : Valid
        (allocate parents state
          ((parent.map (fun usage => usage.ref :: usage.ancestors)).getD []))
        (state + 1) := by
  intro ref hk ancestor ha
  by_cases he : ref = state
  · subst ref
    cases parent with
    | none => simp [allocate] at ha
    | some usage =>
        have hh := hu usage rfl
        simp only [allocate, ↓reduceIte, Option.map_some, Option.getD_some, List.mem_cons] at ha
        have hlu : parents usage.ref = usage.ancestors := hh.2
        rcases ha with rfl | ha
        · refine ⟨hh.1, ?_⟩
          intro a ham
          simpa [allocate, Nat.ne_of_lt hh.1, hlu] using List.mem_cons_of_mem usage.ref ham
        · have han := hv usage.ref hh.1 ancestor (hlu ▸ ha)
          refine ⟨Nat.lt_trans han.1 hh.1, ?_⟩
          intro a ham
          have heq : ancestor ≠ state := Nat.ne_of_lt (Nat.lt_trans han.1 hh.1)
          simp only [allocate, heq, ↓reduceIte] at ham
          simp only [allocate, ↓reduceIte, Option.map_some, Option.getD_some]
          exact List.mem_cons_of_mem usage.ref (hlu ▸ han.2 ham)
  · have hks : ref < state := by omega
    have heq := allocate_extends parents state
      ((parent.map (fun usage => usage.ref :: usage.ancestors)).getD []) ref hks
    rw [heq] at ha
    have hh := hv ref hks ancestor ha
    refine ⟨hh.1, ?_⟩
    intro a ham
    rw [allocate_extends parents state _ ancestor (Nat.lt_trans hh.1 hks)] at ham
    rw [heq]
    exact hh.2 ham

theorem mapAt_allocate (parents : Assignment) (state : Nat) (path : ResponsePath)
    (deferMap : DeferMap) (parent : Option DeferUsage) (label : Option DirectiveLabel)
    (hm : MapAt parents state deferMap)
    (hu : OptionalUsageAt parents state deferMap parent)
    : let ancestors := (parent.map (fun usage => usage.ref :: usage.ancestors)).getD []
      let usage : DeferUsage := { ref := state, label, ancestors }
      let next := allocate parents state ancestors
      MapAt next (state + 1) (getNewDeferMap [usage] path deferMap)
      ∧ UsageAt next (state + 1) (getNewDeferMap [usage] path deferMap) usage := by
  dsimp only
  let ancestors := (parent.map (fun usage => usage.ref :: usage.ancestors)).getD []
  have hanc : ancestors.Subset (mapRefs deferMap) := by
    cases parent with
    | none => intro ref hk; simp [ancestors] at hk
    | some usage =>
        have hh := hu usage rfl
        intro ref hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hh.2.2
        · exact usage_ancestors_known hm hh hk
  have he := allocate_extends parents state ancestors
  have hme := hm.extend he (Nat.le_succ state)
  let fragment : DeferredFragment := {
    node := { ref := state, path, label }
    ancestors := ancestors.filterMap (fun ref => (lookupDeferredFragment? deferMap ref).map DeferredFragment.node) }
  change MapAt (allocate parents state ancestors) (state + 1) (deferMap ++ [fragment])
    ∧ UsageAt (allocate parents state ancestors) (state + 1) (deferMap ++ [fragment]) _
  constructor
  · intro group hg
    rcases List.mem_append.mp hg with hg | hg
    · have hh := hme group hg
      refine ⟨hh.1, ?_⟩
      intro ref hk
      simpa only [mapRefs, List.map_append] using List.mem_append_left
        (mapRefs [fragment]) (hh.2 hk)
    · have hg' := List.mem_singleton.mp hg
      subst group
      refine ⟨⟨Nat.lt_succ_self _, ?_⟩, ?_⟩
      · simpa [fragment, allocate] using ancestor_nodes_refs deferMap ancestors hanc
      · intro ref hk
        simp only [fragment, allocate, ↓reduceIte] at hk
        simpa only [mapRefs, List.map_append] using List.mem_append_left
          (mapRefs [fragment]) (hanc hk)
  · refine ⟨Nat.lt_succ_self _, by simp [allocate, ancestors], ?_⟩
    simp [mapRefs, fragment]

theorem getNewDeferMap_append (left right : List DeferUsage) (path : ResponsePath)
    (deferMap : DeferMap)
    : getNewDeferMap (left ++ right) path deferMap
      = getNewDeferMap right path (getNewDeferMap left path deferMap) := by
  exact List.foldl_append

theorem getNewDeferMap_refs (usages : List DeferUsage) (path : ResponsePath)
    (deferMap : DeferMap)
    : mapRefs (getNewDeferMap usages path deferMap)
      = mapRefs deferMap ++ usages.map DeferUsage.ref := by
  unfold getNewDeferMap
  induction usages generalizing deferMap with
  | nil => simp
  | cons usage rest ih =>
      rw [List.foldl_cons, ih]
      simp [mapRefs, List.append_assoc]

end GraphQL.IncrementalDelivery.Semantics.Ancestry
