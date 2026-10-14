import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ParentDiscovery

/-! The same immutable forest supplies parent lookup and a decreasing height witness.
Nearest-first contexts determine each immediate edge; discovery receives original field
usages, including those dominated during later filtering. No runtime rank is introduced.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ForestParentSource

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning ParentDiscovery

-----------------------------------------------------------------------------------------
-- Keyed parent observations and original unfiltered field seeds
-----------------------------------------------------------------------------------------

def lookup (forest : Forest) (key : Nat) : Option DeferUsage :=
  ((forest.encode 0 []).find? (fun entry => entry.usage.ref == key)).map Entry.usage

def parents (forest : Forest) : Parents :=
  fun key => (lookup forest key).bind (fun usage => usage.ancestors.head?)

def height (forest : Forest) (key : Nat) : Nat :=
  ((lookup forest key).map (fun usage => usage.ancestors.length)).getD 0

def fieldSeeds (groups : CollectedFieldsMap) : List Nat :=
  groups.flatMap
    (fun group => (group.2.filterMap FieldDetails.deferUsage).map DeferUsage.ref)

def ForestParentConstruction : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → Decreasing (parents forest) (height forest)
      ∧ (∀ entry ∈ forest.encode 0 [],
          parents forest entry.usage.ref = entry.usage.ancestors.head?)
      ∧ ParentClosed (parents forest) forest.keys

def ForestFieldDiscoveryOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups,
        (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let observed := discover (parents forest) (height forest) (fieldSeeds groups)
          observed.finished = true
          ∧ observed.nodes.Nodup
          ∧ ParentClosed (parents forest) observed.nodes
          ∧ observed.nodes.Subset forest.keys
          ∧ (∀ key,
              key ∈ observed.nodes ↔ Reachable (parents forest) (fieldSeeds groups) key)
          ∧ observed.parentReads = observed.nodes.length
          ∧ observed.probes ≤ observed.nodes.length + (fieldSeeds groups).length

-----------------------------------------------------------------------------------------
-- Every nonexternal parent context is the exact context of a node in this forest
-----------------------------------------------------------------------------------------

private theorem parent_context (forest : Forest) (base : Nat) (context : List Nat)
    (entry : Entry) (member : entry ∈ forest.encode base context)
    : entry.usage.ancestors = context
      ∨ ∃ ancestor ∈ forest.encode base context,
          entry.usage.ancestors = ancestor.usage.ref :: ancestor.usage.ancestors := by
  induction forest generalizing base context with
  | empty => simp [Forest.encode] at member
  | node key children siblings childIH siblingIH =>
      simp only [Forest.encode, List.mem_cons, List.mem_append] at member
      rcases member with rfl | child | sibling
      · exact Or.inl rfl
      · rcases childIH _ _ child with external | ⟨ancestor, present, ancestors⟩
        · exact Or.inr ⟨⟨{ ref := key, ancestors := context }, ⟨base, base + 1 + children.keys.length⟩⟩,
            by simp [Forest.encode], external⟩
        · exact Or.inr ⟨ancestor, by simp [Forest.encode, present], ancestors⟩
      · rcases siblingIH _ _ sibling with external | ⟨ancestor, present, ancestors⟩
        · exact Or.inl external
        · exact Or.inr ⟨ancestor, by simp [Forest.encode, present], ancestors⟩

theorem lookup_entry (forest : Forest) (unique : forest.keys.Nodup)
    (entry : Entry) (member : entry ∈ forest.encode 0 [])
    : lookup forest entry.usage.ref = some entry.usage := by
  rw [lookup, find_entry _ (by simpa only [Forest.encode_keys] using unique) entry member]
  rfl

private theorem lookup_some (forest : Forest) (key : Nat) (usage : DeferUsage)
    (found : lookup forest key = some usage)
    : ∃ entry ∈ forest.encode 0 [], entry.usage = usage ∧ entry.usage.ref = key := by
  unfold lookup at found
  cases selected : (forest.encode 0 []).find? (fun entry => entry.usage.ref == key) with
  | none => simp [selected] at found
  | some entry =>
      simp only [selected, Option.map_some, Option.some.injEq] at found
      have matchKey := List.find?_some (p := fun (candidate : Entry) => candidate.usage.ref == key) selected
      exact ⟨
        entry,
        List.mem_of_find?_eq_some selected,
        found,
        by simpa only [beq_iff_eq] using matchKey
      ⟩

theorem ForestParentConstruction_holds : ForestParentConstruction := by
  intro forest unique
  have edgeFor : ∀ entry ∈ forest.encode 0 [], parents forest entry.usage.ref = entry.usage.ancestors.head? := by
    intro entry member
    simp only [parents, lookup_entry forest unique entry member, Option.bind_some]
  have ancestorFor : ∀ entry ∈ forest.encode 0 [], ∀ ancestor,
      parents forest entry.usage.ref = some ancestor → ∃ other ∈ forest.encode 0 [],
        other.usage.ref = ancestor ∧ entry.usage.ancestors = ancestor :: other.usage.ancestors := by
    intro entry member ancestor edge
    rcases parent_context forest 0 [] entry member with empty | ⟨other, present, context⟩
    · rw [edgeFor entry member, empty] at edge
      contradiction
    · rw [edgeFor entry member, context] at edge
      simp only [List.head?_cons, Option.some.injEq] at edge
      exact ⟨other, present, edge, edge ▸ context⟩
  refine ⟨?_, edgeFor, ?_⟩
  · intro key ancestor edge
    cases found : lookup forest key with
    | none => simp [parents, found] at edge
    | some usage =>
        obtain ⟨entry, member, usageEq, keyEq⟩ := lookup_some forest key usage found
        obtain ⟨other, present, ancestorEq, context⟩ := ancestorFor entry member ancestor (keyEq ▸ edge)
        simp only [height, ← keyEq, ← ancestorEq, lookup_entry forest unique entry member,
          lookup_entry forest unique other present, Option.map_some, Option.getD_some, context, List.length_cons]
        omega
  · intro key member ancestor edge
    obtain ⟨entry, present, keyEq⟩ := List.mem_map.mp (forest.encode_keys 0 [] ▸ member)
    obtain ⟨other, otherMember, ancestorEq, _⟩ := ancestorFor entry present ancestor (keyEq ▸ edge)
    rw [← ancestorEq, ← forest.encode_keys 0 []]
    exact List.mem_map.mpr ⟨other, otherMember, rfl⟩

private theorem seeds_subset (forest : Forest) (groups : CollectedFieldsMap)
    (fromForest : ∀ group ∈ groups, FieldsFromForest forest group.2)
    : (fieldSeeds groups).Subset forest.keys := by
  intro key member
  obtain ⟨group, groupMember, selected⟩ := List.mem_flatMap.mp member
  obtain ⟨usage, usageMember, keyEq⟩ := List.mem_map.mp selected
  obtain ⟨entry, entryMember, equal, _⟩ := fromForest group groupMember usage usageMember
  rw [← keyEq, ← equal, ← forest.encode_keys 0 []]
  exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩

theorem ForestFieldDiscoveryOptimization_holds : ForestFieldDiscoveryOptimization := by
  intro forest unique groups fromForest
  obtain ⟨decreasing, _, closed⟩ := ForestParentConstruction_holds forest unique
  obtain ⟨finished, nodesUnique, nodesClosed, domain, reads, probes⟩ :=
    ParentDiscoveryOptimization_holds (parents forest) (height forest) decreasing (fieldSeeds groups)
  refine ⟨finished, nodesUnique, nodesClosed, ?_, domain, reads, probes⟩
  intro key member
  have reached := (domain key).1 member
  clear member
  induction reached with
  | seed node present => exact seeds_subset forest groups fromForest present
  | ancestor node ancestor _ edge covered => exact closed node covered ancestor edge

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ForestParentSource
