import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegionRegistration

/-! Exposed keys identify their stream-item boundary without assuming output admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open Semantics.KeyRegions

-----------------------------------------------------------------------------------------
-- A stream-item boundary exposes its whole defer region, not just one contributor
-----------------------------------------------------------------------------------------

/-- One exposed key in a located root region exposes every key in that same region.
Witness: navigation stays within the root region until an item boundary; generated
separation then forces that particular item's identity into the observed inventory.
No successful object-producer publication is required.
-/
theorem Located.exposedRootKeys {work address current producer owners seen key}
    (located : Located work address current producer owners)
    (separated : WorkSeparated work) (member : key ∈ rootKeys current)
    (exposed : ExposedKey work seen key)
    : ∀ other ∈ rootKeys current, ExposedKey work seen other := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact fun _ included => .inl included
  | left _ ih =>
      exact fun other included =>
        ih (List.mem_append_left _ member) other (List.mem_append_left _ included)
  | right _ ih =>
      exact fun other included =>
        ih (List.mem_append_right _ member) other (List.mem_append_right _ included)
  | executionGroup _ ih =>
      exact fun other included =>
        ih (List.mem_append_right _ member) other (List.mem_append_right _ included)
  | @item address stream items birth enclosing index result children prior entry _ =>
      have region := Located.streamRegion_member prior.toCurrent entry
      have observed : Occurrence.item address index ∈ seen := by
        apply Classical.byContradiction
        intro absent
        exact streamRegion_unexposed separated region absent member exposed
      exact fun other included => .inr ⟨_, observed, rootKeys children, region, included⟩

/-- An exposed key directly below a stream-item producer identifies that observed item.
Witness: invert navigation to the last producer edge and use disjoint key regions.
Combines do not change the producer; an object edge cannot name an item producer.
-/
theorem Located.itemProducer_seen
    {work address current owners source index seen key}
    (located : Located work address current (some (.item source index)) owners)
    (separated : WorkSeparated work) (member : key ∈ rootKeys current)
    (exposed : ExposedKey work seen key)
    : Occurrence.item source index ∈ seen := by
  have descend {address current producer owners}
      (navigation : StructuralEquivalence.Located work address current producer owners)
      (same : producer = some (.item source index)) (member : key ∈ rootKeys current)
      : Occurrence.item source index ∈ seen := by
    induction navigation with
    | root => cases same
    | left _ ih => exact ih same (List.mem_append_left _ member)
    | right _ ih => exact ih same (List.mem_append_right _ member)
    | executionGroup => cases same
    | item prior entry =>
        cases same
        apply Classical.byContradiction
        intro absent
        exact streamRegion_unexposed separated (Located.streamRegion_member prior.toCurrent entry)
          absent member exposed
  exact descend (StructuralEquivalence.located_of_current located) rfl member

-----------------------------------------------------------------------------------------
-- Task and group projections retain this boundary through permanent registration
-----------------------------------------------------------------------------------------

/-- An object task's contributors and full ancestor metadata share its exposed region.
Witness: the task's exact location supplies its contributor in the root-key inventory;
region exposure then applies to every key there, including ancestor-only records.
-/
theorem TaskAt.executionGroup_exposedRootKeys
    {work address owners producer payload seen key}
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (separated : WorkSeparated work) (owner : key ∈ owners)
    (exposed : ExposedKey work seen key)
    : ∀ location,
        locateWork work address = some location
        → ∀ other ∈ rootKeys location.current, ExposedKey work seen other := by
  obtain ⟨groups, locationPath, value, children, enclosing, located, sameOwners, _⟩ := known
  have member : key ∈ rootKeys (.executionGroup groups locationPath value children) := by
    rw [sameOwners] at owner
    obtain ⟨fragment, included, same⟩ := List.mem_map.mp owner
    exact List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨fragment, included, List.mem_cons.mpr (.inl same.symm)⟩)
  intro location found
  have same := Option.some.inj (located.symm.trans found)
  subst location
  exact Located.exposedRootKeys located separated member exposed

/-- Exposure of a group includes its entire defer ancestry in the same region.
Witness: its descriptor's contributor and ancestor keys all occur in one located root
region, including taskless intermediate ancestors.
-/
theorem NodeAt.group_exposedChain {work node dependencies producer seen}
    (known : NodeAt work node .group dependencies producer)
    (separated : WorkSeparated work) (exposed : ExposedKey work seen node.key)
    : ∀ key ∈ node.key :: dependencies, ExposedKey work seen key := by
  obtain ⟨address, groups, path, result, children, enclosing, fragment,
    located, member, sameNode, sameDependencies⟩ := known
  have rootMember : node.key ∈ rootKeys (.executionGroup groups path result children) :=
    List.mem_append_left _ (List.mem_flatMap.mpr
      ⟨fragment, member, List.mem_cons.mpr (.inl (congrArg Execution.DeliveryNode.key sameNode))⟩)
  intro key included
  apply Located.exposedRootKeys located separated rootMember exposed key
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨fragment, member, ?_⟩
  simpa only [sameNode, sameDependencies, Semantics.KeyRoles.fragmentKeys] using included

/-- Exposure of an item-produced group identifies the item that revealed its region.
Witness: project the group's contributor key and invert its exact item-producer edge.
-/
theorem NodeAt.group_itemProducer_seen {work node dependencies source index seen}
    (known : NodeAt work node .group dependencies (some (.item source index)))
    (separated : WorkSeparated work) (exposed : ExposedKey work seen node.key)
    : Occurrence.item source index ∈ seen := by
  obtain ⟨address, groups, path, result, children, enclosing, fragment,
    located, member, sameNode, _⟩ := known
  apply Located.itemProducer_seen located separated (key := node.key) _ exposed
  exact List.mem_append_left _ (List.mem_flatMap.mpr
    ⟨fragment, member, List.mem_cons.mpr (.inl (congrArg Execution.DeliveryNode.key sameNode))⟩)

/-- A registered group with an item producer was introduced by an already-observed item.
Witness: permanent registration exposes its key, and exact structural navigation locates
the unique item boundary. This uses source identities, not a chosen response matching.
-/
theorem State.RegionInventory.group_itemProducer_seen {queue : State} {work seen}
    (inventory : queue.RegionInventory work seen) (generated : ExecutedWork work)
    {node dependencies source index}
    (known : NodeAt work node .group dependencies (some (.item source index)))
    (registered : node.key ∈ queue.registeredGroups)
    : Occurrence.item source index ∈ seen :=
  NodeAt.group_itemProducer_seen known generated.regionsSeparated
    (inventory.registered_exposed registered)

/-- An observed item identity comes from a successful item batch, not an object failure.
Witness: source payload matching excludes item identities in the object-failure case.
-/
theorem ValidGraphEvents.itemIdentity_success {work received source index}
    (valid : ValidGraphEvents work received)
    (observed
      : Occurrence.item source index ∈ received.flatMap (fun event => event.identities.1))
    : Occurrence.item source index ∈ received.flatMap GraphEvent.successes := by
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp observed
  have matching := valid.eachMatches member
  apply List.mem_flatMap.mpr
  refine ⟨event, member, ?_⟩
  cases event with
  | taskSuccess | streamItems => exact included
  | streamSuccess | streamFailure => cases included
  | taskFailure occurrence errors =>
      have same := List.mem_singleton.mp included
      subst occurrence
      obtain ⟨owners, producer, path, task⟩ := matching
      cases StructuralEquivalence.taskAt_of_current task

/-- Valid replay has already received the item producer of every registered group.
Witness: general registration-region coverage, separated item regions, and the source's
fixed payloads. This proves successful settlement, not historical cancellation safety.
-/
theorem ExecutedWork.registered_group_itemProducer_succeeded {work received}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    {node dependencies source index}
    (known : NodeAt work node .group dependencies (some (.item source index)))
    (registered
      : node.key
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).registeredGroups)
    : Occurrence.item source index ∈ received.flatMap GraphEvent.successes :=
  valid.itemIdentity_success
    ((createWorkQueue_replay_regionInventory valid).group_itemProducer_seen generated
      known registered)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
