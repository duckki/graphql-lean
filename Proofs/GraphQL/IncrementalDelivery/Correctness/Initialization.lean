import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.SpecificationSource
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.FailureCauses
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedDeferContinuity
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedStreamOwnerKeys

/-! Nonvacuous initialization for execution-generated work, independent of a schedule.
This execution-specific bridge is outside the raw work-history proof surface.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution
open Semantics Semantics.Ancestry Semantics.GeneralScheduling

-----------------------------------------------------------------------------------------
-- The first work boundary
-----------------------------------------------------------------------------------------

/-- Descriptors at the first work boundaries, before any task has published. The list is
a proof projection of existing work, not an implementation queue or selected schedule.
-/
def initialCandidates : Work → List (DeliveryNode × NodeKind × Keys)
  | .empty => []
  | .combine left right => initialCandidates left ++ initialCandidates right
  | .executionGroup groups .. =>
      groups.map
        (fun group =>
          (group.node, .group, group.ancestors.map DeliveryNode.key))
  | .stream node _ => [(node, .stream, [])]

/-- Nonempty well-formed work has a first descriptor; witness: combine descent and the
existing nonempty-owner certificate at deferred boundaries.
-/
theorem initialCandidates_nonempty {parents lower bound work}
    (coherent : MixedKeys.WorkAt parents lower bound work) (nonempty : work.size ≠ 0)
    : initialCandidates work ≠ [] := by
  cases work with
  | empty => exact False.elim (nonempty rfl)
  | combine left right =>
      rw [MixedKeys.WorkAt] at coherent
      intro empty
      obtain ⟨hl, hr⟩ := List.append_eq_nil_iff.mp empty
      by_cases leftEmpty : left.size = 0
      · have rightNonempty : right.size ≠ 0 := by
          simpa only [Work.size, leftEmpty, Nat.zero_add] using nonempty
        exact initialCandidates_nonempty coherent.2 rightNonempty hr
      · exact initialCandidates_nonempty coherent.1 leftEmpty hl
  | executionGroup groups path result children =>
      rw [MixedKeys.WorkAt] at coherent
      intro empty
      exact coherent.1 (List.map_eq_nil_iff.mp empty)
  | stream node items => simp [initialCandidates]
termination_by sizeOf work

/-- First-boundary stream descriptors have no enclosing owners; witness: append descent
to the root-context stream constructor.
-/
theorem initialCandidates_stream_dependencies {work node parents}
    (member : (node, .stream, parents) ∈ initialCandidates work)
    : parents = [] := by
  cases work with
  | empty => simp [initialCandidates] at member
  | combine left right =>
      rcases List.mem_append.mp member with member | member
      · exact initialCandidates_stream_dependencies member
      · exact initialCandidates_stream_dependencies member
  | executionGroup groups path result children =>
      obtain ⟨group, _, impossible⟩ := List.mem_map.mp member
      cases impossible
  | stream other items =>
      have same := List.mem_singleton.mp member
      cases same
      rfl
termination_by sizeOf work

/-- A first-boundary descriptor has no producer or enclosing owner. Witness: navigation
through combine nodes only, stopping at the first deferred or streamed work.
-/
theorem initialCandidates_known {root address work node kind parents}
    (located : Located root address work none [])
    (member : (node, kind, parents) ∈ initialCandidates work)
    : NodeAt root node kind parents none := by
  cases work with
  | empty => simp [initialCandidates] at member
  | combine left right =>
      rcases List.mem_append.mp member with member | member
      · exact initialCandidates_known (.left located) member
      · exact initialCandidates_known (.right located) member
  | executionGroup groups path result children =>
      obtain ⟨group, inGroups, equal⟩ := List.mem_map.mp member
      cases equal
      exact .group located inGroups
  | stream node items =>
      have equal := List.mem_singleton.mp member
      cases equal
      exact .stream located
termination_by sizeOf work

-----------------------------------------------------------------------------------------
-- No hidden work precedes the least first-boundary key
-----------------------------------------------------------------------------------------

/-- Descendant keys are at least their supporting owner's key; witness: strict ancestry
ordering, or reuse of that very owner.
-/
theorem descends_lower {parents bound owners key lower}
    (valid : Valid parents bound) (keyBound : key < bound)
    (supported : Descends parents owners key)
    (bounded : ∀ owner ∈ owners, lower ≤ owner)
    : lower ≤ key := by
  obtain ⟨owner, member, same | ancestor⟩ := supported
  · simpa only [← same] using bounded owner member
  · exact Nat.le_trans (bounded owner member) (Nat.le_of_lt (valid key keyBound owner ancestor).1)

/-- A deferred region cannot hide a smaller key than all its enclosing owners. Witness:
defer continuity, stream-owner ordering, and fresh streamed-item key ranges.
-/
theorem scoped_lower {parents bound owners work lower}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (under : DeferUnder parents owners work) (streams : OwnersBefore owners work)
    (nonempty : owners ≠ []) (bounded : ∀ owner ∈ owners, lower ≤ owner)
    : MixedKeys.WorkAt parents lower bound work := by
  cases work <;> simp only [MixedKeys.WorkAt, DeferContinuous, StreamOwnersOrdered,
    DeferUnder, OwnersBefore] at coherent continuous ordered under streams ⊢
  case combine left right =>
    exact ⟨scoped_lower valid coherent.1 continuous.1 ordered.1 under.1 streams.1
        nonempty bounded,
      scoped_lower valid coherent.2 continuous.2 ordered.2 under.2 streams.2
        nonempty bounded⟩
  case executionGroup groups path result children =>
    have groupBounds : ∀ group ∈ groups, lower ≤ group.node.key := by
      intro group member
      exact descends_lower valid (coherent.2.1 group member).2.1
        (under.1 group member) bounded
    refine ⟨coherent.1, fun group member =>
      ⟨groupBounds group member, (coherent.2.1 group member).2⟩, ?_⟩
    apply scoped_lower valid coherent.2.2 continuous.2 ordered.2 continuous.1 ordered.1
    · intro empty
      exact coherent.1 (List.map_eq_nil_iff.mp empty)
    · intro key member
      obtain ⟨group, inGroups, rfl⟩ := List.mem_map.mp member
      exact groupBounds group inGroups
  case stream node items =>
    obtain ⟨owner, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨Nat.le_trans (bounded owner member) (Nat.le_of_lt (streams owner member)),
      coherent.2⟩
termination_by sizeOf work

/-- Bounding the first-boundary keys bounds all work keys. Witness: the scoped lower-bound
lemma at deferred boundaries; streamed descendants already have stricter fresh bounds.
-/
theorem initialCandidates_lower {parents bound work lower}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (bounded : ∀ entry ∈ initialCandidates work, lower ≤ entry.1.key)
    : MixedKeys.WorkAt parents lower bound work := by
  cases work <;> simp only [MixedKeys.WorkAt, DeferContinuous, StreamOwnersOrdered]
    at coherent continuous ordered ⊢
  case combine left right =>
    exact ⟨initialCandidates_lower valid coherent.1 continuous.1 ordered.1
        (fun entry member => bounded entry (List.mem_append_left _ member)),
      initialCandidates_lower valid coherent.2 continuous.2 ordered.2
        (fun entry member => bounded entry (List.mem_append_right _ member))⟩
  case executionGroup groups path result children =>
    have groupBounds : ∀ group ∈ groups, lower ≤ group.node.key := by
      intro group member
      exact bounded _ (List.mem_map.mpr ⟨group, member, rfl⟩)
    refine ⟨coherent.1, fun group member =>
      ⟨groupBounds group member, (coherent.2.1 group member).2⟩, ?_⟩
    apply scoped_lower valid coherent.2.2 continuous.2 ordered.2 continuous.1 ordered.1
    · intro empty
      exact coherent.1 (List.map_eq_nil_iff.mp empty)
    · intro key member
      obtain ⟨group, inGroups, rfl⟩ := List.mem_map.mp member
      exact groupBounds group inGroups
  case stream node items =>
    exact ⟨bounded (node, .stream, []) (by simp [initialCandidates]), coherent.2⟩
termination_by sizeOf work

/-- Global key bounds survive structural lookup, including the stricter key ranges
below stream items. Witness: induction on the existing navigation evidence.
-/
theorem coherent_located {parents lower bound work address current producer owners}
    (coherent : MixedKeys.WorkAt parents lower bound work)
    (located : Located work address current producer owners)
    : MixedKeys.WorkAt parents lower bound current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact coherent
  | left _ ih =>
      rw [MixedKeys.WorkAt] at ih; exact ih.1
  | right _ ih =>
      rw [MixedKeys.WorkAt] at ih; exact ih.2
  | executionGroup _ ih =>
      rw [MixedKeys.WorkAt] at ih; exact ih.2.2
  | item _ entry ih =>
      rw [MixedKeys.WorkAt] at ih
      exact (ih.2.2 _ (List.mem_of_getElem? entry)).lower (by omega)

/-- Every descriptor is within the global key interval. Witness: its located group
metadata or stream allocation.
-/
theorem coherent_node_bounds {parents lower bound work node kind dependencies birth}
    (coherent : MixedKeys.WorkAt parents lower bound work)
    (known : NodeAt work node kind dependencies birth)
    : lower ≤ node.key ∧ node.key < bound := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localWork := coherent_located coherent located.toCurrent
      rw [MixedKeys.WorkAt] at localWork
      exact ⟨(localWork.2.1 _ member).1, (localWork.2.1 _ member).2.1⟩
  | stream located =>
      have localWork := coherent_located coherent located.toCurrent
      rw [MixedKeys.WorkAt] at localWork
      exact ⟨localWork.1, localWork.2.1⟩

/-- Group dependencies are strictly smaller than the group's key. Witness: coherent
ancestry recovered from its structural descriptor.
-/
theorem coherent_group_dependencies {parents lower bound work node dependencies birth}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents lower bound work)
    (known : NodeAt work node .group dependencies birth)
    : ∀ key ∈ dependencies, key < node.key := by
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, rfl, rfl⟩ := known
  have localWork := coherent_located coherent located
  rw [MixedKeys.WorkAt] at localWork
  obtain ⟨_, keyBound, ancestors⟩ := localWork.2.1 group member
  intro key inDependencies
  exact (valid group.node.key keyBound key (ancestors ▸ inDependencies)).1

/-- Every group descriptor has a contributing task. Before any failure or publication
it cannot already be accounted for. Witness: that descriptor's own deferred task.
-/
theorem group_not_initially_accounted {work node parents birth}
    (known : NodeAt work node .group parents birth)
    : ¬NodeAccounted work (fun _ => .executionGroup []) [] [] node.key := by
  obtain ⟨address, groups, path, result, children, enclosing, group,
    located, member, rfl, rfl⟩ := known
  intro accounted
  have task := accounted (.executionGroup address) (groups.map (·.node.key))
    ⟨birth, .object path result, .executionGroup located⟩ (List.mem_map.mpr ⟨group, member, rfl⟩)
  rcases task with cancelled | published
  · exact cancelled.nonempty rfl
  · simp [Published] at published

-----------------------------------------------------------------------------------------
-- Nonvacuous factories
-----------------------------------------------------------------------------------------

/-- Ordered, continuous, nonempty work has valid initial notices. Witness: a least-key
first-boundary descriptor; every smaller dependency is absent from the entire work.
-/
theorem initialization_exists {parents bound work}
    (valid : Valid parents bound) (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (nonempty : work.size ≠ 0)
    : ∃ groups streams, Initializes work groups streams := by
  have candidates := initialCandidates_nonempty coherent nonempty
  have keysNonempty : ((initialCandidates work).map (fun entry => entry.1.key)) ≠ [] := by
    intro empty
    exact candidates (List.map_eq_nil_iff.mp empty)
  obtain ⟨key, member, least⟩ := nonempty_keys_minimum _ keysNonempty
  obtain ⟨⟨node, kind, dependencies⟩, inCandidates, rfl⟩ := List.mem_map.mp member
  have bounded := initialCandidates_lower valid coherent continuous ordered
    (fun entry member => least _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
  have known := initialCandidates_known (root := work) .root inCandidates
  have healthy : ¬NodeFailed work [] node.key := fun failure => failure.nonempty rfl
  have fresh : node.key ∉ announcedKeys [] [] := by simp [announcedKeys, pendingKeys]
  cases kind with
  | group =>
      have eligible : CanAnnounce work [] (fun _ => .executionGroup []) [] []
          node .group dependencies none := by
        refine ⟨fresh, healthy, Or.inr (group_not_initially_accounted known),
          by simp, ?_⟩
        intro key member
        refine ⟨fun failure => failure.nonempty rfl, Or.inl ?_⟩
        rintro ⟨birth, other, kind, otherDependencies, otherKnown, same⟩
        have lower := (coherent_node_bounds bounded otherKnown).1
        have smaller := coherent_group_dependencies valid coherent known key member
        dsimp only at lower
        omega
      refine ⟨[node], [], ⟨?_, by simp⟩⟩
      exact ⟨
        by simp,
        fun other member => by
          have same := List.mem_singleton.mp member
          subst other
          exact ⟨dependencies, none, known, eligible⟩,
        by simp
      ⟩
  | stream =>
      have empty : dependencies = [] := initialCandidates_stream_dependencies inCandidates
      subst dependencies
      have eligible : CanAnnounce work [] (fun _ => .executionGroup []) [] []
          node .stream [] none :=
        ⟨fresh, healthy, Or.inl rfl, by simp, Or.inl rfl⟩
      refine ⟨[], [node], ⟨?_, by simp⟩⟩
      exact ⟨
        by simp,
        by simp,
        fun other member => by
          have same := List.mem_singleton.mp member
          subst other
          exact ⟨[], none, known, eligible⟩
      ⟩

/-- Every nonempty prepared root work has a valid initialization. Witness: execution's
independent key-order and continuity certificates, followed by least-key initialization.
-/
theorem executeRoot_initialization_exists (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : let work :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType
            source selections).run
          0).1.work
      work.size ≠ 0 → ∃ groups streams, Initializes work groups streams := by
  intro work nonempty
  obtain ⟨_, parents, valid, coherent, continuous⟩ :=
    executeRoot_continuity schema resolvers variables fuel parentType source selections 0
  exact initialization_exists valid coherent continuous
    (executeRoot_streamOwnersOrdered schema resolvers variables fuel parentType source
      selections 0) nonempty

end GraphQL.IncrementalDelivery.WorkScheduler
