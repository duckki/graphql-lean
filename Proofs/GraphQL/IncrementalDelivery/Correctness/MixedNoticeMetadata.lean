import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferDependencies
import Proofs.GraphQL.IncrementalDelivery.Correctness.NodeRoles
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.GroupAccounting

/-! Structural support for mixed-work notice progress, using existing execution metadata.
Stream dependencies are deferred owners; deferred producers retain group ancestry.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.Ancestry Semantics.GeneralScheduling
open WorkScheduler

-----------------------------------------------------------------------------------------
-- Dependency keys have defer roles, including absent ancestor placeholders
-----------------------------------------------------------------------------------------

/-- A descriptor whose key has defer role must be a group, even in mixed work.
Witness: execution assigns a disjoint Boolean role to every actual stream key.
-/
theorem node_kind_of_defer_role {roles work node kind dependencies producer}
    (coherent : KeyRoles.WorkRoles roles work)
    (known : NodeAt work node kind dependencies producer)
    (role : roles node.key = false)
    : kind = .group := by
  have same := node_key_role coherent known
  cases kind with
  | group => rfl
  | stream =>
      change roles node.key = true at same
      rw [role] at same
      cases same

/-- Every ancestor listed by a group descriptor has defer role.
Witness: the fragment's metadata includes ancestor placeholders, not only actual nodes.
-/
theorem group_dependency_role {roles work node dependencies producer key}
    (coherent : KeyRoles.WorkRoles roles work)
    (known : NodeAt work node .group dependencies producer)
    (member : key ∈ dependencies)
    : roles key = false := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located included =>
      have localRoles := workRoles_located coherent located.toCurrent
      rw [KeyRoles.WorkRoles] at localRoles
      obtain ⟨ancestor, selected, rfl⟩ := List.mem_map.mp member
      exact (localRoles.1 _ included).2 ancestor selected

/-- A nonempty stream dependency list is exactly its deferred producer's owner list.
Witness: structural lookup preserves the nearest defer context and resets it at items.
-/
theorem stream_dependency_task {work node dependencies producer key}
    (known : NodeAt work node .stream dependencies producer)
    (member : key ∈ dependencies)
    : ∃ address birth path result,
        producer = some (.executionGroup address)
        ∧ TaskAt work (.executionGroup address) dependencies birth
            (.object path result) := by
  obtain ⟨address, items, located⟩ := known
  have context := located_producer_context located
  cases producer with
  | none => simp_all
  | some occurrence =>
      cases occurrence with
      | executionGroup producerAddress =>
          obtain ⟨birth, path, result, task⟩ := context
          exact ⟨producerAddress, birth, path, result, rfl, task⟩
      | item => simp_all

/-- Each explicit stream dependency is a represented group key, not a stream key.
Witness: the corresponding owner of its actual deferred producer.
-/
theorem stream_dependency_group {work node dependencies producer key}
    (known : NodeAt work node .stream dependencies producer)
    (member : key ∈ dependencies)
    : ∃ group ancestors birth,
        NodeAt work group .group ancestors birth ∧ group.key = key := by
  obtain ⟨address, birth, path, result, _, task⟩ := stream_dependency_task known member
  obtain ⟨group, ancestors, descriptor, same⟩ := task.executionGroup_owner member
  exact ⟨group, ancestors, birth, descriptor, same⟩

-----------------------------------------------------------------------------------------
-- A deferred producer supports its children even when the surrounding work has streams
-----------------------------------------------------------------------------------------

/-- Work produced by a deferred task retains that task's owner ancestry.
Witness: the generating deferred edge and append descent; an item edge cannot be that
same producer. No restriction is imposed on streams elsewhere in the work tree.
-/
theorem deferred_producer_context
    {parents work address current enclosing producer}
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (located : Located work address current (some (.executionGroup producer)) enclosing)
    : ∃ owners ancestor payload,
        TaskAt work (.executionGroup producer) owners ancestor payload
        ∧ DeferUnder parents owners current := by
  have context {address current birth enclosing}
      (navigation : StructuralEquivalence.Located work address current birth enclosing)
      {producer} (generated : birth = some (.executionGroup producer)) :
      ∃ owners ancestor payload,
        TaskAt work (.executionGroup producer) owners ancestor payload
        ∧ DeferUnder parents owners current := by
    induction navigation with
    | root => contradiction
    | left _ ih =>
        obtain ⟨owners, ancestor, payload, task, under⟩ := ih generated
        exact ⟨owners, ancestor, payload, task, under.1⟩
    | right _ ih =>
        obtain ⟨owners, ancestor, payload, task, under⟩ := ih generated
        exact ⟨owners, ancestor, payload, task, under.2⟩
    | executionGroup navigation =>
        cases generated
        have properties := dependencyProperties_located continuous ordered navigation.toCurrent
        simp only [DeferContinuous] at properties
        exact ⟨_, _, _, .executionGroup navigation.toCurrent, properties.1.1⟩
    | item => cases generated
  exact context (StructuralEquivalence.located_of_current located) rfl

/-- A group produced by deferred work reuses or depends on a producer owner.
Witness: continuity at its own producer, regardless of other mixed stream regions.
-/
theorem deferred_producer_dependency
    {parents bound work node dependencies producer}
    (coherent : MixedKeys.WorkAt parents 0 bound work)
    (continuous : DeferContinuous parents work) (ordered : StreamOwnersOrdered work)
    (known : NodeAt work node .group dependencies (some (.executionGroup producer)))
    : ∃ owners ancestor payload key,
        TaskAt work (.executionGroup producer) owners ancestor payload
        ∧ key ∈ owners
        ∧ (key = node.key ∨ key ∈ dependencies) := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      obtain ⟨owners, ancestor, payload, task, under⟩ :=
        deferred_producer_context continuous ordered located.toCurrent
      obtain ⟨key, contributes, support⟩ := under.1 _ member
      refine ⟨owners, ancestor, payload, key, task, contributes, ?_⟩
      rcases support with reused | dependency
      · exact Or.inl reused
      · have localWork := coherent_located coherent located.toCurrent
        rw [MixedKeys.WorkAt] at localWork
        exact Or.inr (by simpa only [(localWork.2.1 _ member).2.2] using dependency)

end GraphQL.IncrementalDelivery.Correctness
