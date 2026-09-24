import Proofs.GraphQL.IncrementalDelivery.Semantics.KeyRoles
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence

/-! Structural node lookup preserves execution's disjoint stream/defer key roles. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkScheduler

/-- A located subtree retains the original assignment of stream and defer key roles.
Witness: structural navigation through combine, deferred, and stream-item boundaries.
-/
theorem workRoles_located {roles work address current producer owners}
    (coherent : KeyRoles.WorkRoles roles work)
    (located : Located work address current producer owners)
    : KeyRoles.WorkRoles roles current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact coherent
  | left _ ih =>
      rw [KeyRoles.WorkRoles] at ih; exact ih.1
  | right _ ih | executionGroup _ ih =>
      rw [KeyRoles.WorkRoles] at ih; exact ih.2
  | item _ entry ih =>
      rw [KeyRoles.WorkRoles] at ih
      exact ih.2 _ (List.mem_of_getElem? entry)

/-- A known group's key has defer role and a known stream's key has stream role.
Witness: the metadata at its located boundary, retaining repeated descriptors.
-/
theorem node_key_role {roles work node kind dependencies producer}
    (coherent : KeyRoles.WorkRoles roles work)
    (known : NodeAt work node kind dependencies producer)
    : roles node.key = (kind == .stream) := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localRoles := workRoles_located coherent located.toCurrent
      rw [KeyRoles.WorkRoles] at localRoles
      exact (localRoles.1 _ member).1
  | stream located =>
      have localRoles := workRoles_located coherent located.toCurrent
      rw [KeyRoles.WorkRoles] at localRoles
      exact localRoles.1

/-- A stream and a deferred group cannot share an execution key. Witness: equality
would assign both Boolean roles to that key. No path or output-history premise is used.
-/
theorem stream_group_keys_distinct
    {roles work stream group streamDependencies groupDependencies streamBirth groupBirth}
    (coherent : KeyRoles.WorkRoles roles work)
    (streamKnown : NodeAt work stream .stream streamDependencies streamBirth)
    (groupKnown : NodeAt work group .group groupDependencies groupBirth)
    : stream.key ≠ group.key := by
  intro same
  have left := node_key_role coherent streamKnown
  have right := node_key_role coherent groupKnown
  rw [same, right] at left
  cases left

end GraphQL.IncrementalDelivery.Correctness
