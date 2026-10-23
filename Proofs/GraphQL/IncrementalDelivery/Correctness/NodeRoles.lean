import Proofs.GraphQL.IncrementalDelivery.Semantics.RefRoles
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence

/-! Structural node lookup preserves execution's disjoint stream/defer ref roles. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open WorkQueueSemantics

/-- Stripping declaration annotations retains role assignments of the underlying work. -/
theorem workRoles_withoutDeclarations {roles work} (known : RefRoles.WorkRoles roles work)
    : RefRoles.WorkRoles roles work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      simp only [RefRoles.WorkRoles] at known
      simpa only [Work.withoutDeclarations] using workRoles_withoutDeclarations known.2
  | _ => simpa only [Work.withoutDeclarations] using known
termination_by work

/-- A located subtree retains the original assignment of stream and defer ref roles.
Witness: structural navigation through combine, deferred, and stream-item boundaries.
-/
theorem workRoles_located {roles work address current producer owners}
    (coherent : RefRoles.WorkRoles roles work)
    (located : Located work address current producer owners)
    : RefRoles.WorkRoles roles current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact workRoles_withoutDeclarations coherent
  | left _ ih =>
      rw [RefRoles.WorkRoles] at ih; exact workRoles_withoutDeclarations ih.1
  | right _ ih | executionGroup _ ih =>
      rw [RefRoles.WorkRoles] at ih; exact workRoles_withoutDeclarations ih.2
  | item _ entry ih =>
      rw [RefRoles.WorkRoles] at ih
      exact workRoles_withoutDeclarations (ih.2 _ (List.mem_of_getElem? entry))

/-- A known group's ref has defer role and a known stream's ref has stream role.
Witness: the metadata at its located boundary, retaining repeated descriptors.
-/
theorem node_ref_role {roles work node kind dependencies producer}
    (coherent : RefRoles.WorkRoles roles work)
    (known : NodeAt work node kind dependencies producer)
    : roles node.ref = (kind == .stream) := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      have localRoles := workRoles_located coherent located.toCurrent
      rw [RefRoles.WorkRoles] at localRoles
      exact (localRoles.1 _ member).1
  | stream located =>
      have localRoles := workRoles_located coherent located.toCurrent
      rw [RefRoles.WorkRoles] at localRoles
      exact localRoles.1

/-- A stream and a deferred group cannot share an execution ref. Witness: equality
would assign both Boolean roles to that ref. No path or output-history premise is used.
-/
theorem stream_group_refs_distinct
    {roles work stream group streamDependencies groupDependencies streamBirth groupBirth}
    (coherent : RefRoles.WorkRoles roles work)
    (streamKnown : NodeAt work stream .stream streamDependencies streamBirth)
    (groupKnown : NodeAt work group .group groupDependencies groupBirth)
    : stream.ref ≠ group.ref := by
  intro same
  have left := node_ref_role coherent streamKnown
  have right := node_ref_role coherent groupKnown
  rw [same, right] at left
  cases left

end GraphQL.IncrementalDelivery.Correctness
