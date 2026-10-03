import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedDescriptors
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupRecords

/-! Generated descriptor coherence connects ancestor records to actual contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Semantics.OwnerPaths (mapNodes fragmentNodes)

-----------------------------------------------------------------------------------------
-- One descriptor assignment covers both contributor nodes and ancestor-only records
-----------------------------------------------------------------------------------------

/-- Structural navigation preserves the descriptor certificate of the selected subwork.
Witness: address induction, following child work through groups and streamed items.
-/
theorem DescriptorMetadata.WorkAt.located
    {nodes bound work address current producer owners}
    (known : DescriptorMetadata.WorkAt nodes bound work)
    (located : Located work address current producer owners)
    : DescriptorMetadata.WorkAt nodes bound current := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact known
  | left _ ih => rw [DescriptorMetadata.WorkAt] at ih; exact ih.1
  | right _ ih => rw [DescriptorMetadata.WorkAt] at ih; exact ih.2
  | executionGroup _ ih => rw [DescriptorMetadata.WorkAt] at ih; exact ih.2
  | item _ entry ih =>
      rw [DescriptorMetadata.WorkAt] at ih
      exact ih.2 _ (List.mem_of_getElem? entry)

/-- A real structural node agrees with its complete allocated descriptor.
Witness: its located contributor map or stream descriptor supplies the assignment.
-/
theorem DescriptorMetadata.WorkAt.node {nodes bound work node kind dependencies producer}
    (known : DescriptorMetadata.WorkAt nodes bound work)
    (located : NodeAt work node kind dependencies producer)
    : DescriptorMetadata.Assigned nodes bound node := by
  cases StructuralEquivalence.nodeAt_of_current located with
  | group region member =>
      have localWork := known.located region.toCurrent
      rw [DescriptorMetadata.WorkAt] at localWork
      exact localWork.1 _ (List.mem_flatMap.mpr
        ⟨_, member, List.mem_cons_self⟩)
  | stream region =>
      have localWork := known.located region.toCurrent
      rw [DescriptorMetadata.WorkAt] at localWork
      exact localWork.1

/-- Every registration record, including taskless ancestors, has its assigned descriptor.
Witness: the record is a suffix member of a located contributor's full metadata chain.
-/
theorem DescriptorMetadata.WorkAt.record {nodes bound work node dependencies}
    (known : DescriptorMetadata.WorkAt nodes bound work)
    (record : GroupRecordAt work node dependencies)
    : DescriptorMetadata.Assigned nodes bound node := by
  obtain ⟨address, groups, path, result, children, producer, owners, fragment,
    ancestors, located, member, suffix, _⟩ := record
  have localWork := known.located located
  rw [DescriptorMetadata.WorkAt] at localWork
  exact localWork.1 node (List.mem_flatMap.mpr
    ⟨fragment, member, suffix.subset List.mem_cons_self⟩)

/-- Root-generated work has a complete descriptor assignment for all of its metadata.
Witness: instantiate the pure execution induction at the generating root and supply zero.
-/
theorem ExecutedWork.descriptorAssignment {work : Execution.Work}
    (generated : ExecutedWork work)
    : ∃ nodes bound, DescriptorMetadata.WorkAt nodes bound work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source,
    selections, same⟩ := generated
  obtain ⟨nodes, known⟩ := DescriptorMetadata.executeRoot_descriptors schema resolvers
    variables fuel parentType source selections 0
  exact ⟨nodes, _, same ▸ known⟩

/-- Equal generated refs identify the entire node, not only its attachment path.
Witness: both structural nodes agree with the same allocation assignment.
Conformance derives this fact internally from generated work.
-/
theorem ExecutedWork.nodeRefCoherent {work : Execution.Work}
    (generated : ExecutedWork work)
    : NodeRefCoherent work := by
  obtain ⟨nodes, bound, assigned⟩ := generated.descriptorAssignment
  intro first firstKind firstDependencies firstProducer
    second secondKind secondDependencies secondProducer firstAt secondAt same
  exact (assigned.node firstAt).2.symm.trans (same ▸ (assigned.node secondAt).2)

/-- A registration record and an actual contributor at the same generated ref are equal.
Witness: ancestor metadata and structural contributor metadata use one complete assignment.
-/
theorem ExecutedWork.record_eq_node
    {work record recordDependencies node dependencies producer}
    (generated : ExecutedWork work)
    (recordAt : GroupRecordAt work record recordDependencies)
    (nodeAt : NodeAt work node .group dependencies producer)
    (same : record.ref = node.ref)
    : record = node := by
  obtain ⟨nodes, bound, assigned⟩ := generated.descriptorAssignment
  exact (assigned.record recordAt).2.symm.trans (same ▸ (assigned.node nodeAt).2)

/-- Contributor-ref support upgrades a generated registration record to exact provenance.
Witness: find the real contributor at that ref and identify its complete descriptor.
No structural node is fabricated for an ancestor ref without a contributing task.
-/
theorem ExecutedWork.record_contributor {work node recordDependencies}
    (generated : ExecutedWork work) (record : GroupRecordAt work node recordDependencies)
    (contributes : ∃ dependencies, NodeHasDependencies work node.ref .group dependencies)
    : ∃ dependencies producer, NodeAt work node .group dependencies producer := by
  obtain ⟨dependencies, contributor, producer, located, same⟩ := contributes
  have equal := generated.record_eq_node record located same.symm
  exact ⟨dependencies, producer, equal ▸ located⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
