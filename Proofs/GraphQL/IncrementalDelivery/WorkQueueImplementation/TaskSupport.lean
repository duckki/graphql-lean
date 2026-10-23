import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A task supports registration of its contributors and their full ancestor chains
-----------------------------------------------------------------------------------------

/-- A task's structural occurrence supports `ref` through a contributor or its ancestors.
This does not assert that the ref contributes to the task or that the task has started.
-/
def Task.SupportsGroup (work : Execution.Work) (task : Task) (ref : NodeRef) : Prop :=
  ∃ address groups path result children producer owners fragment,
    task.occurrence = .executionGroup address
    ∧ Located work address (.executionGroup groups path result children) producer owners
    ∧ fragment ∈ groups
    ∧ ref ∈ fragment.node.ref :: fragment.ancestors.map Execution.DeliveryNode.ref

/-- A supporting task supplies an actual contributor-or-ancestor registration descriptor.
Witness: split its full chain at the supported ref and retain the remaining suffix.
-/
theorem Task.SupportsGroup.recordAt {work : Execution.Work} {task : Task} {ref : NodeRef}
    (supported : task.SupportsGroup work ref)
    : ∃ node dependencies, GroupRecordAt work node dependencies ∧ node.ref = ref := by
  obtain ⟨address, groups, path, result, children, producer, owners, fragment,
    _, located, member, contains⟩ := supported
  have mapped : ref ∈ (fragment.node :: fragment.ancestors).map Execution.DeliveryNode.ref :=
    contains
  obtain ⟨node, inChain, sameRef⟩ := List.mem_map.mp mapped
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp inChain
  refine ⟨
    node,
    after.map Execution.DeliveryNode.ref,
    ⟨
      fragment,
      GroupMetadata.located_fragments located
        (by
          rw [GroupMetadata.fragments]; exact List.mem_append_left _ member),
      after,
      ?_,
      rfl
    ⟩,
    sameRef
  ⟩
  exact ⟨before, split.symm⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
