import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DeclarationMetadata
import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorChainMetadata

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration metadata includes taskless ancestors, not just task contributors
-----------------------------------------------------------------------------------------

/-- A registration descriptor belongs to an explicit declaration or contributor chain.
This records metadata without claiming that an unused declaration has a supporting task.
-/
def GroupRecordAt (work : Execution.Work) (node : Execution.DeliveryNode)
    (dependencies : NodeRefs)
    : Prop :=
  ∃ fragment ∈ GroupMetadata.fragments work,
    ∃ ancestors,
      (node :: ancestors).IsSuffix (fragment.node :: fragment.ancestors)
      ∧ dependencies = ancestors.map Execution.DeliveryNode.ref

/-- An actual contributor supplies its own registration record through located metadata. -/
theorem groupRecordAt_of_nodeAt {work node dependencies producer}
    (known : NodeAt work node .group dependencies producer)
    : GroupRecordAt work node dependencies := by
  obtain ⟨address, groups, path, result, children, owners, fragment,
    located, member, nodeEq, dependenciesEq⟩ := known
  refine ⟨fragment, GroupMetadata.located_fragments located ?_,
    fragment.ancestors, ?_, dependenciesEq⟩
  · rw [GroupMetadata.fragments]
    exact List.mem_append_left _ member
  · rw [nodeEq]
    exact List.suffix_rfl

/-- A recorded chain supplies its immediate parent's exact suffix. -/
theorem GroupRecordAt.parent {work node ref dependencies}
    (known : GroupRecordAt work node (ref :: dependencies))
    : ∃ parent, parent.ref = ref ∧ GroupRecordAt work parent dependencies := by
  obtain ⟨fragment, member, ancestors, suffix, equal⟩ := known
  cases ancestors with
  | nil => cases equal
  | cons parent rest =>
      obtain ⟨refEq, dependenciesEq⟩ := List.cons.inj equal
      exact ⟨parent, refEq.symm, fragment, member, rest,
        (List.suffix_cons _ _).trans suffix, dependenciesEq⟩

/-- Every registration candidate retains the metadata of its explicit declaration. -/
theorem workFromSpec_groups_metadata {current : Execution.Work} {address : Address}
    {group : Group}
    (member : group ∈ (Work.fromExecution current address).groups)
    : ∃ fragment ∈ GroupMetadata.fragments current,
        ∃ ancestors,
          (group.node :: ancestors).IsSuffix (fragment.node :: fragment.ancestors)
          ∧ group.parent = ancestors.head?.map Execution.DeliveryNode.ref := by
  cases current with
  | empty => simp [Work.fromExecution] at member
  | combine left right =>
      simp only [Work.fromExecution, Work.combine, List.mem_append] at member
      rcases member with inLeft | inRight
      · obtain ⟨fragment, found, ancestors, suffix, parent⟩ :=
          workFromSpec_groups_metadata (current := left) inLeft
        exact ⟨fragment, by rw [GroupMetadata.fragments]; exact List.mem_append_left _ found,
          ancestors, suffix, parent⟩
      · obtain ⟨fragment, found, ancestors, suffix, parent⟩ :=
          workFromSpec_groups_metadata (current := right) inRight
        exact ⟨fragment, by rw [GroupMetadata.fragments]; exact List.mem_append_right _ found,
          ancestors, suffix, parent⟩
  | declareGroups groups tasks =>
      simp only [Work.fromExecution, List.mem_append] at member
      rcases member with declared | nested
      · obtain ⟨fragment, found, rfl⟩ := List.mem_map.mp declared
        exact ⟨fragment, by rw [GroupMetadata.fragments]; exact List.mem_append_left _ found,
          fragment.ancestors, List.suffix_rfl, rfl⟩
      · obtain ⟨fragment, found, ancestors, suffix, parent⟩ :=
          workFromSpec_groups_metadata (current := tasks) nested
        exact ⟨fragment, by rw [GroupMetadata.fragments]; exact List.mem_append_right _ found,
          ancestors, suffix, parent⟩
  | executionGroup => cases member
  | stream node items => simp [Work.fromExecution] at member
termination_by sizeOf current

/-- Metadata inclusion connects any lowered work chunk with its original source. -/
theorem workFromSpec_groups_recordAt_of_fragments
    {root current : Execution.Work} {address : Address}
    (contained : (GroupMetadata.fragments current).Subset (GroupMetadata.fragments root))
    {group : Group} (member : group ∈ (Work.fromExecution current address).groups)
    : ∃ dependencies,
        GroupRecordAt root group.node dependencies
        ∧ group.parent = dependencies.head? := by
  obtain ⟨fragment, found, ancestors, suffix, parent⟩ := workFromSpec_groups_metadata member
  exact ⟨
    ancestors.map Execution.DeliveryNode.ref,
    ⟨fragment, contained found, ancestors, suffix, rfl⟩,
    by simpa only [List.head?_map] using parent
  ⟩

/-- Located subwork contributes only registration metadata already present in its root. -/
theorem workFromSpec_groups_recordAt
    {root current : Execution.Work} {address : Address} {producer : Option Occurrence}
    {owners : NodeRefs} (located : Located root address current producer owners)
    {group : Group} (member : group ∈ (Work.fromExecution current address).groups)
    : ∃ dependencies,
        GroupRecordAt root group.node dependencies ∧ group.parent = dependencies.head? :=
  workFromSpec_groups_recordAt_of_fragments (GroupMetadata.located_fragments located)
    member

/-- Root registration includes explicit declarations before address normalization. -/
theorem workFromSpec_groups_recordAt_root {work : Execution.Work} {group : Group}
    (member : group ∈ (Work.fromExecution work).groups)
    : ∃ dependencies,
        GroupRecordAt work group.node dependencies ∧ group.parent = dependencies.head? :=
  workFromSpec_groups_recordAt_of_fragments (fun _ member => member) member

/-- Exact generated ancestry assignments also identify every taskless ancestor suffix.
Witness: descend the coherent parent chain, retaining the strict allocation-ref bound.
-/
theorem ancestor_suffix_canonical {parents : Nat → NodeRefs} {bound : Nat}
    (valid : AncestorChains.Valid parents bound) {node child : Execution.DeliveryNode}
    {ancestors dependencies : List Execution.DeliveryNode}
    (childBound : child.ref < bound)
    (canonical : ancestors.map Execution.DeliveryNode.ref = parents child.ref)
    (suffix : (node :: dependencies).IsSuffix (child :: ancestors))
    : node.ref < bound
      ∧ dependencies.map Execution.DeliveryNode.ref = parents node.ref := by
  induction ancestors generalizing child with
  | nil =>
      rcases List.suffix_cons_iff.mp suffix with same | impossible
      · obtain ⟨nodeEq, dependenciesEq⟩ := List.cons.inj same
        subst node
        subst dependencies
        exact ⟨childBound, canonical⟩
      · have empty := List.eq_nil_of_suffix_nil impossible
        cases empty
  | cons parent rest ih =>
      rcases List.suffix_cons_iff.mp suffix with same | tail
      · obtain ⟨nodeEq, dependenciesEq⟩ := List.cons.inj same
        subst node
        subst dependencies
        exact ⟨childBound, canonical⟩
      · have parentBound : parent.ref < bound :=
          Nat.lt_trans (valid.1 child.ref childBound parent.ref
            (by rw [← canonical]; simp)).1 childBound
        have parentCanonical := valid.2 child.ref childBound parent.ref
          (rest.map Execution.DeliveryNode.ref) canonical.symm
        exact ih parentBound parentCanonical tail

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
