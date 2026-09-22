import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorChainMetadata

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration metadata includes taskless ancestors, not just task contributors
-----------------------------------------------------------------------------------------

/-- A registration descriptor occurs in a contributor's full ancestor chain in `work`.
`dependencies` records the suffix above that descriptor. This supplies no task ownership,
publication, or producer assertion for an ancestor-only record.
-/
def GroupRecordAt (work : Execution.Work) (node : Execution.DeliveryNode)
    (dependencies : Keys)
    : Prop :=
  ∃ address groups path result children producer owners fragment ancestors,
    Located work address (.executionGroup groups path result children) producer owners
    ∧ fragment ∈ groups
    ∧ (node :: ancestors).IsSuffix (fragment.node :: fragment.ancestors)
    ∧ dependencies = ancestors.map Execution.DeliveryNode.key

/-- Every actual task-contributing group has its own registration descriptor.
Witness: the entire contributor chain is a suffix of itself.
-/
theorem groupRecordAt_of_nodeAt {work node dependencies producer}
    (known : NodeAt work node .group dependencies producer)
    : GroupRecordAt work node dependencies := by
  obtain ⟨address, groups, path, result, children, owners, fragment,
    located, member, nodeEq, dependenciesEq⟩ := known
  refine ⟨address, groups, path, result, children, producer, owners, fragment,
    fragment.ancestors, located, member, ?_, dependenciesEq⟩
  rw [nodeEq]
  exact List.suffix_rfl

/-- A recorded nonempty ancestry list supplies its immediate parent's own descriptor.
Witness: removing the child from the chain suffix retains the parent's exact suffix.
-/
theorem GroupRecordAt.parent {work node key dependencies}
    (known : GroupRecordAt work node (key :: dependencies))
    : ∃ parent, parent.key = key ∧ GroupRecordAt work parent dependencies := by
  obtain ⟨address, groups, path, result, children, producer, owners, fragment,
    ancestors, located, member, suffix, equal⟩ := known
  cases ancestors with
  | nil => cases equal
  | cons parent rest =>
      obtain ⟨keyEq, dependenciesEq⟩ := List.cons.inj equal
      exact ⟨parent, keyEq.symm, address, groups, path, result, children, producer,
        owners, fragment, rest, located, member,
        (List.suffix_cons _ _).trans suffix, dependenciesEq⟩

/-- Each lowered chain entry retains precisely the ancestor suffix above its node.
Witness: induction over the nearest-first chain; lowering appends its head last.
-/
theorem workFromSpec_groupChain_member {nodes : List Execution.DeliveryNode}
    {group : Group} (member : group ∈ Work.fromExecution.groupChain nodes)
    : ∃ ancestors,
        (group.node :: ancestors).IsSuffix nodes
        ∧ group.parent = ancestors.head?.map Execution.DeliveryNode.key := by
  induction nodes with
  | nil => simp [Work.fromExecution.groupChain] at member
  | cons node ancestors ih =>
      rcases List.mem_append.mp member with earlier | last
      · obtain ⟨tail, suffix, parent⟩ := ih earlier
        exact ⟨tail, suffix.trans (List.suffix_cons _ _), parent⟩
      · have same := List.mem_singleton.mp last
        subst group
        exact ⟨ancestors, List.suffix_rfl, rfl⟩

/-- A contributor itself remains a candidate even when its ancestors precede it.
Witness: it is the final entry appended by chain lowering.
-/
theorem workFromSpec_groupChain_self (node : Execution.DeliveryNode)
    (ancestors : List Execution.DeliveryNode)
    : (⟨node, ancestors.head?.map Execution.DeliveryNode.key⟩ : Group)
      ∈ Work.fromExecution.groupChain (node :: ancestors) := by
  simp [Work.fromExecution.groupChain]

/-- Lowering any located chunk produces registration descriptors of the original work.
Witness: traverse only `combine` and select a suffix of an actual contributor chain.
-/
theorem workFromSpec_groups_recordAt
    {root current : Execution.Work} {address : Address} {producer : Option Occurrence}
    {owners : Keys} (located : Located root address current producer owners)
    {group : Group} (member : group ∈ (Work.fromExecution current address).groups)
    : ∃ dependencies,
        GroupRecordAt root group.node dependencies
        ∧ group.parent = dependencies.head? := by
  cases current with
  | empty => simp [Work.fromExecution] at member
  | combine left right =>
      rcases List.mem_append.mp member with inLeft | inRight
      · exact workFromSpec_groups_recordAt located.left inLeft
      · exact workFromSpec_groups_recordAt located.right inRight
  | executionGroup fragments path result children =>
      obtain ⟨fragment, fragmentMember, chainMember⟩ := List.mem_flatMap.mp member
      obtain ⟨ancestors, suffix, parent⟩ := workFromSpec_groupChain_member chainMember
      refine ⟨ancestors.map Execution.DeliveryNode.key,
        ⟨address, fragments, path, result, children, producer, owners, fragment,
          ancestors, located, fragmentMember, suffix, rfl⟩, ?_⟩
      simpa only [List.head?_map] using parent
  | stream node items => simp [Work.fromExecution] at member
termination_by sizeOf current

/-- Exact generated ancestry assignments also identify every taskless ancestor suffix.
Witness: descend the coherent parent chain, retaining the strict allocation-key bound.
-/
theorem ancestor_suffix_canonical {parents : Nat → Keys} {bound : Nat}
    (valid : AncestorChains.Valid parents bound) {node child : Execution.DeliveryNode}
    {ancestors dependencies : List Execution.DeliveryNode}
    (childBound : child.key < bound)
    (canonical : ancestors.map Execution.DeliveryNode.key = parents child.key)
    (suffix : (node :: dependencies).IsSuffix (child :: ancestors))
    : node.key < bound
      ∧ dependencies.map Execution.DeliveryNode.key = parents node.key := by
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
      · have parentBound : parent.key < bound :=
          Nat.lt_trans (valid.1 child.key childBound parent.key
            (by rw [← canonical]; simp)).1 childBound
        have parentCanonical := valid.2 child.key childBound parent.key
          (rest.map Execution.DeliveryNode.key) canonical.symm
        exact ih parentBound parentCanonical tail

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
