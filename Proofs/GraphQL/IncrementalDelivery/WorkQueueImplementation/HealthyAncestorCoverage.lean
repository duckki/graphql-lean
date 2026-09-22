import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants

/-! Healthy live contributors prevent retired-parent gaps below their supported children. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A missing intermediate parent would contradict the existing retirement certificate
-----------------------------------------------------------------------------------------

/-- A healthy child below a live task-bearing ancestor has a live immediate parent.
Witness: a missing parent is registered and hence retired. Healthy retirement would also
retire the supporting ancestor, contradicting its live lookup. Taskless intermediate
parents use registration descriptors, not invented task-contribution witnesses.
-/
theorem State.HealthyRetiredAncestors.supported_parent_present {queue : State}
    {work parents failed child parent rest ancestor occurrence owners}
    (retirement : queue.HealthyRetiredAncestors work failed)
    (registered : queue.LiveGroupsRegistered)
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (found : queue.groupNode? child.group.node.key = some child)
    (known : GroupRecordAt work child.group.node (parent :: rest))
    (healthy : ¬GroupRecordInvalidated work failed child.group.node.key)
    (member : ancestor ∈ parent :: rest) (task : TaskHasOwners work occurrence owners)
    (contributes : ancestor ∈ owners)
    (live : ∃ node, queue.groupNode? ancestor = some node)
    : ∃ node, queue.groupNode? parent = some node := by
  cases parentFound : queue.groupNode? parent with
  | some node => exact ⟨node, rfl⟩
  | none =>
      have parentRegistered : parent ∈ queue.registeredGroups :=
        registry child.group.node.key (registered child (List.mem_of_find?_eq_some found))
          parent (by rw [← canonical _ _ known]; rfl)
      have retired : queue.RetiredGroup parent :=
        ⟨parentRegistered, (queue.groupNode?_eq_none_iff parent).mp parentFound⟩
      obtain ⟨ancestorNode, ancestorFound⟩ := live
      rcases List.mem_cons.mp member with same | above
      · rw [same, parentFound] at ancestorFound
        contradiction
      · obtain ⟨parentNode, parentKey, parentKnown⟩ := known.parent
        have parentHealthy : ¬GroupRecordInvalidated work failed parent :=
          fun invalid => healthy (.ancestor known List.mem_cons_self invalid)
        have ancestorRetired := retirement parent retired parentHealthy
          parentNode rest parentKnown parentKey ancestor above occurrence owners task contributes
        exact False.elim (ancestorRetired.2 (List.mem_map.mpr
          ⟨ancestorNode, List.mem_of_find?_eq_some ancestorFound,
            State.groupNode?_key ancestorFound⟩))

-----------------------------------------------------------------------------------------
-- Separate the remaining concrete link-completeness obligation from missing-parent health
-----------------------------------------------------------------------------------------

/-- Every live child's live canonical parent stores the child's key in its child list.
`parents` is the generated primary-parent assignment. This proof-side bookkeeping target
is not a new scheduler, host-source, or conformance premise.
-/
def State.ParentLinksComplete (queue : State) (parents : Nat → Keys) : Prop :=
  ∀ child ∈ queue.groupNodes,
  ∀ parent ∈ queue.groupNodes,
    (parents child.group.node.key).head? = some parent.group.node.key
    → child.group.node.key ∈ parent.childGroups

/-- A live task-bearing ancestor has a concrete path to its healthy live descendant.
Witness: follow exact generated parent suffixes. Retirement excludes each missing parent;
concrete parent-link completeness joins the live steps. Only that bookkeeping certificate
remains to be derived at integration boundaries; no output admission is assumed here.
-/
theorem State.ParentLinksComplete.healthy_ancestor_path {queue : State}
    {work parents failed child dependencies ancestor occurrence owners}
    (links : queue.ParentLinksComplete parents) (generated : ExecutedWork work)
    (records : queue.GroupNodesMatchWork work)
    (retirement : queue.HealthyRetiredAncestors work failed)
    (registered : queue.LiveGroupsRegistered)
    (registry : queue.ParentRegistryClosed parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (found : queue.groupNode? child.group.node.key = some child)
    (known : GroupRecordAt work child.group.node dependencies)
    (healthy : ¬GroupRecordInvalidated work failed child.group.node.key)
    (member : ancestor ∈ dependencies) (task : TaskHasOwners work occurrence owners)
    (contributes : ancestor ∈ owners)
    (live : ∃ node, queue.groupNode? ancestor = some node)
    : queue.LiveDescendant ancestor child.group.node.key := by
  induction dependencies generalizing child with
  | nil => cases member
  | cons parent rest ih =>
      obtain ⟨parentNode, parentFound⟩ := retirement.supported_parent_present registered
        registry canonical found known healthy member task contributes live
      have parentKey := State.groupNode?_key parentFound
      have head : (parent :: rest).head? = some parentNode.group.node.key := by
        simp [parentKey]
      have linked := links child (List.mem_of_find?_eq_some found) parentNode
        (List.mem_of_find?_eq_some parentFound) (by rw [← canonical _ _ known]; exact head)
      have edge : queue.LiveDescendant parentNode.group.node.key child.group.node.key :=
        .child (parentKey.symm ▸ parentFound) linked (.self found)
      rcases List.mem_cons.mp member with same | above
      · simpa only [parentKey, same] using edge
      · obtain ⟨parentDependencies, parentKnown⟩ :=
          records parentNode (List.mem_of_find?_eq_some parentFound)
        have chain := generated.groupRecordAncestryChain known parentKnown head
        have tail : rest = parentDependencies := (List.cons.inj chain).2
        have parentHealthy : ¬GroupRecordInvalidated work failed parentNode.group.node.key := by
          intro invalid
          exact healthy (.ancestor known List.mem_cons_self (parentKey ▸ invalid))
        have earlier := ih (parentKey.symm ▸ parentFound) (tail.symm ▸ parentKnown)
          parentHealthy above
        exact earlier.trans edge

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
