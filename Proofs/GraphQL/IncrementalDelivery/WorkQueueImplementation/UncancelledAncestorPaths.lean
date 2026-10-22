import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames

/-! Actual uncancelled retirement excludes missing parents below live supporting ancestors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A live child below a live task-bearing ancestor cannot have a missing canonical parent. -/
theorem ParentCutFrame.supported_parent_present
    {queue work parents child parent rest ancestor occurrence owners}
    (frame : ParentCutFrame queue work parents)
    (retirement : queue.UncancelledRetiredAncestors work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (found : queue.groupNode? child.group.node.ref = some child)
    (known : GroupRecordAt work child.group.node (parent :: rest))
    (member : ancestor ∈ parent :: rest) (task : TaskHasOwners work occurrence owners)
    (contributes : ancestor ∈ owners)
    (live : ∃ node, queue.groupNode? ancestor = some node)
    : ∃ node, queue.groupNode? parent = some node := by
  cases parentFound : queue.groupNode? parent with
  | some node => exact ⟨node, rfl⟩
  | none =>
      have childMember := List.mem_of_find?_eq_some found
      have parentRegistered : parent ∈ queue.registeredGroups :=
        frame.closed child.group.node.ref (frame.live child childMember)
          parent (by rw [← canonical _ _ known]; rfl)
      have parentSafe : parent ∉ queue.cancelledGroups := frame.safe child childMember parent
        (by rw [frame.fields child childMember, ← canonical _ _ known]; rfl)
      have retired : queue.RetiredGroup parent :=
        ⟨parentRegistered, (queue.groupNode?_eq_none_iff parent).mp parentFound⟩
      obtain ⟨ancestorNode, ancestorFound⟩ := live
      rcases List.mem_cons.mp member with same | above
      · rw [same, parentFound] at ancestorFound
        contradiction
      · obtain ⟨parentNode, parentRef, parentKnown⟩ := known.parent
        have ancestorRetired := retirement parent retired parentSafe
          parentNode rest parentKnown parentRef ancestor above occurrence owners task contributes
        exact False.elim (ancestorRetired.2 (List.mem_map.mpr
          ⟨ancestorNode, List.mem_of_find?_eq_some ancestorFound,
            State.groupNode?_ref ancestorFound⟩))

/-- Complete canonical links join every live task-bearing ancestor to its live descendant.
Missing parents are uncancelled by the live-parent frame, so their structural retirement
would contradict the supporting ancestor's live record. No failure-inventory health is used. -/
theorem ParentCutFrame.uncancelled_ancestor_path
    {queue work parents child dependencies ancestor occurrence owners}
    (frame : ParentCutFrame queue work parents)
    (retirement : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (found : queue.groupNode? child.group.node.ref = some child)
    (known : GroupRecordAt work child.group.node dependencies)
    (member : ancestor ∈ dependencies) (task : TaskHasOwners work occurrence owners)
    (contributes : ancestor ∈ owners)
    (live : ∃ node, queue.groupNode? ancestor = some node)
    : queue.LiveDescendant ancestor child.group.node.ref := by
  induction dependencies generalizing child with
  | nil => cases member
  | cons parent rest ih =>
      obtain ⟨parentNode, parentFound⟩ := frame.supported_parent_present retirement canonical
        found known member task contributes live
      have parentRef := State.groupNode?_ref parentFound
      have head : (parent :: rest).head? = some parentNode.group.node.ref := by
        simp [parentRef]
      have linked := frame.complete child (List.mem_of_find?_eq_some found) parentNode
        (List.mem_of_find?_eq_some parentFound) (by rw [← canonical _ _ known]; exact head)
      have edge : queue.LiveDescendant parentNode.group.node.ref child.group.node.ref :=
        .child (parentRef.symm ▸ parentFound) linked (.self found)
      rcases List.mem_cons.mp member with same | above
      · simpa only [parentRef, same] using edge
      · obtain ⟨parentDependencies, parentKnown⟩ :=
          frame.records parentNode (List.mem_of_find?_eq_some parentFound)
        have chain := generated.groupRecordAncestryChain known parentKnown head
        have tail : rest = parentDependencies := (List.cons.inj chain).2
        have earlier := ih (parentRef.symm ▸ parentFound) (tail.symm ▸ parentKnown) above
        exact earlier.trans edge

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
