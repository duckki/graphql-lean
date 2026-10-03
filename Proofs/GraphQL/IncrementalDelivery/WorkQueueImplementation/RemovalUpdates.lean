import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage

/-! Membership and cached-error updates preserve the group-removal forest. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Updates that leave every stored ref and child list unchanged
-----------------------------------------------------------------------------------------

/-- Changes outside the group-node map preserve every live descendant path.
Witness: transport the same lookups and child links through equality of the map.
-/
theorem State.LiveDescendant.of_groupNodes_eq {queue next : State} {root target}
    (same : next.groupNodes = queue.groupNodes)
    (path : queue.LiveDescendant root target)
    : next.LiveDescendant root target := by
  induction path with
  | self found => exact .self (by simpa only [State.groupNode?, same] using found)
  | child found linked below ih =>
      exact .child (by simpa only [State.groupNode?, same] using found) linked ih

/-- Mapping group records without changing refs commutes with lookup.
Witness: the lookup predicate is unchanged under the record map. -/
theorem State.groupNode?_mapRefs (queue : State) (update : GroupNode → GroupNode)
    (refs : ∀ node, (update node).group.node.ref = node.group.node.ref) (ref : NodeRef)
    : ({ queue with groupNodes := queue.groupNodes.map update }).groupNode? ref
      = (queue.groupNode? ref).map update := by
  simp only [State.groupNode?, List.find?_map, Function.comp_def, refs]

/-- Record updates preserving refs and child lists preserve every live path.
Witness: map each path lookup and reuse its unchanged child edge. -/
theorem State.LiveDescendant.mapGroupNodes
    {queue : State} {root target} (path : queue.LiveDescendant root target)
    (update : GroupNode → GroupNode)
    (refs : ∀ node, (update node).group.node.ref = node.group.node.ref)
    (children : ∀ node ∈ queue.groupNodes, (update node).childGroups = node.childGroups)
    : ({ queue with groupNodes := queue.groupNodes.map update }).LiveDescendant
        root target := by
  induction path with
  | self found =>
      exact .self (by rw [State.groupNode?_mapRefs queue update refs, found]; rfl)
  | child found linked below ih =>
      exact .child
        (by rw [State.groupNode?_mapRefs queue update refs, found]; rfl)
        (by rw [children _ (List.mem_of_find?_eq_some found)]; exact linked)
        ih

/-- Shape-preserving record maps retain the finite removal forest.
Witness: each mapped edge comes from the same old pair of live group refs. -/
theorem State.RemovalForest.mapGroupNodes
    {queue : State} {parents} (forest : queue.RemovalForest parents)
    (update : GroupNode → GroupNode)
    (refs : ∀ node, (update node).group.node.ref = node.group.node.ref)
    (children : ∀ node ∈ queue.groupNodes, (update node).childGroups = node.childGroups)
    : ({ queue with groupNodes := queue.groupNodes.map update }).RemovalForest
        parents := by
  refine ⟨?_, ?_, ?_⟩
  · intro node member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [children old oldMember]
    exact forest.uniqueChildren old oldMember
  · intro node member child linked
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rw [children old oldMember] at linked
    rw [refs]
    exact forest.canonical old oldMember child linked
  · intro parent child parentMember childMember linked
    obtain ⟨oldParent, oldParentMember, rfl⟩ := List.mem_map.mp parentMember
    obtain ⟨oldChild, oldChildMember, rfl⟩ := List.mem_map.mp childMember
    rw [refs, children oldParent oldParentMember] at linked
    rw [refs, refs]
    exact forest.increasing oldParentMember oldChildMember linked

/-- Removing task memberships does not change group paths.
Witness: only the task list of each stored group record is filtered. -/
theorem State.LiveDescendant.removeTask {queue : State} {root target}
    (path : queue.LiveDescendant root target) (occurrence : Occurrence)
    : (queue.removeTask occurrence).LiveDescendant root target := by
  have mapped := path.mapGroupNodes
    (fun node => { node with tasks := node.tasks.filter (· != occurrence) })
    (fun _ => rfl) (fun _ _ => rfl)
  refine State.LiveDescendant.of_groupNodes_eq ?_ mapped
  rfl

/-- Removing task memberships retains the removal forest.
Witness: refs and child lists are unchanged by the membership filter. -/
theorem State.RemovalForest.removeTask {queue : State} {parents}
    (forest : queue.RemovalForest parents) (occurrence : Occurrence)
    : (queue.removeTask occurrence).RemovalForest parents := by
  have mapped := forest.mapGroupNodes
    (fun node => { node with tasks := node.tasks.filter (· != occurrence) })
    (fun _ => rfl) (fun _ _ => rfl)
  exact ⟨mapped.uniqueChildren, mapped.canonical, mapped.increasing⟩

-----------------------------------------------------------------------------------------
-- A cached failure changes counters and errors, not group shape
-----------------------------------------------------------------------------------------

/-- Updating a looked-up record's counters preserves every replaced child list.
Witness: unique live refs identify every matching entry with that lookup's record. -/
theorem State.GroupRefsUnique.counterUpdate_shape
    {queue : State} (unique : queue.GroupRefsUnique)
    {ref node} (found : queue.groupNode? ref = some node)
    (pending : Nat) (failure : Option Nat)
    : let update :=
        fun old : GroupNode =>
          if old.group.node.ref == node.group.node.ref then
            { node with pending, failure }
          else
            old
      (∀ old, (update old).group.node.ref = old.group.node.ref)
      ∧ ∀ old ∈ queue.groupNodes, (update old).childGroups = old.childGroups := by
  constructor
  · intro old
    dsimp only
    split
    · rename_i same
      exact (beq_iff_eq.mp same).symm
    · rfl
  · intro old member
    dsimp only
    split
    · rename_i same
      have equal := unique.sameNode member (List.mem_of_find?_eq_some found)
        (beq_iff_eq.mp same)
      change node.childGroups = old.childGroups
      exact congrArg GroupNode.childGroups equal.symm
    · rfl

/-- A counter/error update preserves existing live descendant paths.
Witness: its record map has the unchanged shape certified by unique refs. -/
theorem State.LiveDescendant.putCounters
    {queue : State} {root target ref node}
    (path : queue.LiveDescendant root target) (unique : queue.GroupRefsUnique)
    (found : queue.groupNode? ref = some node) (pending : Nat) (failure : Option Nat)
    : (queue.putGroupNode { node with pending, failure }).LiveDescendant root target := by
  obtain ⟨refs, children⟩ := unique.counterUpdate_shape found pending failure
  exact path.mapGroupNodes _ refs children

/-- A counter/error update preserves the finite removal forest.
Witness: its record map leaves all refs and child edges unchanged. -/
theorem State.RemovalForest.putCounters
    {queue : State} {parents ref node} (forest : queue.RemovalForest parents)
    (unique : queue.GroupRefsUnique) (found : queue.groupNode? ref = some node)
    (pending : Nat) (failure : Option Nat)
    : (queue.putGroupNode { node with pending, failure }).RemovalForest parents := by
  obtain ⟨refs, children⟩ := unique.counterUpdate_shape found pending failure
  exact forest.mapGroupNodes _ refs children

/-- Counter/error updates cannot recreate an absent group lookup.
Witness: their ref-preserving map takes an absent lookup to `none`. -/
theorem State.putCounters_groupNodeAbsent
    {queue : State} {ref : NodeRef} {node : GroupNode}
    (absent : queue.groupNode? ref = none)
    (pending : Nat) (failure : Option Nat)
    : (queue.putGroupNode { node with pending, failure }).groupNode? ref = none := by
  let update := fun old : GroupNode =>
    if old.group.node.ref == node.group.node.ref then
      { node with pending, failure } else old
  have refs : ∀ old, (update old).group.node.ref = old.group.node.ref := by
    intro old
    dsimp only [update]
    split
    · rename_i same
      exact (beq_iff_eq.mp same).symm
    · rfl
  change ({ queue with groupNodes := queue.groupNodes.map update }).groupNode? ref = none
  rw [State.groupNode?_mapRefs queue update refs, absent]
  rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
