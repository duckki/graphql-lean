import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalCoverage

/-! Membership and cached-error updates preserve the group-removal forest. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Updates that leave every stored key and child list unchanged
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

/-- Mapping group records without changing keys commutes with lookup.
Witness: the lookup predicate is unchanged under the record map. -/
theorem State.groupNode?_mapKeys (queue : State) (update : GroupNode → GroupNode)
    (keys : ∀ node, (update node).group.node.key = node.group.node.key) (key : Nat)
    : ({ queue with groupNodes := queue.groupNodes.map update }).groupNode? key
      = (queue.groupNode? key).map update := by
  simp only [State.groupNode?, List.find?_map, Function.comp_def, keys]

/-- Record updates preserving keys and child lists preserve every live path.
Witness: map each path lookup and reuse its unchanged child edge. -/
theorem State.LiveDescendant.mapGroupNodes
    {queue : State} {root target} (path : queue.LiveDescendant root target)
    (update : GroupNode → GroupNode)
    (keys : ∀ node, (update node).group.node.key = node.group.node.key)
    (children : ∀ node ∈ queue.groupNodes, (update node).childGroups = node.childGroups)
    : ({ queue with groupNodes := queue.groupNodes.map update }).LiveDescendant
        root target := by
  induction path with
  | self found =>
      exact .self (by rw [State.groupNode?_mapKeys queue update keys, found]; rfl)
  | child found linked below ih =>
      exact .child
        (by rw [State.groupNode?_mapKeys queue update keys, found]; rfl)
        (by rw [children _ (List.mem_of_find?_eq_some found)]; exact linked)
        ih

/-- Shape-preserving record maps retain the finite removal forest.
Witness: each mapped edge comes from the same old pair of live group keys. -/
theorem State.RemovalForest.mapGroupNodes
    {queue : State} {parents} (forest : queue.RemovalForest parents)
    (update : GroupNode → GroupNode)
    (keys : ∀ node, (update node).group.node.key = node.group.node.key)
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
    rw [keys]
    exact forest.canonical old oldMember child linked
  · intro parent child parentMember childMember linked
    obtain ⟨oldParent, oldParentMember, rfl⟩ := List.mem_map.mp parentMember
    obtain ⟨oldChild, oldChildMember, rfl⟩ := List.mem_map.mp childMember
    rw [keys, children oldParent oldParentMember] at linked
    rw [keys, keys]
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
Witness: keys and child lists are unchanged by the membership filter. -/
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
Witness: unique live keys identify every matching entry with that lookup's record. -/
theorem State.GroupKeysUnique.counterUpdate_shape
    {queue : State} (unique : queue.GroupKeysUnique)
    {key node} (found : queue.groupNode? key = some node)
    (pending : Nat) (failure : Option Nat)
    : let update :=
        fun old : GroupNode =>
          if old.group.node.key == node.group.node.key then
            { node with pending, failure }
          else
            old
      (∀ old, (update old).group.node.key = old.group.node.key)
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
Witness: its record map has the unchanged shape certified by unique keys. -/
theorem State.LiveDescendant.putCounters
    {queue : State} {root target key node}
    (path : queue.LiveDescendant root target) (unique : queue.GroupKeysUnique)
    (found : queue.groupNode? key = some node) (pending : Nat) (failure : Option Nat)
    : (queue.putGroupNode { node with pending, failure }).LiveDescendant root target := by
  obtain ⟨keys, children⟩ := unique.counterUpdate_shape found pending failure
  exact path.mapGroupNodes _ keys children

/-- A counter/error update preserves the finite removal forest.
Witness: its record map leaves all keys and child edges unchanged. -/
theorem State.RemovalForest.putCounters
    {queue : State} {parents key node} (forest : queue.RemovalForest parents)
    (unique : queue.GroupKeysUnique) (found : queue.groupNode? key = some node)
    (pending : Nat) (failure : Option Nat)
    : (queue.putGroupNode { node with pending, failure }).RemovalForest parents := by
  obtain ⟨keys, children⟩ := unique.counterUpdate_shape found pending failure
  exact forest.mapGroupNodes _ keys children

/-- Counter/error updates cannot recreate an absent group lookup.
Witness: their key-preserving map takes an absent lookup to `none`. -/
theorem State.putCounters_groupNodeAbsent
    {queue : State} {key : Nat} {node : GroupNode}
    (absent : queue.groupNode? key = none)
    (pending : Nat) (failure : Option Nat)
    : (queue.putGroupNode { node with pending, failure }).groupNode? key = none := by
  let update := fun old : GroupNode =>
    if old.group.node.key == node.group.node.key then
      { node with pending, failure } else old
  have keys : ∀ old, (update old).group.node.key = old.group.node.key := by
    intro old
    dsimp only [update]
    split
    · rename_i same
      exact (beq_iff_eq.mp same).symm
    · rfl
  change ({ queue with groupNodes := queue.groupNodes.map update }).groupNode? key = none
  rw [State.groupNode?_mapKeys queue update keys, absent]
  rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
