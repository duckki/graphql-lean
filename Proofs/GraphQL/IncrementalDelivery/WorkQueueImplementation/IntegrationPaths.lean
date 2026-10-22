import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RemovalUpdates
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupPaths

/-! Work registration preserves all previously live group paths. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration may grow child lists, but never removes an existing child path
-----------------------------------------------------------------------------------------

/-- Ref-preserving maps with growing child lists retain every existing live path.
Witness: map each successful lookup and retain its child membership in the larger list.
-/
theorem State.LiveDescendant.mapGroupNodes_growing {queue : State} {root target}
    (path : queue.LiveDescendant root target) (update : GroupNode → GroupNode)
    (refs : ∀ node, (update node).group.node.ref = node.group.node.ref)
    (children
      : ∀ node ∈ queue.groupNodes, node.childGroups.Subset (update node).childGroups)
    : ({ queue with groupNodes := queue.groupNodes.map update }).LiveDescendant root
        target := by
  induction path with
  | self found =>
      exact .self (by rw [State.groupNode?_mapRefs queue update refs, found]; rfl)
  | child found linked below ih =>
      exact .child (by rw [State.groupNode?_mapRefs queue update refs, found]; rfl)
        (children _ (List.mem_of_find?_eq_some found) linked) ih

/-- Updating one looked-up record preserves paths when its child list only grows.
Witness: unique refs identify any replaced record with the looked-up original.
-/
theorem State.LiveDescendant.putGroupNode_growing {queue : State} {root target ref node}
    (path : queue.LiveDescendant root target) (unique : queue.GroupRefsUnique)
    (found : queue.groupNode? ref = some node) (updated : GroupNode)
    (sameRef : updated.group.node.ref = node.group.node.ref)
    (children : node.childGroups.Subset updated.childGroups)
    : (queue.putGroupNode updated).LiveDescendant root target := by
  apply path.mapGroupNodes_growing
    (fun old => if old.group.node.ref == updated.group.node.ref then updated else old)
  · intro old
    split
    · rename_i same
      exact (beq_iff_eq.mp same).symm
    · rfl
  · intro old member
    split
    · rename_i same
      have equal := unique.sameNode member (List.mem_of_find?_eq_some found)
        ((beq_iff_eq.mp same).trans sameRef)
      exact equal ▸ children
    · exact List.Subset.refl _

/-- Appending a shell leaves every old first-match lookup and path intact.
Witness: the left lookup already succeeds, so the appended record is never consulted.
-/
theorem State.LiveDescendant.appendGroupNode {queue : State} {root target}
    (path : queue.LiveDescendant root target) (node : GroupNode)
    : ({ queue with groupNodes := queue.groupNodes ++ [node] }).LiveDescendant root
        target := by
  have lookup {ref old} (found : queue.groupNode? ref = some old)
      : ({ queue with groupNodes := queue.groupNodes ++ [node] }).groupNode? ref = some old := by
    simp only [State.groupNode?, List.find?_append]
    change (queue.groupNode? ref).or _ = some old
    simp [found]
  induction path with
  | self found => exact .self (lookup found)
  | child found linked below ih => exact .child (lookup found) linked ih

/-- Installing a shell and growing its parent's child list retain every live path.
Witness: old lookups survive the append, and unique refs identify the updated parent.
-/
theorem State.LiveDescendant.addGroup {queue : State} {root target}
    (path : queue.LiveDescendant root target) (unique : queue.GroupRefsUnique)
    (group : Group)
    : (queue.addGroup group).LiveDescendant root target := by
  unfold State.addGroup
  split
  · exact path
  · rename_i guard
    have absent : group.node.ref ∉ queue.registeredGroups
        ∧ queue.groupNode? group.node.ref = none := by simpa using guard
    have appended : ({queue with
        registeredGroups := queue.registeredGroups ++ [group.node.ref],
        groupNodes := queue.groupNodes ++ [{group}]} : State).LiveDescendant root target :=
      State.LiveDescendant.of_groupNodes_eq
        (queue := {queue with groupNodes := queue.groupNodes ++ [{group}]}) rfl
        (path.appendGroupNode {group})
    split
    · exact appended
    · rename_i parent parentEq
      split
      · split <;> exact State.LiveDescendant.of_groupNodes_eq (queue := queue) rfl path
      · rename_i node found
        apply State.LiveDescendant.putGroupNode_growing (ref := parent)
          appended
        · have fresh : group.node.ref ∉ queue.groupNodes.map (fun node => node.group.node.ref) := by
            intro member
            obtain ⟨old, included, same⟩ := List.mem_map.mp member
            exact List.find?_eq_none.mp absent.2 old included (beq_iff_eq.mpr same)
          change ((queue.groupNodes ++ [({group} : GroupNode)]).map _).Nodup
          simpa [List.map_append, fresh] using List.nodup_append.mpr
            ⟨unique, by simp, by
              intro ref member other included same
              obtain rfl := List.mem_singleton.mp included
              exact fresh (same ▸ member)⟩
        · simp only [State.groupNode?, List.find?_append]
          change (queue.groupNode? _).or _ = some node
          simp [found]
        · rfl
        · split
          · exact List.Subset.refl _
          · exact List.subset_append_left _ _

/-- Recursive registration preserves old paths through immediate parent updates.
Witness: distinct refs and the existing path are preserved at each installation.
-/
theorem State.LiveDescendant.addGroups {queue : State} {root target}
    (path : queue.LiveDescendant root target) (unique : queue.GroupRefsUnique)
    (groups : List Group)
    : (queue.addGroups groups).1.LiveDescendant root target := by
  exact (State.addGroups_preserves
    (fun current => current.GroupRefsUnique ∧ current.LiveDescendant root target) groups
    (fun _ group _ prior => ⟨prior.1.addGroup group, prior.2.addGroup prior.1 group⟩)
    queue ⟨unique, path⟩).2

-----------------------------------------------------------------------------------------
-- Task and stream registration preserve the same paths through the remaining stages
-----------------------------------------------------------------------------------------

/-- Task registration changes memberships and counts, not the stored child topology.
Witness: each looked-up owner update preserves its child list; starting a task changes
only task bookkeeping after the owner fold.
-/
theorem State.LiveDescendant.addTask {queue : State} {root target}
    (path : queue.LiveDescendant root target) (unique : queue.GroupRefsUnique)
    (task : Task)
    : (queue.addTask task).LiveDescendant root target := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have loop (more : List Execution.DeliveryNode) (current : State)
      (refs : current.GroupRefsUnique) (covered : current.LiveDescendant root target)
      : (more.foldl step current).LiveDescendant root target := by
    induction more generalizing current with
    | nil => exact covered
    | cons group rest ih =>
        rw [List.foldl_cons]
        unfold step
        split
        · exact ih _ refs covered
        · rename_i node found
          split
          · exact ih _ refs covered
          · apply ih _ (refs.putGroupNode _)
            apply covered.putGroupNode_growing refs found
            · rfl
            · exact List.Subset.refl _
  let current := task.groups.foldl step registered
  have covered := loop task.groups registered unique
    (State.LiveDescendant.of_groupNodes_eq (queue := queue) rfl path)
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).LiveDescendant root target
  split
  · exact State.LiveDescendant.of_groupNodes_eq (queue := current) rfl covered
  · exact covered

/-- Stream registration preserves all group paths, including task-attached streams.
Witness: every branch leaves the group-node map unchanged.
-/
theorem State.LiveDescendant.addStreams {queue : State} {root target}
    (path : queue.LiveDescendant root target) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.LiveDescendant root target := by
  unfold State.addStreams
  split
  · exact State.LiveDescendant.of_groupNodes_eq (queue := queue) rfl path
  · dsimp only
    split <;> exact State.LiveDescendant.of_groupNodes_eq (queue := queue) rfl path

/-- Full work integration preserves every old live child path.
Witness: sequential group registration, task linking, and stream attachment retain the
path, while independent ref-uniqueness preservation supports each owner update.
-/
theorem State.LiveDescendant.maybeIntegrateWork {queue : State} {root target}
    (path : queue.LiveDescendant root target) (unique : queue.GroupRefsUnique)
    (work : Work) (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.LiveDescendant root target := by
  have loop (more : List Task) (current : State)
      (refs : current.GroupRefsUnique) (covered : current.LiveDescendant root target)
      : (more.foldl State.addTask current).LiveDescendant root target := by
    induction more generalizing current with
    | nil => exact covered
    | cons task rest ih => exact ih _ (refs.addTask task) (covered.addTask refs task)
  exact (loop work.tasks _ (unique.addGroups work.groups)
    (path.addGroups unique work.groups)).addStreams work.streams parentTask

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
