import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ParentLinkCompleteness

/-! Complete live parent links survive task updates, removal, and work integration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Frame rules for unchanged, filtered, and ref-preserving group records
-----------------------------------------------------------------------------------------

/-- Restricting the live map retains every surviving canonical parent-child edge.
Witness: apply completeness to the same two records in the original map.
-/
theorem State.ParentLinksComplete.of_subset {queue next : State} {parents}
    (complete : queue.ParentLinksComplete parents)
    (subset : next.groupNodes.Subset queue.groupNodes)
    : next.ParentLinksComplete parents :=
  fun child childMember parent parentMember head =>
    complete child (subset childMember) parent (subset parentMember) head

/-- Ref-preserving record updates retain completeness when every child list grows.
Witness: recover the old records, retain the canonical relation, and transport its edge.
-/
theorem State.ParentLinksComplete.mapGroupNodes {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (update : GroupNode → GroupNode)
    (refs : ∀ node, (update node).group.node.ref = node.group.node.ref)
    (children
      : ∀ node ∈ queue.groupNodes, node.childGroups.Subset (update node).childGroups)
    : ({ queue with groupNodes := queue.groupNodes.map update }).ParentLinksComplete
        parents := by
  intro child childMember parent parentMember head
  obtain ⟨oldChild, oldChildMember, rfl⟩ := List.mem_map.mp childMember
  obtain ⟨oldParent, oldParentMember, rfl⟩ := List.mem_map.mp parentMember
  rw [refs, refs] at head
  rw [refs]
  exact children oldParent oldParentMember
    (complete oldChild oldChildMember oldParent oldParentMember head)

/-- Replacing a looked-up record retains complete links when its ref and children survive.
Witness: unique refs identify every replaced record with the original lookup.
-/
theorem State.ParentLinksComplete.putGroupNode {queue : State} {parents ref node}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (found : queue.groupNode? ref = some node) (updated : GroupNode)
    (sameRef : updated.group.node.ref = node.group.node.ref)
    (children : node.childGroups.Subset updated.childGroups)
    : (queue.putGroupNode updated).ParentLinksComplete parents := by
  apply complete.mapGroupNodes
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

-----------------------------------------------------------------------------------------
-- Registration changes memberships, not the already completed parent links
-----------------------------------------------------------------------------------------

/-- Registering task memberships retains every live canonical parent edge.
Witness: each looked-up owner update preserves its ref and child list.
-/
theorem State.ParentLinksComplete.addTask {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (task : Task)
    : (queue.addTask task).ParentLinksComplete parents := by
  let registered : State := { queue with tasks := queue.tasks ++ [task] }
  let step (current : State) (group : Execution.DeliveryNode) : State :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode
          { node with tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have loop (more : List Execution.DeliveryNode) (current : State)
      (refs : current.GroupRefsUnique) (covered : current.ParentLinksComplete parents)
      : (more.foldl step current).ParentLinksComplete parents := by
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
          · exact ih _ (refs.putGroupNode _)
              (covered.putGroupNode refs found _ rfl (List.Subset.refl _))
  let current := task.groups.foldl step registered
  have covered := loop task.groups registered unique complete
  change (if task.groups.any (fun group => current.rootGroups.contains group.ref)
      && (current.taskNode? task.occurrence).isNone then
    { current with taskNodes := current.taskNodes ++ [{ task }] }
    else current).ParentLinksComplete parents
  split <;> exact covered

/-- Stream registration leaves the complete group-link map unchanged.
Witness: all branches only update stream and task bookkeeping.
-/
theorem State.ParentLinksComplete.addStreams {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (streams : List Stream)
    (parentTask : Option Occurrence)
    : (queue.addStreams streams parentTask).1.ParentLinksComplete parents := by
  unfold State.addStreams
  split
  · exact complete
  · dsimp only
    split <;> exact complete

/-- Integrating canonical work retains complete live parent links.
Witness: the exact two-pass group theorem followed by shape-preserving task/stream folds.
Permanent parent closure prevents a newly live parent from leaving an old child unlinked.
-/
theorem State.ParentLinksComplete.maybeIntegrateWork {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (unique : queue.GroupRefsUnique)
    (registered : queue.LiveGroupsRegistered)
    (closed : queue.ParentRegistryClosed parents) (work : Work)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    (parentTask : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parentTask).1.ParentLinksComplete parents := by
  have loop (more : List Task) (current : State)
      (refs : current.GroupRefsUnique) (covered : current.ParentLinksComplete parents)
      : (more.foldl State.addTask current).ParentLinksComplete parents := by
    induction more generalizing current with
    | nil => exact covered
    | cons task rest ih => exact ih _ (refs.addTask task) (covered.addTask refs task)
  exact (loop work.tasks _ (unique.addGroups work.groups)
    (complete.addGroups unique registered closed work.groups canonical)).addStreams
    work.streams parentTask

-----------------------------------------------------------------------------------------
-- Pruning, activation, and removal keep all edges between surviving records
-----------------------------------------------------------------------------------------

/-- Pruning taskless shells cannot remove an edge between two surviving records.
Witness: each recursive deletion filters the live map without editing any child list.
-/
theorem State.ParentLinksComplete.pruneEmptyGroups {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.ParentLinksComplete parents := by
  have loop (fuel : Nat) (current : State)
      (remaining kept : List Execution.DeliveryNode)
      (covered : current.ParentLinksComplete parents)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.ParentLinksComplete
          parents := by
    induction fuel generalizing current remaining kept with
    | zero => exact covered
    | succ fuel ih =>
        cases remaining with
        | nil => exact covered
        | cons group rest =>
            unfold State.pruneEmptyGroups.go
            split
            · exact ih _ _ _ covered
            · split
              · exact ih _ _ _ (covered.of_subset (fun _ member => (List.mem_filter.mp member).1))
              · exact ih _ _ _ covered
  exact loop _ queue groups [] complete

/-- Activation retains parent-link completeness because it leaves group records unchanged.
Witness: the checked group-core equation for starting new work.
-/
theorem State.ParentLinksComplete.startNewWork {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (newWork : NewWork)
    : (queue.startNewWork newWork).ParentLinksComplete parents :=
  complete.of_subset
    (by rw [(queue.startNewWork_groupCore newWork).1]; exact List.Subset.refl _)

/-- Removing a failed subtree preserves complete links between surviving groups.
Witness: the removal algorithm only filters the live group map.
-/
theorem State.ParentLinksComplete.removeGroup {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (ref : NodeRef)
    : (queue.removeGroup ref).ParentLinksComplete parents :=
  complete.of_subset (fun _ member => (List.mem_filter.mp member).1)

/-- Removing a task retains all canonical parent edges.
Witness: the group-record map changes only each record's task membership list.
-/
theorem State.ParentLinksComplete.removeTask {queue : State} {parents}
    (complete : queue.ParentLinksComplete parents) (occurrence : Occurrence)
    : (queue.removeTask occurrence).ParentLinksComplete parents := by
  have mapped := complete.mapGroupNodes
    (fun node => { node with tasks := node.tasks.filter (· != occurrence) })
    (fun _ => rfl) (fun _ _ => List.Subset.refl _)
  exact mapped

/-- Initialization establishes every live canonical parent-child link.
Witness: empty-map completeness, exact registration, pruning, and activation preservation.
The theorem permits child-first input and does not require a notice for every group.
-/
theorem createWorkQueue_parentLinksComplete (work : Work) (parents : Nat → NodeRefs)
    (canonical : ∀ group ∈ work.groups, group.parent = (parents group.node.ref).head?)
    : (State.initialize work).ParentLinksComplete parents := by
  have emptyComplete : ({} : State).ParentLinksComplete parents := by
    intro node member
    cases member
  have emptyRegistered : ({} : State).LiveGroupsRegistered := by
    intro node member
    cases member
  have emptyClosed : ({} : State).ParentRegistryClosed parents := by
    intro ref member
    cases member
  have integrated := emptyComplete.maybeIntegrateWork (by simp [State.GroupRefsUnique])
    emptyRegistered emptyClosed work canonical
  exact (integrated.pruneEmptyGroups _).startNewWork _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
