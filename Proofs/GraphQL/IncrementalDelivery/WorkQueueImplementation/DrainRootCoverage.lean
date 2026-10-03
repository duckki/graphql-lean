import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainNormalForm

/-! Actual mixed success/failure draining preserves coverage of surviving live groups. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- The existing finite forest survives pruning, closure, and activation
-----------------------------------------------------------------------------------------

/-- Restricting the live map preserves its finite removal forest.
Witness: every remaining child list and live edge already appeared in the old map.
-/
theorem State.RemovalForest.of_subset {before after : State} {parents}
    (forest : before.RemovalForest parents)
    (included : after.groupNodes.Subset before.groupNodes)
    : after.RemovalForest parents := by
  exact ⟨fun node member => forest.uniqueChildren node (included member),
    fun node member => forest.canonical node (included member),
    fun first second linked => forest.increasing (included first) (included second) linked⟩

/-- Success retains the forest through membership mapping, parent removal, and pruning.
Witness: the flush forest and the actual ref filters; no acyclicity is assumed anew.
-/
theorem State.RemovalForest.finishGroupSuccess {queue : State} {parents}
    (forest : queue.RemovalForest parents) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RemovalForest parents := by
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  let current : State := { flushed with
    groupNodes := (flushed.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref))
    rootGroups := flushed.rootGroups.filter (· != group.group.node.ref) }
  let candidates := group.childGroups.filterMap
    (fun ref => (current.groupNode? ref).map (fun node => node.group.node))
  have currentForest : current.RemovalForest parents :=
    (forest.flushGroupTasks group.tasks [] []).1.of_subset
      (fun _ member => (List.mem_filter.mp member).1)
  exact currentForest.of_subset (current.pruneEmptyGroups_groupNodes_sublist candidates).subset

/-- Activation preserves the same live forest.
Witness: the group-node map is unchanged while root lists and started tasks are updated.
-/
theorem State.RemovalForest.startNewWork {queue : State} {parents}
    (forest : queue.RemovalForest parents) (released : NewWork)
    : (queue.startNewWork released).RemovalForest parents := by
  apply forest.of_subset
  rw [(queue.startNewWork_groupCore released).1]
  exact List.Subset.refl _

-----------------------------------------------------------------------------------------
-- Failure removal retains root coverage for every surviving target
-----------------------------------------------------------------------------------------

/-- A failed subtree removal cannot disconnect a surviving root-covered target.
Witness: traversal coverage removes all descendants together; a surviving target keeps
its original path and root, and that root survives the exact root-ref filter.
-/
theorem State.removeGroup_root_coverage {queue : State} {parents target}
    (forest : queue.RemovalForest parents) (removed : Nat)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (survives : ∃ node, (queue.removeGroup removed).groupNode? target = some node)
    : ∃ root ∈ (queue.removeGroup removed).rootGroups,
        (queue.removeGroup removed).LiveDescendant root target := by
  obtain ⟨root, member, path⟩ := covered
  have outside : ¬queue.LiveDescendant removed target := by
    intro affected
    obtain ⟨node, found⟩ := survives
    rw [(State.removeGroup_liveDescendant_absent forest affected).1] at found
    contradiction
  have rootOutside : ¬queue.LiveDescendant removed root :=
    fun reaches => outside (reaches.trans path)
  have notRemoved : root ∉ State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [removed] [] := fun included => rootOutside
        (State.removeGroup_collect_mem_iff forest |>.mp included)
  refine ⟨root, List.mem_filter.mpr ⟨member, ?_⟩, path.removeGroup forest outside⟩
  simpa using notRemoved

-----------------------------------------------------------------------------------------
-- Compose the actual recursive mixed drain, retaining exact live paths
-----------------------------------------------------------------------------------------

/-- Every old root-covered group that survives a mixed drain remains root-covered.
Witness: a single concrete invariant combines forest preservation, edge provenance, and
coverage. Success promotes surviving descendants; failure removes subtrees atomically.
No event-admission, settled-value, or host-progress premise is needed.
-/
theorem State.drainReadyGroups_root_coverage {queue : State} {parents}
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    : ∀ target,
        (∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
        → (∃ node, queue.drainReadyGroups.1.groupNode? target = some node)
        → ∃ root ∈ queue.drainReadyGroups.1.rootGroups,
            queue.drainReadyGroups.1.LiveDescendant root target := by
  let property (current : State) := current.GroupRefsUnique ∧ current.RemovalForest parents
    ∧ ∀ target,
      (∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
      → (∃ node, current.groupNode? target = some node)
      → ∃ root ∈ current.rootGroups, current.LiveDescendant root target
  have result :=
    State.drainReadyGroups_preserves property
      (fun current node prior member _ _ _ => by
        let released := current.finishGroupSuccess node
        refine ⟨(prior.1.finishGroupSuccess node).startNewWork _,
          (prior.2.1.finishGroupSuccess node).startNewWork _, ?_⟩
        intro target covered survives
        have retained : ∃ child, released.1.groupNode? target = some child := by
          simpa only [State.groupNode?, (State.startNewWork_groupCore _ _).1]
            using survives
        obtain ⟨child, found⟩ := retained
        obtain ⟨old, oldFound, _⟩ :=
          (current.finishGroupSuccess_descendants node).1 _ _ found
        exact State.finishGroupSuccess_root_coverage prior.2.1
          (prior.1.groupNode?_of_mem member) (prior.2.2 target covered ⟨old, oldFound⟩)
          ⟨child, found⟩)
      (fun current node errors prior _ _ _ => by
        refine ⟨prior.1.finishGroupFailure node errors,
          prior.2.1.removeGroup node.group.node.ref, ?_⟩
        intro target covered survives
        obtain ⟨child, found⟩ := survives
        have edges := current.filterRefs_groupEdgesFrom (fun ref =>
          !(State.removeGroup.collect (current.groupNodes.length + 1) current
            [node.group.node.ref] []).contains ref)
        obtain ⟨old, oldFound, _⟩ := edges _ _ found
        exact State.removeGroup_root_coverage prior.2.1 _
          (prior.2.2 target covered ⟨old, oldFound⟩) ⟨child, found⟩)
      (show property queue from ⟨unique, forest, fun _ covered _ => covered⟩)
  exact result.2.2

/-- Empty post-drain roots rule out every previously covered surviving live group.
Witness: the generic drain coverage theorem would otherwise produce an actual root ref.
This is concrete endpoint coverage, not yet accounting for never-integrated spec work.
-/
theorem State.drainReadyGroups_no_stranded_group {queue : State} {parents target}
    (unique : queue.GroupRefsUnique) (forest : queue.RemovalForest parents)
    (empty : queue.drainReadyGroups.1.rootGroups = [])
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    : queue.drainReadyGroups.1.groupNode? target = none := by
  cases found : queue.drainReadyGroups.1.groupNode? target with
  | none => rfl
  | some node =>
      obtain ⟨root, member, _⟩ := State.drainReadyGroups_root_coverage unique forest target
        covered ⟨node, found⟩
      rw [empty] at member
      cases member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
