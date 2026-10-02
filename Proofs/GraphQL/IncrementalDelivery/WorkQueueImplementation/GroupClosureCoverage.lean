import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PruningBudget
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFrontierUniqueness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PromotionPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ForestPathPreservation

/-! Successful group closure transfers surviving descendants to its released frontier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Flushing shared memberships leaves the entire live child topology unchanged
-----------------------------------------------------------------------------------------

/-- Every old child path survives the concrete task-flush fold.
Witness: each selected task removal changes memberships, not live keys or child links.
-/
theorem State.LiveDescendant.flushGroupTasks {queue : State} {root target}
    (path : queue.LiveDescendant root target) (tasks : List Occurrence)
    (values : List ExecutionGroupValue) (streams : Keys)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.LiveDescendant root
        target := by
  induction tasks generalizing queue values streams with
  | nil => exact path
  | cons occurrence rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih path _ _
      · exact ih (path.removeTask occurrence) _ _

/-- Flushing preserves the derived finite forest and records every old child edge.
Witness: membership removal maps records without changing keys or children.
-/
theorem State.RemovalForest.flushGroupTasks {queue : State} {parents}
    (forest : queue.RemovalForest parents)
    (tasks : List Occurrence) (values : List ExecutionGroupValue) (streams : Keys)
    : let next := (tasks.foldl flushGroupTask (queue, values, streams)).1
      next.RemovalForest parents ∧ next.GroupEdgesFrom queue := by
  induction tasks generalizing queue values streams with
  | nil => exact ⟨forest, .refl queue⟩
  | cons occurrence rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih forest _ _
      · rename_i node found
        have next := ih (forest.removeTask occurrence)
          (match node.value with | none => values | some value => values ++ [value])
          (streams ++ node.childStreams)
        exact ⟨next.1, next.2.trans (queue.removeTask_groupEdgesFrom occurrence)⟩

-----------------------------------------------------------------------------------------
-- The removed root's surviving descendants are covered by newly released roots
-----------------------------------------------------------------------------------------

/-- The actual state immediately before successful-release pruning. -/
private abbrev successPruningState (queue : State) (group : GroupNode) : State :=
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  {
    flushed with
      groupNodes :=
        (flushed.groupNodes.filter
          (fun node => node.group.node.key != group.group.node.key))
      rootGroups := flushed.rootGroups.filter (· != group.group.node.key)
  }

/-- The actual live child descriptors passed to successful-release pruning. -/
private abbrev successPruningCandidates (queue : State) (group : GroupNode) :=
  group.childGroups.filterMap
    (fun key =>
      ((successPruningState queue group).groupNode? key).map
        (fun node => node.group.node))

/-- Successful release supplies the complete structural pruning premises.
Witness: membership flushing preserves links; filtering the unique parent leaves a live,
distinct incoming-free child frontier, including when some child links are stale.
-/
private theorem success_pruning_frontier {queue : State} {parents}
    (forest : queue.RemovalForest parents)
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    : let current := successPruningState queue group
      let candidates := successPruningCandidates queue group
      current.ChildLinksCanonical parents
      ∧ current.ChildGroupsUnique
      ∧ current.GroupFrontier candidates
      ∧ (candidates.map Execution.DeliveryNode.key).Nodup
      ∧ ∀ child ∈ candidates, ∃ node, current.groupNode? child.key = some node := by
  intro current candidates
  have flushedForest := (forest.flushGroupTasks group.tasks [] []).1
  have currentLinks : current.ChildLinksCanonical parents :=
    fun node member => flushedForest.canonical node (List.mem_filter.mp member).1
  have currentChildren : current.ChildGroupsUnique :=
    fun node member => flushedForest.uniqueChildren node (List.mem_filter.mp member).1
  have candidateFrontier : current.GroupFrontier candidates := by
    intro child member parent live linked
    have canonical := forest.canonical group (List.mem_of_find?_eq_some found) child.key
      (State.childDescriptors_member member).1
    have actual := currentLinks parent live child.key linked
    have same := Option.some.inj (actual.symm.trans canonical)
    have different : parent.group.node.key ≠ group.group.node.key := by
      simpa only [bne_iff_ne] using (List.mem_filter.mp live).2
    exact different same
  have candidateUnique : (candidates.map Execution.DeliveryNode.key).Nodup :=
    (current.childDescriptors_keys_sublist group.childGroups).nodup
      (forest.uniqueChildren group (List.mem_of_find?_eq_some found))
  have candidateLive : ∀ child ∈ candidates, ∃ node, current.groupNode? child.key = some node := by
    intro child member
    obtain ⟨key, linked, selected⟩ := List.mem_filterMap.mp member
    change (current.groupNode? key).map (fun node => node.group.node) = some child at selected
    cases lookup : current.groupNode? key with
    | none => simp [lookup] at selected
    | some node =>
        have same : node.group.node = child := by simpa [lookup] using selected
        exact ⟨node, by rw [← same, State.groupNode?_key lookup]; exact lookup⟩
  exact ⟨currentLinks, currentChildren, candidateFrontier, candidateUnique, candidateLive⟩

/-- Closing a group in the finite forest cannot strand any surviving descendant of it.
Witness: preserve its paths through shared-task flushing, remove the first edge's parent,
then apply complete pruning coverage to the distinct live child frontier. This is concrete
bookkeeping coverage, not an assumed abstract work-accounting or event-admission property.
-/
theorem State.finishGroupSuccess_surviving_descendant {queue : State} {parents target}
    (forest : queue.RemovalForest parents)
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (path : queue.LiveDescendant group.group.node.key target)
    (survives : ∃ node, (queue.finishGroupSuccess group).1.groupNode? target = some node)
    : ∃ root ∈ (queue.finishGroupSuccess group).2.2.newGroups,
        (queue.finishGroupSuccess group).1.LiveDescendant root.key target := by
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  let current := successPruningState queue group
  let candidates := successPruningCandidates queue group
  have flushedForest := (forest.flushGroupTasks group.tasks [] []).1
  obtain ⟨currentLinks, currentChildren, candidateFrontier, candidateUnique, candidateLive⟩ :=
    success_pruning_frontier forest found
  change ∃ root ∈ (current.pruneEmptyGroups candidates).2,
    (current.pruneEmptyGroups candidates).1.LiveDescendant root.key target
  apply State.pruneEmptyGroups_surviving_descendant currentLinks currentChildren
    candidateFrontier candidateUnique candidateLive ?_ survives
  cases path with
  | self lookup =>
      obtain ⟨node, retained⟩ := survives
      obtain ⟨old, oldFound, _⟩ :=
        (current.pruneEmptyGroups_descendants candidates).1 _ _ retained
      change (flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)).find?
          (fun node => node.group.node.key == group.group.node.key) = some old at oldFound
      rw [State.groupNode?_filterKeys flushed (fun key => key != group.group.node.key)] at oldFound
      simp at oldFound
  | @child key parent child target lookup linked below =>
      have equal : parent = group := Option.some.inj (lookup.symm.trans found)
      subst parent
      have belowFlushed := below.flushGroupTasks group.tasks [] []
      obtain ⟨childNode, childLookup⟩ := below.found
      have lower := forest.increasing (List.mem_of_find?_eq_some found)
        (List.mem_of_find?_eq_some childLookup) (State.groupNode?_key childLookup ▸ linked)
      rw [State.groupNode?_key childLookup] at lower
      have belowCurrent : current.LiveDescendant child target :=
        State.LiveDescendant.of_groupNodes_eq
          (queue := { flushed with groupNodes := (flushed.groupNodes.filter
            (fun node => node.group.node.key != group.group.node.key)) })
          (path := belowFlushed.filter_lower flushedForest lower) rfl
      obtain ⟨node, childFound⟩ := belowCurrent.found
      refine ⟨node.group.node, ?_, ?_⟩
      · apply List.mem_filterMap.mpr
        refine ⟨child, linked, ?_⟩
        change (current.groupNode? child).map (fun node => node.group.node) = _
        simp [childFound]
      · rw [State.groupNode?_key childFound]
        exact belowCurrent

/-- Successful closure preserves paths to targets outside its subtree.
Witness: shared-task flushing preserves paths, the closing-key filter cannot cut an
unrelated path, and complete frontier pruning preserves its surviving root.
-/
theorem State.LiveDescendant.finishGroupSuccess {queue : State} {parents root target}
    (path : queue.LiveDescendant root target)
    (forest : queue.RemovalForest parents)
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (outside : ¬queue.LiveDescendant group.group.node.key target)
    (survives : ∃ node, (queue.finishGroupSuccess group).1.groupNode? root = some node)
    : (queue.finishGroupSuccess group).1.LiveDescendant root target := by
  let flushed := (group.tasks.foldl flushGroupTask (queue, [], [])).1
  let current := successPruningState queue group
  let candidates := successPruningCandidates queue group
  have edges := (forest.flushGroupTasks group.tasks [] []).2
  obtain ⟨currentLinks, currentChildren, candidateFrontier, candidateUnique, candidateLive⟩ :=
    success_pruning_frontier forest found
  have initialPath := (path.flushGroupTasks group.tasks [] []).filter_outside
    (fun reached => outside (edges.liveDescendant reached))
  have currentPath : current.LiveDescendant root target :=
    State.LiveDescendant.of_groupNodes_eq
      (queue := { flushed with groupNodes := (flushed.groupNodes.filter
        (fun node => node.group.node.key != group.group.node.key)) }) rfl initialPath
  exact currentPath.pruneEmptyGroups currentLinks currentChildren candidateFrontier
    candidateUnique candidateLive survives

/-- Activating a successful release puts every surviving descendant under an active root.
Witness: the returned covering root is appended by `startNewWork`, which leaves all
group records and paths unchanged. No further host settlement is needed for activation.
-/
theorem State.finishGroupSuccess_activated_descendant {queue : State} {parents target}
    (forest : queue.RemovalForest parents)
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (path : queue.LiveDescendant group.group.node.key target)
    (survives : ∃ node, (queue.finishGroupSuccess group).1.groupNode? target = some node)
    : let result := queue.finishGroupSuccess group
      let next := result.1.startNewWork result.2.2
      ∃ root ∈ next.rootGroups, next.LiveDescendant root target := by
  intro result next
  obtain ⟨root, released, below⟩ :=
    State.finishGroupSuccess_surviving_descendant forest found path survives
  refine ⟨root.key, ?_, below.of_groupNodes_eq (result.1.startNewWork_groupCore result.2.2).1⟩
  rw [(result.1.startNewWork_groupCore result.2.2).2.2]
  exact List.mem_append_right _ (List.mem_map_of_mem released)

-----------------------------------------------------------------------------------------
-- Complete root coverage survives one successful close-and-activate step
-----------------------------------------------------------------------------------------

/-- Every previously root-covered surviving group remains root-covered after success.
Witness: closing-group descendants use the promoted frontier; unrelated paths retain
their roots and edges. Activation appends releases. No separate root-frontier law is used.
-/
theorem State.finishGroupSuccess_root_coverage {queue : State} {parents target}
    (forest : queue.RemovalForest parents)
    {group : GroupNode} (found : queue.groupNode? group.group.node.key = some group)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (survives : ∃ node, (queue.finishGroupSuccess group).1.groupNode? target = some node)
    : let result := queue.finishGroupSuccess group
      let next := result.1.startNewWork result.2.2
      ∃ root ∈ next.rootGroups, next.LiveDescendant root target := by
  intro result next
  classical
  obtain ⟨root, member, path⟩ := covered
  by_cases affected : queue.LiveDescendant group.group.node.key target
  · exact State.finishGroupSuccess_activated_descendant forest found affected survives
  · have outside : ¬queue.LiveDescendant group.group.node.key root :=
      fun reaches => affected (reaches.trans path)
    have different : root ≠ group.group.node.key := fun same => affected (same ▸ path)
    obtain ⟨old, oldFound⟩ := path.found
    have oldMember : root ∈ queue.groupNodes.map (fun node => node.group.node.key) :=
      List.mem_map.mpr ⟨old, List.mem_of_find?_eq_some oldFound, State.groupNode?_key oldFound⟩
    have retained := State.finishGroupSuccess_preserves_outside oldMember found outside
    have rootSurvives : ∃ node, result.1.groupNode? root = some node := by
      cases lookup : result.1.groupNode? root with
      | none =>
          obtain ⟨node, live, key⟩ := List.mem_map.mp retained
          have missing := List.find?_eq_none.mp lookup node live
          simp [key] at missing
      | some node => exact ⟨node, rfl⟩
    have retainedPath := path.finishGroupSuccess forest found affected rootSurvives
    refine ⟨root, ?_, retainedPath.of_groupNodes_eq
      (result.1.startNewWork_groupCore result.2.2).1⟩
    rw [(result.1.startNewWork_groupCore result.2.2).2.2]
    apply List.mem_append_left
    rw [State.finishGroupSuccess_rootGroups]
    exact List.mem_filter.mpr ⟨member, by simp [different]⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
