import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainValueCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupRootCoverage

/-! Cached startup removal supplies a queued failure path for every lost live owner.
The proof follows the actual startup fold and keeps notices distinct from immediate output.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

private theorem startTasks_nodes (tasks : List Occurrence) (queue : State)
    (available : List (Occurrence × Nat))
    : (tasks.foldl (fun current task => current.startTask task available)
        queue).groupNodes
      = queue.groupNodes := by
  induction tasks generalizing queue with
  | nil => rfl
  | cons task rest ih => rw [List.foldl_cons, ih, State.startTask_groupNodes]

/-- Startup retains the original child edges of every surviving lookup. -/
theorem State.startGroup_groupEdgesFrom (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.GroupEdgesFrom queue := by
  have cached : (queue.cacheTaskFailures available).GroupEdgesFrom queue := by
    intro key node found
    rw [State.groupNode?, State.cacheTaskFailures_groupNodes] at found
    exact ⟨node, found, rfl⟩
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · rename_i node found
    split
    · intro key node found
      rw [State.groupNode?, startTasks_nodes] at found
      exact cached key node found
    · exact ((queue.cacheTaskFailures available).filterRefs_groupEdgesFrom (fun candidate =>
        !(State.removeGroup.collect ((queue.cacheTaskFailures available).groupNodes.length + 1)
          (queue.cacheTaskFailures available) [node.group.node.ref] []).contains candidate)).trans
        cached

/-- A live owner outside this startup's queued failed subtree keeps its exact lookup. -/
theorem State.startGroup_outside_survives {queue : State} {parents key node}
    (forest : queue.RemovalForest parents) (ref : NodeRef)
    (found : queue.groupNode? key = some node)
    (available : List (Occurrence × Nat))
    (outside
      : ∀ failure ∈ (queue.startGroup ref available).2,
          ¬queue.LiveDescendant failure.group.ref key)
    : (queue.startGroup ref available).1.groupNode? key = some node := by
  have cachedNodes := queue.cacheTaskFailures_groupNodes available
  have cachedFound : (queue.cacheTaskFailures available).groupNode? key = some node := by
    simpa only [State.groupNode?, cachedNodes] using found
  have cachedForest := forest.of_subset
    (show (queue.cacheTaskFailures available).groupNodes.Subset queue.groupNodes from
      by rw [cachedNodes]; exact List.Subset.refl _)
  unfold State.startGroup at outside ⊢
  dsimp only at outside ⊢
  split
  · exact cachedFound
  · rename_i group source
    split
    · simpa only [State.groupNode?, startTasks_nodes] using cachedFound
    · rename_i rejected
      simp only [source, rejected, State.finishGroupFailure] at outside
      apply (State.removeGroup_groupNodeRetained cachedForest ?_).trans cachedFound
      intro path
      have oldPath : queue.LiveDescendant group.group.node.ref key :=
        path.of_groupNodes_eq cachedNodes.symm
      exact outside ⟨group.group.node, _⟩ List.mem_cons_self oldPath

private def startupStep (available : List (Occurrence × Nat))
    (acc : State × List GroupFailureEvent) (ref : NodeRef)
    : State × List GroupFailureEvent :=
  let (next, queued) := acc.1.startGroup ref available
  (next, acc.2 ++ queued)

private theorem startupFold_failuresSubset (refs : NodeRefs)
    (acc : State × List GroupFailureEvent) (available : List (Occurrence × Nat))
    : acc.2.Subset (refs.foldl (startupStep available) acc).2 := by
  induction refs generalizing acc with
  | nil => exact List.Subset.refl _
  | cons ref rest ih =>
      exact (List.subset_append_left _ _).trans (ih (startupStep available acc ref))

/-- Activating released work retains every old owner outside its actual queued failures. -/
theorem State.startNewWork_outside_survives {queue : State} {parents key node}
    (forest : queue.RemovalForest parents) (roots : NewWork)
    (found : queue.groupNode? key = some node)
    (available : List (Occurrence × Nat))
    (outside
      : ∀ failure ∈ (queue.startNewWork roots available).2,
          ¬queue.LiveDescendant failure.group.ref key)
    : (queue.startNewWork roots available).1.groupNode? key = some node := by
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (forest : acc.1.RemovalForest parents) (found : acc.1.groupNode? key = some node)
      (outside
        : ∀ failure ∈ (refs.foldl (startupStep available) acc).2,
            ¬acc.1.LiveDescendant failure.group.ref key)
      : (refs.foldl (startupStep available) acc).1.groupNode? key = some node := by
    induction refs generalizing acc with
    | nil => exact found
    | cons ref rest ih =>
        have stepOutside : ∀ failure ∈ (acc.1.startGroup ref available).2,
            ¬acc.1.LiveDescendant failure.group.ref key := by
          intro failure member
          exact outside failure (startupFold_failuresSubset rest (startupStep available acc ref)
            available (List.mem_append_right _ member))
        have retained := State.startGroup_outside_survives forest ref found available stepOutside
        have nextForest := forest.of_subset
          (acc.1.startGroup_groupNodes_sublist ref available).subset
        apply ih (startupStep available acc ref) nextForest retained
        intro failure member path
        exact outside failure member
          ((acc.1.startGroup_groupEdgesFrom ref available).liveDescendant path)
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).groupNodes = current.groupNodes := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih => rw [List.foldl_cons, ih, State.startStream_groupNodes]
  unfold State.startNewWork at outside ⊢
  rw [State.groupNode?, streams]
  let installed : State := { queue with
    rootGroups := queue.rootGroups ++ roots.newGroups.map Execution.DeliveryNode.ref }
  exact loop _ (installed, [])
    ⟨forest.uniqueChildren, forest.canonical, forest.increasing⟩ found
    (fun failure member path =>
      outside failure member
        (State.LiveDescendant.of_groupNodes_eq (queue := installed) (next := queue) rfl
          path))

/-- A live owner lost during activation lies below one of that activation's queued notices.
This is a causal topology fact over actual startup, independent of wire forwarding order.
-/
theorem State.startNewWork_ownerCut {queue : State} {parents key}
    (forest : queue.RemovalForest parents) (roots : NewWork)
    (live : ∃ node, queue.groupNode? key = some node)
    (available : List (Occurrence × Nat) := [])
    : (∃ node, (queue.startNewWork roots available).1.groupNode? key = some node)
      ∨ ∃ failure ∈ (queue.startNewWork roots available).2,
          queue.LiveDescendant failure.group.ref key := by
  classical
  by_cases affected : ∃ failure ∈ (queue.startNewWork roots available).2,
      queue.LiveDescendant failure.group.ref key
  · exact .inr affected
  · obtain ⟨node, found⟩ := live
    exact .inl ⟨node, State.startNewWork_outside_survives forest roots found available
      (fun failure member path => affected ⟨failure, member, path⟩)⟩

private theorem lookupAbsent_of_subset {before after : State} {key}
    (included : after.groupNodes.Subset before.groupNodes)
    (absent : before.groupNode? key = none)
    : after.groupNode? key = none := by
  apply List.find?_eq_none.mpr
  intro node member selected
  exact List.find?_eq_none.mp absent node (included member) selected

/-- Startup retains an old descendant path whenever its target survives removal. -/
theorem State.startGroup_preservesPath {queue : State} {parents root key}
    (forest : queue.RemovalForest parents) (ref : NodeRef)
    (path : queue.LiveDescendant root key) (available : List (Occurrence × Nat))
    (survives : ∃ node, (queue.startGroup ref available).1.groupNode? key = some node)
    : (queue.startGroup ref available).1.LiveDescendant root key := by
  have cachedNodes := queue.cacheTaskFailures_groupNodes available
  have cachedPath := path.of_groupNodes_eq cachedNodes
  have cachedForest := forest.of_subset
    (show (queue.cacheTaskFailures available).groupNodes.Subset queue.groupNodes from
      by rw [cachedNodes]; exact List.Subset.refl _)
  unfold State.startGroup at survives ⊢
  dsimp only at survives ⊢
  split
  · exact cachedPath
  · rename_i group found
    split
    · exact cachedPath.of_groupNodes_eq (startTasks_nodes _ _ available)
    · rename_i rejected
      simp only [found, rejected, Bool.false_eq_true, ↓reduceIte, State.finishGroupFailure]
        at survives
      apply cachedPath.removeGroup cachedForest
      intro affected
      obtain ⟨node, lookup⟩ := survives
      rw [(State.removeGroup_liveDescendant_absent cachedForest affected).1] at lookup
      contradiction

/-- Released-root activation preserves each old path whose target remains live. -/
theorem State.startNewWork_preservesPath {queue : State} {parents root key}
    (forest : queue.RemovalForest parents) (roots : NewWork)
    (path : queue.LiveDescendant root key) (available : List (Occurrence × Nat))
    (survives : ∃ node, (queue.startNewWork roots available).1.groupNode? key = some node)
    : (queue.startNewWork roots available).1.LiveDescendant root key := by
  have subset (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      : (refs.foldl (startupStep available) acc).1.groupNodes.Sublist acc.1.groupNodes := by
    induction refs generalizing acc with
    | nil => exact .refl _
    | cons ref rest ih =>
        exact (ih _).trans (acc.1.startGroup_groupNodes_sublist ref available)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (forest : acc.1.RemovalForest parents) (path : acc.1.LiveDescendant root key)
      (survives : ∃ node, (refs.foldl (startupStep available) acc).1.groupNode? key = some node)
      : (refs.foldl (startupStep available) acc).1.LiveDescendant root key := by
    induction refs generalizing acc with
    | nil => exact path
    | cons ref rest ih =>
        have stepSurvives := State.groupNode?_exists_before_subset
          (subset rest (startupStep available acc ref)).subset survives
        exact ih _ (forest.of_subset
          (acc.1.startGroup_groupNodes_sublist ref available).subset)
          (State.startGroup_preservesPath forest ref path available stepSurvives) survives
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).groupNodes = current.groupNodes := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih => rw [List.foldl_cons, ih, State.startStream_groupNodes]
  let initial : State := { queue with
    rootGroups := queue.rootGroups ++ roots.newGroups.map Execution.DeliveryNode.ref }
  let grouped := (roots.newGroups.map Execution.DeliveryNode.ref).foldl
    (startupStep available) (initial, [])
  have nodes := streams (roots.newStreams.map Execution.DeliveryNode.ref) grouped.1
  have groupedSurvives : ∃ node, grouped.1.groupNode? key = some node := by
    change ∃ node, ((roots.newStreams.map Execution.DeliveryNode.ref).foldl
      State.startStream grouped.1).groupNode? key = some node at survives
    simpa only [State.groupNode?, nodes] using survives
  have groupedPath := loop _ (initial, [])
    (forest.of_subset (after := initial) (List.Subset.refl _))
    (State.LiveDescendant.of_groupNodes_eq (queue := queue) (next := initial) rfl path)
    groupedSurvives
  exact groupedPath.of_groupNodes_eq nodes

private theorem startGroup_queuedRoot_absent (queue : State) (ref : NodeRef)
    (available : List (Occurrence × Nat)) {failure : GroupFailureEvent}
    (queued : failure ∈ (queue.startGroup ref available).2)
    : (queue.startGroup ref available).1.groupNode? failure.group.ref = none := by
  cases found : (queue.cacheTaskFailures available).groupNode? ref with
  | none => simp only [State.startGroup, found, List.not_mem_nil] at queued
  | some group =>
      simp only [State.startGroup, found] at queued ⊢
      by_cases rejected : (group.tasks.filterMap
          (fun task => ((queue.cacheTaskFailures available).taskNode? task).bind
            (·.rejection))).isEmpty
          = true
      · simp only [rejected, ↓reduceIte, List.not_mem_nil] at queued
      · simp only [rejected, State.finishGroupFailure] at queued ⊢
        have same := List.mem_singleton.mp queued
        subst failure
        exact State.removeGroup_ownGroupAbsent _ _

/-- Every queued startup notice already has no live owner at activation's endpoint. -/
theorem State.startNewWork_queuedRoot_absent (queue : State) (roots : NewWork)
    (available : List (Occurrence × Nat)) {failure : GroupFailureEvent}
    (queued : failure ∈ (queue.startNewWork roots available).2)
    : (queue.startNewWork roots available).1.groupNode? failure.group.ref = none := by
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : ∀ failure ∈ acc.2, acc.1.groupNode? failure.group.ref = none)
      : ∀ failure ∈ (refs.foldl (startupStep available) acc).2,
          (refs.foldl (startupStep available) acc).1.groupNode? failure.group.ref = none := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih (startupStep available acc ref)
        intro failure member
        rcases List.mem_append.mp member with old | fresh
        · exact lookupAbsent_of_subset (acc.1.startGroup_groupNodes_sublist ref available).subset
            (prior failure old)
        · exact startGroup_queuedRoot_absent acc.1 ref available fresh
  have streams (refs : NodeRefs) (current : State)
      : (refs.foldl State.startStream current).groupNodes = current.groupNodes := by
    induction refs generalizing current with
    | nil => rfl
    | cons ref rest ih => rw [List.foldl_cons, ih, State.startStream_groupNodes]
  unfold State.startNewWork at queued ⊢
  rw [State.groupNode?, streams]
  exact loop _ _ (by intro failure impossible; cases impossible) failure queued

/-- A queued failed root removes all of its old live descendants before forwarding. -/
theorem State.startNewWork_failedDescendant_absent {queue : State} {parents key failure}
    (forest : queue.RemovalForest parents) (roots : NewWork)
    (available : List (Occurrence × Nat))
    (queued : failure ∈ (queue.startNewWork roots available).2)
    (path : queue.LiveDescendant failure.group.ref key)
    : (queue.startNewWork roots available).1.groupNode? key = none := by
  cases found : (queue.startNewWork roots available).1.groupNode? key with
  | none => rfl
  | some node =>
      have finalPath := State.startNewWork_preservesPath forest roots path available ⟨node, found⟩
      obtain ⟨root, lookup⟩ := finalPath.found
      rw [State.startNewWork_queuedRoot_absent queue roots available queued] at lookup
      contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
