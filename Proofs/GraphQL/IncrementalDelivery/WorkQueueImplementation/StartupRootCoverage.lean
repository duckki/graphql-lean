import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureDescendants
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivation

/-! Startup subtree removal preserves coverage for every surviving group. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

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

/-- Startup retains the finite forest on its surviving group records. -/
theorem State.RemovalForest.startNewWork {queue : State} {parents}
    (forest : queue.RemovalForest parents) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.RemovalForest parents :=
  forest.of_subset (queue.startNewWork_groupNodes_sublist released available).subset

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

/-- A surviving lookup supplies an earlier live lookup under group-record inclusion.
Witness: its ref occurs in the earlier list, so a failed ref search would contradict it.
-/
theorem State.groupNode?_exists_before_subset {before after : State} {target}
    (included : after.groupNodes.Subset before.groupNodes)
    (survives : ∃ node, after.groupNode? target = some node)
    : ∃ node, before.groupNode? target = some node := by
  obtain ⟨node, found⟩ := survives
  have member := included (List.mem_of_find?_eq_some found)
  cases lookup : before.groupNode? target with
  | some old => exact ⟨old, rfl⟩
  | none =>
      have absent := List.find?_eq_none.mp lookup node member
      simp [State.groupNode?_ref found] at absent

/-- One group startup keeps coverage of each target that survives its immediate removal.
Witness: successful task starts change no group path; failure removes a whole subtree,
which cannot disconnect a surviving target from all its covering roots.
-/
theorem State.startGroup_root_coverage {queue : State} {parents target}
    (forest : queue.RemovalForest parents) (ref : NodeRef)
    (covered : ∃ root ∈ queue.rootGroups, queue.LiveDescendant root target)
    (available : List (Occurrence × Nat) := [])
    (survives : ∃ node, (queue.startGroup ref available).1.groupNode? target = some node)
    : ∃ root ∈ (queue.startGroup ref available).1.rootGroups,
        (queue.startGroup ref available).1.LiveDescendant root target := by
  have cachedNodes := queue.cacheTaskFailures_groupNodes available
  have cachedRoots := queue.cacheTaskFailures_rootGroups available
  have cachedForest : (queue.cacheTaskFailures available).RemovalForest parents :=
    forest.of_subset (by rw [cachedNodes]; exact List.Subset.refl _)
  have cachedCovered : ∃ root ∈ (queue.cacheTaskFailures available).rootGroups,
      (queue.cacheTaskFailures available).LiveDescendant root target := by
    obtain ⟨root, active, path⟩ := covered
    exact ⟨root, by rwa [cachedRoots], path.of_groupNodes_eq cachedNodes⟩
  unfold State.startGroup at survives ⊢
  dsimp only at survives ⊢
  split at *
  · exact cachedCovered
  · rename_i node found
    split at survives
    · rename_i healthy
      simp only [ite_eq_left healthy]
      have nodes := fold_projection State.groupNodes
        (fun current task => current.startTask task available)
        (fun current task => current.startTask_groupNodes task available)
        node.tasks (queue.cacheTaskFailures available)
      have roots := fold_projection State.rootGroups
        (fun current task => current.startTask task available)
        (fun current task => by unfold State.startTask; split; rfl; split <;> rfl)
        node.tasks (queue.cacheTaskFailures available)
      obtain ⟨root, active, path⟩ := cachedCovered
      exact ⟨root, by rwa [roots], path.of_groupNodes_eq nodes⟩
    · rename_i failed
      simp only [ite_eq_right failed]
      exact State.removeGroup_root_coverage cachedForest _ cachedCovered survives

/-- Startup preserves coverage from old or newly released roots for every surviving target.
Witness: activate each announced group with subtree-aware coverage, then start streams,
which change no group ref, active group root or path.
-/
theorem State.startNewWork_root_coverage {queue : State} {parents target}
    (forest : queue.RemovalForest parents) (released : NewWork)
    (covered
      : ∃ root ∈ queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref,
          queue.LiveDescendant root target)
    (available : List (Occurrence × Nat) := [])
    (survives
      : ∃ node, (queue.startNewWork released available).1.groupNode? target = some node)
    : ∃ root ∈ (queue.startNewWork released available).1.rootGroups,
        (queue.startNewWork released available).1.LiveDescendant root target := by
  let step (acc : State × List GroupFailureEvent) (ref : NodeRef) :=
    let (next, queued) := acc.1.startGroup ref available
    (next, acc.2 ++ queued)
  have loop (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (forest : acc.1.RemovalForest parents)
      (covered : ∃ root ∈ acc.1.rootGroups, acc.1.LiveDescendant root target)
      (survives : ∃ node, (refs.foldl step acc).1.groupNode? target = some node)
      : ∃ root ∈ (refs.foldl step acc).1.rootGroups,
          (refs.foldl step acc).1.LiveDescendant root target := by
    induction refs generalizing acc with
    | nil => exact covered
    | cons ref rest ih =>
        have subset (more : NodeRefs) (current : State × List GroupFailureEvent)
            : (more.foldl step current).1.groupNodes.Sublist current.1.groupNodes := by
          induction more generalizing current with
          | nil => exact List.Sublist.refl _
          | cons next more ih =>
              exact (ih _).trans (current.1.startGroup_groupNodes_sublist next available)
        have atStep := State.groupNode?_exists_before_subset (subset rest (step acc ref)).subset
          survives
        exact ih (step acc ref)
          (forest.of_subset (acc.1.startGroup_groupNodes_sublist ref available).subset)
          (State.startGroup_root_coverage forest ref covered available atStep) survives
  let initial : State := { queue with rootGroups :=
    queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref }
  let grouped := (released.newGroups.map Execution.DeliveryNode.ref).foldl step (initial, [])
  have nodes := fold_projection State.groupNodes State.startStream
    State.startStream_groupNodes (released.newStreams.map Execution.DeliveryNode.ref) grouped.1
  have roots := fold_projection State.rootGroups State.startStream
    (fun current ref => by unfold State.startStream; split <;> rfl)
    (released.newStreams.map Execution.DeliveryNode.ref) grouped.1
  change ∃ node, ((released.newStreams.map Execution.DeliveryNode.ref).foldl
    State.startStream grouped.1).groupNode? target = some node at survives
  have groupedSurvives : ∃ node, grouped.1.groupNode? target = some node := by
    simpa only [State.groupNode?, nodes] using survives
  have initialCovered : ∃ root ∈ initial.rootGroups, initial.LiveDescendant root target := by
    obtain ⟨root, active, path⟩ := covered
    exact ⟨root, active,
      State.LiveDescendant.of_groupNodes_eq (queue := queue) (next := initial) rfl path⟩
  obtain ⟨root, active, path⟩ := loop _ (initial, [])
    (forest.of_subset (after := initial) (List.Subset.refl _)) initialCovered groupedSurvives
  refine ⟨root, ?_, path.of_groupNodes_eq nodes⟩
  change root ∈ ((released.newStreams.map Execution.DeliveryNode.ref).foldl
    State.startStream grouped.1).rootGroups
  rw [roots]
  exact active

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
