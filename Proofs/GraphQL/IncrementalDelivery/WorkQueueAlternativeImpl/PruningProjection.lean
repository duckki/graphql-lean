import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailurePruning
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ForestPathPreservation

/-! Compare dynamic disposal's surviving group keys with the reference removal kernel.
Membership/counter fields need not be equal: only live-owner presence is projected here.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (GroupNode)

private abbrev Kernel := ReferenceWorkQueue.State

-----------------------------------------------------------------------------------------
-- Task disposal preserves group topology and presence
-----------------------------------------------------------------------------------------

/-- Membership unlinking preserves all group lookups up to their task-list fields. -/
theorem PruningTasks.groupEdgesFrom {queue occurrences final targets}
    (trace : PruningTasks queue occurrences final targets)
    : final.GroupEdgesFrom queue := by
  induction trace with
  | nil => exact .refl _
  | missing _ _ ih | shared _ _ _ ih => exact ih
  | dispose _ _ _ ih =>
      exact ih.trans (ReferenceWorkQueue.State.removeTask_groupEdgesFrom _ _)

/-- Every old path survives the task-disposal fold. -/
theorem PruningTasks.liveDescendant {queue occurrences final targets root key}
    (trace : PruningTasks queue occurrences final targets)
    (path : queue.LiveDescendant root key)
    : final.LiveDescendant root key := by
  induction trace with
  | nil => exact path
  | missing _ _ ih | shared _ _ _ ih => exact ih path
  | dispose _ _ _ ih => exact ih (path.removeTask _)

/-- No task-disposal fold removes a live group. -/
theorem PruningTasks.groupPresent {queue occurrences final targets key}
    (trace : PruningTasks queue occurrences final targets)
    (live : ∃ node, queue.groupNode? key = some node)
    : ∃ node, final.groupNode? key = some node := by
  obtain ⟨node, found⟩ := live
  exact (trace.liveDescendant (.self found)).found

/-- The concrete task fold preserves the generated finite forest. -/
theorem PruningTasks.removalForest {queue occurrences final targets parents}
    (trace : PruningTasks queue occurrences final targets)
    (forest : queue.RemovalForest parents)
    : final.RemovalForest parents := by
  induction trace with
  | nil => exact forest
  | missing _ _ ih | shared _ _ _ ih => exact ih forest
  | dispose _ _ _ ih => exact ih (forest.removeTask _)

private abbrev withoutGroup (queue : Kernel) (key : Nat) : Kernel :=
  {
    queue with
      groupNodes := queue.groupNodes.filter (fun node => node.group.node.ref != key)
      rootGroups := queue.rootGroups.filter (· != key)
  }

private theorem withoutGroup_forest {queue : Kernel} {parents key}
    (forest : queue.RemovalForest parents)
    : (withoutGroup queue key).RemovalForest parents :=
  ⟨
    fun node member => forest.uniqueChildren node (List.mem_filter.mp member).1,
    fun node member => forest.canonical node (List.mem_filter.mp member).1,
    fun member other =>
      forest.increasing (List.mem_filter.mp member).1 (List.mem_filter.mp other).1
  ⟩

private theorem withoutGroup_absent (queue : Kernel) (key : Nat)
    : (withoutGroup queue key).groupNode? key = none := by
  change (queue.groupNodes.filter (fun node => node.group.node.ref != key)).find?
    (fun node => node.group.node.ref == key) = none
  rw [ReferenceWorkQueue.State.groupNode?_filterRefs queue (fun other => other != key) key]
  simp

private theorem pathSameGroups {before after : Kernel} {root key}
    (path : before.LiveDescendant root key) (same : after.groupNodes = before.groupNodes)
    : after.LiveDescendant root key := by
  induction path with
  | self found =>
      exact .self (by simpa only [ReferenceWorkQueue.State.groupNode?, same] using found)
  | child found linked _ ih =>
      exact .child (by simpa only [ReferenceWorkQueue.State.groupNode?, same] using found)
        linked ih

-----------------------------------------------------------------------------------------
-- The dynamic trace removes exactly the reachable frontier, not unrelated live owners
-----------------------------------------------------------------------------------------

/-- Dynamic group disposal introduces no new lookup or child edge. -/
theorem PruningGroups.groupEdgesFrom {queue pending final targets}
    (trace : PruningGroups queue pending final targets)
    : final.GroupEdgesFrom queue := by
  induction trace with
  | nil => exact .refl _
  | missing _ _ ih => exact ih
  | @visit group queue key current first keys final later found tasks rest ih =>
      exact (ih.trans tasks.groupEdgesFrom).trans (queue.filterRefs_groupEdgesFrom (· != key))

/-- A live owner outside every supplied failed subtree survives the disposal trace. -/
theorem PruningGroups.preservesOutside {queue pending final targets key}
    (trace : PruningGroups queue pending final targets)
    (live : ∃ node, queue.groupNode? key = some node)
    (outside : ∀ root ∈ pending, ¬queue.LiveDescendant root key)
    : ∃ node, final.groupNode? key = some node := by
  induction trace with
  | nil => exact live
  | missing _ _ ih =>
      exact ih live (fun root member => outside root (List.mem_cons_of_mem _ member))
  | @visit group queue root current first keys final later found tasks rest ih =>
      obtain ⟨node, lookup⟩ := live
      have headOutside := outside root List.mem_cons_self
      have retainedPath := (ReferenceWorkQueue.State.LiveDescendant.self lookup).filter_outside
        headOutside
      have retained : ∃ node, current.groupNode? key = some node :=
        tasks.groupPresent retainedPath.found
      apply ih retained
      intro child member path
      have prior := (tasks.groupEdgesFrom.trans
        (queue.filterRefs_groupEdgesFrom (· != root))).liveDescendant path
      rcases List.mem_append.mp member with linked | tail
      · exact headOutside (.child found linked prior)
      · exact outside child (List.mem_cons_of_mem _ tail) prior

/-- Every original live descendant of the supplied frontier is absent after disposal.
The finite forest matters here: a child's increasing path survives filtering its parent.
-/
theorem PruningGroups.coversDescendants {queue pending final targets parents}
    (trace : PruningGroups queue pending final targets)
    (forest : queue.RemovalForest parents)
    : ∀ root ∈ pending,
        ∀ key, queue.LiveDescendant root key → final.groupNode? key = none := by
  induction trace with
  | nil => simp
  | missing absent rest ih =>
      intro root member key path
      rcases List.mem_cons.mp member with same | tail
      · subst root
        obtain ⟨node, found⟩ := path.found
        rw [absent] at found
        contradiction
      · exact ih forest root tail key path
  | @visit group queue root current first keys final later found tasks rest ih =>
      have currentForest := tasks.removalForest (withoutGroup_forest forest)
      have fromHead (key : Nat) (path : queue.LiveDescendant root key)
          : final.groupNode? key = none := by
        cases path with
        | self lookup =>
            cases selected : final.groupNode? root with
            | none => rfl
            | some node =>
                obtain ⟨old, earlier, _⟩ :=
                  (rest.groupEdgesFrom.trans tasks.groupEdgesFrom) root node selected
                rw [withoutGroup_absent] at earlier
                contradiction
        | @child _ parent child key lookup linked below =>
            have same : parent = group := Option.some.inj (lookup.symm.trans found)
            subst parent
            obtain ⟨childNode, childFound⟩ := below.found
            have lower := forest.increasing (List.mem_of_find?_eq_some found)
              (List.mem_of_find?_eq_some childFound)
              (ReferenceWorkQueue.State.groupNode?_ref childFound ▸ linked)
            rw [ReferenceWorkQueue.State.groupNode?_ref found,
              ReferenceWorkQueue.State.groupNode?_ref childFound] at lower
            have kept := below.filter_lower forest lower
            exact ih currentForest child (List.mem_append_left _ linked) key
              (tasks.liveDescendant (pathSameGroups kept rfl))
      intro old member key path
      by_cases affected : queue.LiveDescendant root key
      · exact fromHead key affected
      · have tail : old ∈ keys := (List.mem_cons.mp member).resolve_left
          (fun same => affected (same ▸ path))
        exact ih currentForest old (List.mem_append_right _ tail) key
          (tasks.liveDescendant (pathSameGroups (path.filter_outside affected) rfl))

-----------------------------------------------------------------------------------------
-- The reference collector and dynamic disposal agree on surviving group presence
-----------------------------------------------------------------------------------------

/-- For one failed root, surviving-owner presence is exactly reference removal's presence.
This is a structural projection, not equality of task membership/counter fields or receipts.
-/
theorem PruningGroups.groupPresent_iff_removeGroup {queue final targets parents root key}
    (trace : PruningGroups queue [root] final targets)
    (forest : queue.RemovalForest parents)
    : (∃ node, final.groupNode? key = some node)
      ↔ ∃ node, (queue.removeGroup root).groupNode? key = some node := by
  let removed := ReferenceWorkQueue.State.removeGroup.collect
    (queue.groupNodes.length + 1) queue [root] []
  have filtered : (queue.removeGroup root).groupNode? key
      = if !removed.contains key then queue.groupNode? key else none := by
    exact queue.groupNode?_filterRefs (fun key => !removed.contains key) key
  by_cases affected : queue.LiveDescendant root key
  · have listed : key ∈ removed := ReferenceWorkQueue.State.removeGroup_collect_covers forest affected
    rw [trace.coversDescendants forest root List.mem_cons_self key affected, filtered]
    simp [listed]
  · have absent : key ∉ removed := fun listed => affected
      ((ReferenceWorkQueue.State.removeGroup_collect_mem_iff forest).mp listed)
    have missing : removed.contains key = false := by simpa using absent
    rw [filtered]
    simp only [missing, Bool.not_false, ↓reduceIte]
    constructor
    · rintro ⟨node, found⟩
      obtain ⟨old, earlier, _⟩ := trace.groupEdgesFrom key node found
      exact ⟨old, earlier⟩
    · intro live
      exact trace.preservesOutside live (by intro key member; cases List.mem_singleton.mp member; exact affected)

/-- Generated forest evidence transfers through alternative replay and terminal clearing. -/
theorem generatedReplay_removalForest {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (inputs : List (List GraphEvent))
    (valid : ReferenceWorkQueue.ValidGraphEvents work inputs.flatten)
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : ∃ parents,
        ((State.initialize work).runNormalized inputs).1.queue.RemovalForest parents := by
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · refine ⟨fun _ => [], ?_, ?_, ?_⟩
    · intro node member; cases member
    · intro node member; cases member
    · intro parent child member; cases member
  · exact generated.runNormalized_removalForest inputs valid

/-- At each generated replay boundary, dynamic single-root disposal agrees with the
actual reference removal on live-owner presence. No forest premise is exported.
-/
def GeneratedPruningGroupProjection : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ∀ root,
        let queue := ((State.initialize work).runNormalized inputs).1.queue
        ∃ final targets,
          PruningGroups queue [root] final targets
          ∧ (({ queue } : State).removeGroup root).2 = uniqueCleanupTargets targets
          ∧ ∀ key,
              (∃ node, final.groupNode? key = some node)
              ↔ ∃ node, (queue.removeGroup root).groupNode? key = some node

/-- Construct the exact dynamic trace and derive its generated kernel projection together. -/
theorem GeneratedPruningGroupProjection_holds : GeneratedPruningGroupProjection := by
  intro work inputs generated valid started root
  let queue := ((State.initialize work).runNormalized inputs).1.queue
  obtain ⟨parents, forest⟩ := generatedReplay_removalForest generated inputs valid started
  obtain ⟨final, targets, trace, same, _records⟩ :=
    pruningRemoval_witness { queue } root
  exact ⟨
    final,
    targets,
    trace,
    same,
    fun key => trace.groupPresent_iff_removeGroup forest
  ⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
