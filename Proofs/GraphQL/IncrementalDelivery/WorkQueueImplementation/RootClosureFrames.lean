import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay

/-! Announced groups cannot disappear through another supported group's failure cleanup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A smaller frame suffices for failure cleanup, including latent error-cache updates
-----------------------------------------------------------------------------------------

/-- Structural metadata and retired ancestry for the currently announced group roots.
Unlike `LiveRootFrame`, this certificate does not constrain mutable task or error contents.
-/
structure RootClosureFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs)
    : Prop where
  records : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  roots : queue.RootAncestorsRetired work
  support
    : ∀ ref ∈ queue.rootGroups,
        ∃ dependencies, NodeHasDependencies work ref .group dependencies

/-- The independently proved live-root frame supplies the smaller closure frame.
Witness: retain only descriptor, ancestry, child-link, and active-root support facts.
-/
theorem LiveRootFrame.rootClosureFrame {queue work parents}
    (frame : LiveRootFrame queue work parents)
    : RootClosureFrame queue work parents :=
  ⟨frame.records, frame.links, frame.roots, frame.support.roots⟩

/-- Removing failed task memberships preserves all structural root-closure facts.
Witness: descriptors, child links, and active roots are unchanged; retirement persists.
-/
theorem RootClosureFrame.removeTask {queue work parents}
    (frame : RootClosureFrame queue work parents) (occurrence : Occurrence)
    : RootClosureFrame (queue.removeTask occurrence) work parents :=
  ⟨
    frame.records.removeTask _,
    frame.links.removeTask _,
    frame.roots.mono (fun _ member => member) (fun _ retired => retired.removeTask _),
    frame.support
  ⟩

/-- Failed subtree removal preserves the closure frame of every surviving root.
Witness: record and root filtering preserve metadata and permanent ancestor retirement.
-/
theorem RootClosureFrame.removeGroup {queue work parents}
    (frame : RootClosureFrame queue work parents) (ref : NodeRef)
    : RootClosureFrame (queue.removeGroup ref) work parents :=
  ⟨
    frame.records.removeGroup _,
    frame.links.removeGroup _,
    frame.roots.mono (queue.removeGroup_rootsSubset _)
      (fun _ retired => retired.removeGroup _),
    fun _ member => frame.support _ (queue.removeGroup_rootsSubset _ member)
  ⟩

/-- Exposing a rejection snapshot leaves all structural root-closure facts intact. -/
theorem RootClosureFrame.cacheTaskFailures {queue work parents}
    (frame : RootClosureFrame queue work parents) (available : List (Occurrence × Nat))
    : RootClosureFrame (queue.cacheTaskFailures available) work parents := by
  refine ⟨frame.records.cacheTaskFailures _, frame.links.cacheTaskFailures _, ?_, ?_⟩
  · intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    exact (frame.roots ref active).mono (fun _ retired => retired.cacheTaskFailures available)
  · intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    exact frame.support ref active

/-- Failure cleanup removes no other announced root than the failed root itself.
Witness: any collected ref has a live descendant path. A supported starting root cannot
reach a distinct root whose task-bearing ancestors are already retired. Stale links and
taskless intermediate groups need no additional restriction.
-/
theorem RootClosureFrame.removeGroup_tracks_roots_of_supported {queue work parents root}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (supported : ∃ dependencies, NodeHasDependencies work root .group dependencies)
    : ∀ ref ∈ queue.rootGroups,
        ref ∈ (queue.removeGroup root).rootGroups ∨ ref = root := by
  intro ref member
  by_cases collected : ref ∈ State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [root] []
  · obtain impossible | ⟨start, atStart, path⟩ :=
      State.removeGroup_collect_provenance _ _ _ _ collected
    · cases impossible
    · have same := List.mem_singleton.mp atStart
      rw [same] at path
      obtain ⟨dependencies, owner, producer, known, sameOwner⟩ := supported
      obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
      exact .inr ((frame.roots ref member).supported_path_eq generated frame.records
        frame.links canonical path ⟨producer, payload, task⟩ (sameOwner ▸ contributes)).symm
  · exact .inl (List.mem_filter.mpr ⟨member, by simpa using collected⟩)

/-- Active roots have the structural contributor required by protected removal. -/
theorem RootClosureFrame.removeGroup_tracks_roots {queue work parents root}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (active : root ∈ queue.rootGroups)
    : ∀ ref ∈ queue.rootGroups, ref ∈ (queue.removeGroup root).rootGroups ∨ ref = root :=
  frame.removeGroup_tracks_roots_of_supported generated canonical
    (frame.support root active)

-----------------------------------------------------------------------------------------
-- Exact notice tracking needs active roots or emitted completions, never silent cancellation
-----------------------------------------------------------------------------------------

/-- Initial and newly announced group refs remain active or have an emitted completion.
The initial refs and segment result are concrete queue data, not assumed scheduler output.
-/
def GroupNoticeCompletion (initial : NodeRefs) (result : State × List WorkQueueEvent)
    : Prop :=
  ∀ ref ∈ initial ++ result.2.flatMap rawGroupNoticeRefs,
    ref ∈ result.1.rootGroups ∨ ref ∈ result.2.flatMap rawGroupClosureRefs

/-- A silent root-preserving transition satisfies completion tracking.
Witness: all tracked refs remain active and there are no new notices.
-/
theorem GroupNoticeCompletion.silent {initial queue}
    (included : initial.Subset queue.rootGroups)
    : GroupNoticeCompletion initial (queue, []) := by
  intro ref member
  exact .inl (included (by simpa using member))

/-- Completion tracking composes across consecutive concrete segments.
Witness: surviving roots feed the next segment; emitted completions persist in the output.
-/
theorem GroupNoticeCompletion.append {initial first second}
    (left : GroupNoticeCompletion initial first)
    (right : GroupNoticeCompletion first.1.rootGroups second)
    : GroupNoticeCompletion initial (second.1, first.2 ++ second.2) := by
  intro ref member
  have later (member : ref ∈ first.1.rootGroups ++ second.2.flatMap rawGroupNoticeRefs) :=
    (right ref member).imp_right (List.mem_append_right (first.2.flatMap rawGroupClosureRefs))
  simp only [List.flatMap_append] at member ⊢
  rcases List.mem_append.mp member with old | noticed
  · rcases left ref (List.mem_append_left _ old) with active | closed
    · exact later (List.mem_append_left _ active)
    · exact .inr (List.mem_append_left _ closed)
  · rcases List.mem_append.mp noticed with earlier | next
    · rcases left ref (List.mem_append_right _ earlier) with active | closed
      · exact later (List.mem_append_left _ active)
      · exact .inr (List.mem_append_left _ closed)
    · exact later (List.mem_append_right _ next)

/-- Completion tracking depends on retained notice and closure memberships. -/
theorem GroupNoticeCompletion.perm {initial queue before after}
    (tracked : GroupNoticeCompletion initial (queue, before)) (same : before.Perm after)
    : GroupNoticeCompletion initial (queue, after) := by
  have transport {first second : List WorkQueueEvent} (perm : first.Perm second)
      (refs : WorkQueueEvent → NodeRefs) {ref} (member : ref ∈ first.flatMap refs)
      : ref ∈ second.flatMap refs := by
    obtain ⟨event, included, mentioned⟩ := List.mem_flatMap.mp member
    exact List.mem_flatMap.mpr ⟨event, perm.mem_iff.mp included, mentioned⟩
  intro ref member
  have earlier : ref ∈ initial ++ before.flatMap rawGroupNoticeRefs := by
    rcases List.mem_append.mp member with original | noticed
    · exact List.mem_append_left _ original
    · exact List.mem_append_right _ (transport same.symm rawGroupNoticeRefs noticed)
  exact (tracked ref earlier).imp_right (transport same rawGroupClosureRefs)

/-- An active failed closure completes every announced ref it removes.
Witness: protected roots exclude collateral removal, and the failed root has its own
failure control. This permits latent descendants to be cancelled without announcing them.
-/
theorem RootClosureFrame.finishGroupFailure_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (node : GroupNode) (errors : Nat) (active : node.group.node.ref ∈ queue.rootGroups)
    : GroupNoticeCompletion queue.rootGroups
        (
          (queue.finishGroupFailure node errors).1,
          [.groupFailure (queue.finishGroupFailure node errors).2.group
            (queue.finishGroupFailure node errors).2.errors]
        ) := by
  intro ref member
  have old : ref ∈ queue.rootGroups := by
    simpa [State.finishGroupFailure, rawGroupNoticeRefs] using member
  rcases frame.removeGroup_tracks_roots generated canonical active ref old with kept | closed
  · exact .inl kept
  · exact .inr (by simpa [State.finishGroupFailure, rawGroupClosureRefs] using closed)

-----------------------------------------------------------------------------------------
-- Failure cleanup preserves exact lifecycle tracking
-----------------------------------------------------------------------------------------

/-- One failed-owner step preserves the structural frame and exact notice tracking.
Witness: active cleanup closes its only removed announced ref; latent caching changes no
root or descriptor and leaves earlier tracking untouched.
-/
theorem RootClosureFrame.failureGroupStep_groupNoticeCompletion
    {acc : State × List WorkQueueEvent} {work parents initial}
    (frame : RootClosureFrame acc.1 work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (tracked : GroupNoticeCompletion initial acc) (errors : Nat)
    (group : Execution.DeliveryNode)
    : RootClosureFrame (failureGroupStep errors acc group).1 work parents
      ∧ GroupNoticeCompletion initial (failureGroupStep errors acc group) := by
  obtain ⟨queue, outputs⟩ := acc
  unfold failureGroupStep
  dsimp only
  split
  · exact ⟨frame, tracked⟩
  · rename_i node found
    split
    · rename_i active
      have activeRef : node.group.node.ref ∈ queue.rootGroups := by
        rw [State.groupNode?_ref found]
        exact List.contains_iff_mem.mp active
      exact ⟨frame.removeGroup _, tracked.append
        (frame.finishGroupFailure_groupNoticeCompletion generated canonical node errors
          activeRef)⟩
    · exact ⟨frame, tracked⟩

/-- The full failed-owner pass cannot silently remove any previously announced group.
Witness: iterate the exact single-pass handler with the preserved structural frame.
No source ordering, distinct-owner, or successful-output premise is required locally.
-/
theorem RootClosureFrame.failureGroupFold_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (errors : Nat) (groups : List Execution.DeliveryNode)
    : GroupNoticeCompletion queue.rootGroups
        (groups.foldl (failureGroupStep errors) (queue, [])) := by
  have loop (remaining : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent)
      (current : RootClosureFrame acc.1 work parents)
      (tracked : GroupNoticeCompletion queue.rootGroups acc)
      : GroupNoticeCompletion queue.rootGroups
          (remaining.foldl (failureGroupStep errors) acc) := by
    induction remaining generalizing acc with
    | nil => exact tracked
    | cons group rest ih =>
        obtain ⟨next, tracked⟩ := current.failureGroupStep_groupNoticeCompletion
          generated canonical tracked errors group
        exact ih _ next tracked
  exact loop groups (queue, []) frame (.silent (List.Subset.refl _))

/-- Task-failure handling completes every announced root it removes.
Witness: ignored settlements keep roots; accepted settlements remove task memberships,
then the exact owner pass closes its only removable announced refs.
-/
theorem RootClosureFrame.taskFailure_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (occurrence : Occurrence) (errors : Nat)
    : GroupNoticeCompletion queue.rootGroups (queue.taskFailure occurrence errors) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskFailure, found]
      exact .silent (List.Subset.refl _)
  | some incoming =>
      rw [queue.taskFailure_eq occurrence errors incoming found]
      let retained : RootClosureFrame
          (queue.putTaskNode { incoming with rejection := some errors }) work parents :=
        ⟨frame.records, frame.links, frame.roots, frame.support⟩
      exact retained.failureGroupFold_groupNoticeCompletion
        generated canonical errors incoming.task.groups

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
