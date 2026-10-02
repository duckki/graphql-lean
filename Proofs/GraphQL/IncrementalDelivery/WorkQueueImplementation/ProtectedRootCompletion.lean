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
structure RootClosureFrame (queue : State) (work : Execution.Work) (parents : Nat → Keys)
    : Prop where
  records : queue.GroupNodesMatchWork work
  links : queue.ChildLinksCanonical parents
  roots : queue.RootAncestorsRetired work
  support
    : ∀ key ∈ queue.rootGroups,
        ∃ dependencies, NodeHasDependencies work key .group dependencies

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
    (frame : RootClosureFrame queue work parents) (key : Nat)
    : RootClosureFrame (queue.removeGroup key) work parents :=
  ⟨
    frame.records.removeGroup _,
    frame.links.removeGroup _,
    frame.roots.mono (queue.removeGroup_rootsSubset _)
      (fun _ retired => retired.removeGroup _),
    fun _ member => frame.support _ (queue.removeGroup_rootsSubset _ member)
  ⟩

/-- Failure cleanup removes no other announced root than the failed root itself.
Witness: any collected key has a live descendant path. A supported starting root cannot
reach a distinct root whose task-bearing ancestors are already retired. Stale links and
taskless intermediate groups need no additional restriction.
-/
theorem RootClosureFrame.removeGroup_tracks_roots {queue work parents root}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (active : root ∈ queue.rootGroups)
    : ∀ key ∈ queue.rootGroups,
        key ∈ (queue.removeGroup root).rootGroups ∨ key = root := by
  intro key member
  by_cases collected : key ∈ State.removeGroup.collect (queue.groupNodes.length + 1)
      queue [root] []
  · obtain impossible | ⟨start, atStart, path⟩ :=
      State.removeGroup_collect_provenance _ _ _ _ collected
    · cases impossible
    · have same := List.mem_singleton.mp atStart
      rw [same] at path
      obtain ⟨dependencies, owner, producer, known, sameOwner⟩ := frame.support root active
      obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
      exact .inr ((frame.roots key member).supported_path_eq generated frame.records
        frame.links canonical path ⟨producer, payload, task⟩ (sameOwner ▸ contributes)).symm
  · exact .inl (List.mem_filter.mpr ⟨member, by simpa using collected⟩)

-----------------------------------------------------------------------------------------
-- Exact notice tracking needs active roots or emitted completions, never silent cancellation
-----------------------------------------------------------------------------------------

/-- Initial and newly announced group keys remain active or have an emitted completion.
The initial keys and segment result are concrete queue data, not assumed scheduler output.
-/
def GroupNoticeCompletion (initial : Keys) (result : State × List WorkQueueEvent)
    : Prop :=
  ∀ key ∈ initial ++ result.2.flatMap rawGroupNoticeKeys,
    key ∈ result.1.rootGroups ∨ key ∈ result.2.flatMap rawGroupClosureKeys

/-- A silent root-preserving transition satisfies completion tracking.
Witness: all tracked keys remain active and there are no new notices.
-/
theorem GroupNoticeCompletion.silent {initial queue}
    (included : initial.Subset queue.rootGroups)
    : GroupNoticeCompletion initial (queue, []) := by
  intro key member
  exact .inl (included (by simpa using member))

/-- Completion tracking composes across consecutive concrete segments.
Witness: surviving roots feed the next segment; emitted completions persist in the output.
-/
theorem GroupNoticeCompletion.append {initial first second}
    (left : GroupNoticeCompletion initial first)
    (right : GroupNoticeCompletion first.1.rootGroups second)
    : GroupNoticeCompletion initial (second.1, first.2 ++ second.2) := by
  intro key member
  have later (member : key ∈ first.1.rootGroups ++ second.2.flatMap rawGroupNoticeKeys) :=
    (right key member).imp_right (List.mem_append_right (first.2.flatMap rawGroupClosureKeys))
  simp only [List.flatMap_append] at member ⊢
  rcases List.mem_append.mp member with old | noticed
  · rcases left key (List.mem_append_left _ old) with active | closed
    · exact later (List.mem_append_left _ active)
    · exact .inr (List.mem_append_left _ closed)
  · rcases List.mem_append.mp noticed with earlier | next
    · rcases left key (List.mem_append_right _ earlier) with active | closed
      · exact later (List.mem_append_left _ active)
      · exact .inr (List.mem_append_left _ closed)
    · exact later (List.mem_append_right _ next)

/-- Successful closure and activation track every old or newly released group exactly.
Witness: the only removed old root has the emitted success control; releases are activated.
-/
theorem State.finishGroupSuccess_groupNoticeCompletion (queue : State) (node : GroupNode)
    : GroupNoticeCompletion queue.rootGroups
        (
          (queue.finishGroupSuccess node).1.startNewWork
            (queue.finishGroupSuccess node).2.2,
          (queue.finishGroupSuccess node).2.1
        ) := by
  intro key member
  rw [(State.startNewWork_groupCore _ _).2.2]
  rcases List.mem_append.mp member with old | noticed
  · rcases queue.finishGroupSuccess_tracks_roots node key old with active | closed
    · exact .inl (List.mem_append_left _ active)
    · exact .inr closed
  · exact .inl (List.mem_append_right _
      ((queue.finishGroupSuccess_groupNotices node).symm ▸ noticed))

/-- An active failed closure completes every announced key it removes.
Witness: protected roots exclude collateral removal, and the failed root has its own
failure control. This permits latent descendants to be cancelled without announcing them.
-/
theorem RootClosureFrame.finishGroupFailure_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (node : GroupNode) (errors : Nat) (active : node.group.node.key ∈ queue.rootGroups)
    : GroupNoticeCompletion queue.rootGroups
        (
          (queue.finishGroupFailure node errors).1,
          [(queue.finishGroupFailure node errors).2]
        ) := by
  intro key member
  have old : key ∈ queue.rootGroups := by
    simpa [State.finishGroupFailure, rawGroupNoticeKeys] using member
  rcases frame.removeGroup_tracks_roots generated canonical active key old with kept | closed
  · exact .inl kept
  · exact .inr (by simpa [State.finishGroupFailure, rawGroupClosureKeys] using closed)

-----------------------------------------------------------------------------------------
-- The actual recursive drain preserves this stronger lifecycle tracking
-----------------------------------------------------------------------------------------

/-- Recursive draining cannot silently lose any earlier or internally announced group.
Witness: each real success activates its notices, each failure closes its only removed
announced root, and the preserved live-root frame supports the next internal step.
-/
theorem LiveRootFrame.drainReadyGroups_go_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
    (fuel : Nat)
    : GroupNoticeCompletion queue.rootGroups (State.drainReadyGroups.go fuel queue) := by
  induction fuel generalizing queue with
  | zero => exact .silent (List.Subset.refl _)
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact .silent (List.Subset.refl _)
      · rename_i node selected
        obtain ⟨key, active, choice⟩ := List.exists_of_findSome?_eq_some selected
        cases found : queue.groupNode? key with
        | none => simp [found] at choice
        | some candidate =>
            simp only [found] at choice
            change (if candidate.failure.isSome || candidate.pending == 0 then
              some candidate else none) = some node at choice
            split at choice
            · cases Option.some.inj choice
              have same := State.groupNode?_key found
              cases cached : node.failure with
              | none =>
                  exact (queue.finishGroupSuccess_groupNoticeCompletion node).append
                    (ih (frame.finishGroupSuccess generated canonical
                      (same ▸ found) (same ▸ active)))
              | some errors =>
                  exact (frame.rootClosureFrame.finishGroupFailure_groupNoticeCompletion
                    generated canonical node errors (same ▸ active)).append
                      (ih (frame.removeGroup node.group.node.key))
            · contradiction

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
