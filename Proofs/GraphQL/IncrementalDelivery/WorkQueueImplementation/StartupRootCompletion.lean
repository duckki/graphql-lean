import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootClosureFrames

/-! Protected startup removals retain exact announced-group completion accounting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open WorkQueueSemantics

private def startupControls (failures : List GroupFailureEvent) : List WorkQueueEvent :=
  failures.map (fun failure => .groupFailure failure.group failure.errors)

/-- The local completion projection is the returned failure notices with exact descriptors. -/
theorem startupControls_eq_failureEvents (failures : List GroupFailureEvent)
    : startupControls failures
      = failures.map
          (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors) :=
  rfl

private theorem GroupNoticeCompletion.of_sameRoots {initial queue next events}
    (tracked : GroupNoticeCompletion initial (queue, events))
    (same : next.rootGroups = queue.rootGroups)
    : GroupNoticeCompletion initial (next, events) := by
  intro ref member
  exact (tracked ref member).imp_left (fun active => same.symm ▸ active)

private theorem RootClosureFrame.startGroup_completion {queue work parents}
    (frame : RootClosureFrame queue work parents)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (ref : Nat) (available : List (Occurrence × Nat))
    : RootClosureFrame (queue.startGroup ref available).1 work parents
      ∧ (queue.startGroup ref available).1.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
      ∧ GroupNoticeCompletion queue.rootGroups
          (
            (queue.startGroup ref available).1,
            startupControls (queue.startGroup ref available).2
          ) := by
  have cached := frame.cacheTaskFailures available
  have cachedSupport := support.cacheTaskFailures available
  have tasks (more : List Occurrence) (current : State)
      (prior : RootClosureFrame current work parents)
      (supported : current.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
      : let final := more.foldl (fun current task => current.startTask task available) current
        RootClosureFrame final work parents
        ∧ final.GroupRefSupport
            (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
        ∧ final.rootGroups = current.rootGroups := by
    induction more generalizing current with
    | nil => exact ⟨prior, supported, rfl⟩
    | cons task rest ih =>
        have next : RootClosureFrame (current.startTask task available) work parents
            ∧ (current.startTask task available).GroupRefSupport
                (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies)
            ∧ (current.startTask task available).rootGroups = current.rootGroups := by
          unfold State.startTask
          split
          · exact ⟨prior, supported, rfl⟩
          · split <;> exact ⟨⟨prior.records, prior.links, prior.roots, prior.support⟩,
              ⟨supported.contents, supported.roots⟩, rfl⟩
        have later := ih _ next.1 next.2.1
        exact ⟨later.1, later.2.1, later.2.2.trans next.2.2⟩
  unfold State.startGroup
  dsimp only
  cases found : (queue.cacheTaskFailures available).groupNode? ref with
  | none =>
      refine ⟨cached, cachedSupport, .silent ?_⟩
      rw [State.cacheTaskFailures_rootGroups]
      exact List.Subset.refl _
  | some group =>
      dsimp only
      by_cases healthy :
        (group.tasks.filterMap
          (fun task =>
            ((queue.cacheTaskFailures available).taskNode? task).bind
              (·.rejection))).isEmpty
        = true
      · simp only [healthy, ite_true, startupControls, List.map_nil]
        have result := tasks group.tasks _ cached cachedSupport
        exact ⟨result.1, result.2.1, .silent (by
          rw [result.2.2, State.cacheTaskFailures_rootGroups]
          exact List.Subset.refl _)⟩
      · simp only [healthy, Bool.false_eq_true, ite_false, State.finishGroupFailure]
        have nonempty : group.tasks ≠ [] := by
          intro empty
          exact healthy (by simp only [empty, List.filterMap_nil, List.isEmpty_nil])
        have supported : ∃ dependencies,
            NodeHasDependencies work group.group.node.ref .group dependencies := by
          apply Classical.byContradiction
          intro absent
          exact nonempty (cachedSupport.contents group (List.mem_of_find?_eq_some found) absent)
        refine ⟨cached.removeGroup _, ⟨?_, ?_⟩, ?_⟩
        · intro node member contents
          exact cachedSupport.contents node (List.mem_filter.mp member).1 contents
        · intro key member
          exact cachedSupport.roots key ((queue.cacheTaskFailures available).removeGroup_rootsSubset
            group.group.node.ref member)
        · intro key member
          have old : key ∈ (queue.cacheTaskFailures available).rootGroups := by
            rw [State.cacheTaskFailures_rootGroups]
            simpa [startupControls, rawGroupNoticeRefs] using member
          rcases cached.removeGroup_tracks_roots_of_supported generated canonical supported key old
            with active | closed
          · exact .inl active
          · exact .inr (by simpa [startupControls, rawGroupClosureRefs] using closed)

/-- Newly announced protected roots stay active or acquire their own queued completion.
Supported root ancestry excludes collateral removal of a different announced group.
-/
theorem RootClosureFrame.startNewWork_groupNoticeCompletion {queue work parents}
    (frame : RootClosureFrame queue work parents)
    (support
      : queue.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (released : NewWork)
    (protectedRoots : ∀ child ∈ released.newGroups, queue.AncestorsRetired work child.ref)
    (supported
      : ∀ child ∈ released.newGroups,
          ∃ dependencies, NodeHasDependencies work child.ref .group dependencies)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeCompletion
        (queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref)
        (
          (queue.startNewWork released available).1,
          startupControls (queue.startNewWork released available).2
        ) := by
  let initialRefs := queue.rootGroups ++ released.newGroups.map Execution.DeliveryNode.ref
  let initial : State := { queue with rootGroups := initialRefs }
  have initialRoots : initial.RootAncestorsRetired work := by
    intro ref member
    rcases List.mem_append.mp member with old | fresh
    · exact frame.roots ref old
    · obtain ⟨child, member, same⟩ := List.mem_map.mp fresh
      exact same ▸ protectedRoots child member
  have initialSupport : initial.GroupRefSupport
      (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) := by
    refine ⟨support.contents, ?_⟩
    intro ref member
    rcases List.mem_append.mp member with old | fresh
    · exact support.roots ref old
    · obtain ⟨child, member, same⟩ := List.mem_map.mp fresh
      exact same ▸ supported child member
  have groups (more : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : RootClosureFrame acc.1 work parents)
      (supported : acc.1.GroupRefSupport
        (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies))
      (tracked : GroupNoticeCompletion initial.rootGroups (acc.1, startupControls acc.2))
      : let final := more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc
        GroupNoticeCompletion initial.rootGroups (final.1, startupControls final.2) := by
    induction more generalizing acc with
    | nil => exact tracked
    | cons ref rest ih =>
        obtain ⟨next, nextSupport, nextTracked⟩ :=
          prior.startGroup_completion supported generated canonical ref available
        exact ih _ next nextSupport
          (by
            simpa only [startupControls, List.map_append]
              using tracked.append nextTracked)
  have streams (more : NodeRefs) (current : State)
      : (more.foldl State.startStream current).rootGroups = current.rootGroups := by
    induction more generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        rw [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  have tracked := groups (released.newGroups.map Execution.DeliveryNode.ref) (initial, [])
    ⟨frame.records, frame.links, initialRoots, initialSupport.roots⟩ initialSupport
    (.silent (List.Subset.refl _))
  exact tracked.of_sameRoots (streams _ _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
