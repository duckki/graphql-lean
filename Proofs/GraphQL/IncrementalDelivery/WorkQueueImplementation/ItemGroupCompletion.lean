import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskGroupCompletion

/-! Stream-item preparation completes failed announced groups through deferred startup notices. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def startupControls (failures : List GroupFailureEvent) : List WorkQueueEvent :=
  failures.map (fun failure => .groupFailure failure.group failure.errors)

private theorem startupControls_noticeRefs (failures : List GroupFailureEvent)
    : (startupControls failures).flatMap rawGroupNoticeRefs = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro event member
  obtain ⟨failure, _, rfl⟩ := List.mem_map.mp member
  rfl

private theorem LiveRootFrame.integrateStreamItem_completion
    {queue work parents stream items item} (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (member : item ∈ items) (available : List (Occurrence × Nat))
    : let integrated := queue.maybeIntegrateWork item.work
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      let started :=
        pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 } available
      LiveRootFrame started.1 work parents
      ∧ started.1.UncancelledRetiredAncestors work
      ∧ GroupNoticeCompletion
          (queue.rootGroups ++ pruned.2.map Execution.DeliveryNode.ref)
          (started.1, startupControls started.2) := by
  let integrated := queue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  let released : NewWork := { integrated.2 with newGroups := pruned.2 }
  have registered := queue.maybeIntegrateWork_registration frame.registered frame.tasks item.work
    (by
      intro task included ref contributes
      exact .inr (matching.streamItem_childTasksCovered generated.declarations member
        task included ref contributes))
  have owners : ∀ task ∈ item.work.tasks, ∀ group ∈ task.groups,
      ∃ dependencies, NodeHasDependencies work group.ref .group dependencies := by
    intro task candidate group contributes
    obtain ⟨address, payload, same, located⟩ :=
      matching.streamItem_childTask_producer member candidate
    have known : TaskMatches work task :=
      ⟨⟨address, payload, some item.occurrence, same, located⟩,
        matching.streamItem_childTask_groupsExact member candidate⟩
    exact known.contributorKnown (List.mem_map_of_mem contributes)
  have integratedFrame : LiveRootFrame integrated.1 work parents :=
    ⟨frame.refs.maybeIntegrateWork _ _,
      frame.records.maybeIntegrateWork _
        (fun _ candidate => matching.streamItem_childGroups_recordAt member candidate) _,
      frame.links.maybeIntegrateWork _
        (fun _ candidate => matching.streamItem_childGroups_parentCanonical canonical
          member candidate) _, registered.1, registered.2.1,
      frame.roots.mono
        (by rw [State.maybeIntegrateWork_rootGroups]; exact List.Subset.refl _)
        (fun _ before => before.maybeIntegrateWork item.work),
      frame.support.maybeIntegrateWork _ owners _, frame.present.maybeIntegrateWork _ _⟩
  have protectedRoots : ∀ child ∈ integrated.2.newGroups,
      integrated.1.AncestorsRetired work child.ref := by
    intro child included
    rw [State.maybeIntegrateWork_newGroups] at included
    obtain ⟨group, candidate, same, parentless, _⟩ :=
      queue.addGroups_newGroup_candidate item.work.groups included
    obtain ⟨dependencies, record⟩ := matching.streamItem_childGroups_recordAt member candidate
    have head := matching.streamItem_childGroups_parentCanonical canonical member candidate
    rw [parentless, ← canonical _ _ record] at head
    have empty : dependencies = [] := List.head?_eq_none_iff.mp head.symm
    rw [← same]
    exact .of_record generated record (by simp [empty])
  have prunedRoots := State.pruneEmptyGroups_ancestorsRetired generated integratedFrame.records
    integratedFrame.links canonical integratedFrame.registered integrated.2.newGroups protectedRoots
  have prunedRegistered := State.pruneEmptyGroups_registration integratedFrame.registered
    integratedFrame.tasks integrated.2.newGroups
  have supported := integratedFrame.support.pruneEmptyGroups integrated.2.newGroups
  have prunedFrame : LiveRootFrame pruned.1 work parents :=
    ⟨integratedFrame.refs.pruneEmptyGroups _, integratedFrame.records.pruneEmptyGroups _,
      integratedFrame.links.pruneEmptyGroups _, prunedRegistered.1, prunedRegistered.2.1,
      integratedFrame.roots.mono
        (by rw [State.pruneEmptyGroups_rootGroups]; exact List.Subset.refl _)
        (fun _ before => before.pruneEmptyGroups _), supported.1,
      frame.present.pruneIntegratedWork frame.registered item.work⟩
  have live : ∀ child ∈ released.newGroups,
      child.ref ∈ pruned.1.groupNodes.map (fun node => node.group.node.ref) := by
    intro child included
    exact integrated.1.pruneEmptyGroups_keptPresent integrated.2.newGroups integratedFrame.refs
      child.ref (List.mem_map_of_mem included)
  have retiredPruned := (retired.maybeIntegrateWork item.work none generated frame.registered
    (by
      intro candidate included
      obtain ⟨dependencies, known⟩ := matching.streamItem_childGroups_recordAt member included
      exact ⟨dependencies, known,
        (matching.streamItem_childGroups_parentCanonical canonical member included).trans
          (congrArg List.head? (canonical _ _ known)).symm⟩)
    (generated.declarations.sourceStreamItem matching member queue.registeredGroups).parentRefs
    ).pruneEmptyGroups generated
    integratedFrame.records integratedFrame.links canonical integratedFrame.registered
    integrated.2.newGroups protectedRoots
  have completion := prunedFrame.rootClosureFrame.startNewWork_groupNoticeCompletion
    supported.1 generated canonical released prunedRoots supported.2 available
  change GroupNoticeCompletion (pruned.1.rootGroups
      ++ released.newGroups.map Execution.DeliveryNode.ref)
    ((pruned.1.startNewWork released available).1,
      startupControls (pruned.1.startNewWork released available).2) at completion
  refine ⟨prunedFrame.startNewWork released prunedRoots live supported.2 available,
    retiredPruned.startNewWork released available, ?_⟩
  simpa only [released, pruned, integrated, State.pruneEmptyGroups_rootGroups,
    State.maybeIntegrateWork_rootGroups]
    using completion

private theorem LiveRootFrame.preparedStreamItems_completion
    {queue work parents stream items} (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : let final :=
        items.foldl (fun acc item => streamItemStep acc item available)
          (queue, [], [], [], [])
      LiveRootFrame final.1 work parents
      ∧ final.1.UncancelledRetiredAncestors work
      ∧ GroupNoticeCompletion
          (queue.rootGroups ++ final.2.1.map Execution.DeliveryNode.ref)
          (final.1, startupControls final.2.2.2.2) := by
  have loop (remaining : List StreamItem) (included : remaining.Subset items)
      (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
        × List Execution.StreamItemValue × List GroupFailureEvent)
      (current : LiveRootFrame acc.1 work parents)
      (closed : acc.1.UncancelledRetiredAncestors work)
      (tracked : GroupNoticeCompletion (queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.ref)
        (acc.1, startupControls acc.2.2.2.2))
      : let final := remaining.foldl (fun acc item => streamItemStep acc item available) acc
        LiveRootFrame final.1 work parents
        ∧ final.1.UncancelledRetiredAncestors work
        ∧ GroupNoticeCompletion (queue.rootGroups ++ final.2.1.map Execution.DeliveryNode.ref)
            (final.1, startupControls final.2.2.2.2) := by
    induction remaining generalizing acc with
    | nil => exact ⟨current, closed, tracked⟩
    | cons item rest ih =>
        let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        let started := pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 } available
        have next := current.integrateStreamItem_completion closed generated canonical matching
          (included List.mem_cons_self) available
        apply ih (fun _ member => included (List.mem_cons_of_mem _ member))
          (streamItemStep acc item available) next.1 next.2.1
        intro ref member
        have mentioned : ref ∈ (queue.rootGroups ++ acc.2.1.map Execution.DeliveryNode.ref)
            ++ pruned.2.map Execution.DeliveryNode.ref := by
          simpa only [streamItemStep, List.map_append, List.append_assoc,
            startupControls_noticeRefs, List.append_nil]
            using member
        have stepCompletion := next.2.2
        change GroupNoticeCompletion
          (acc.1.rootGroups ++ pruned.2.map Execution.DeliveryNode.ref)
          (started.1, startupControls started.2) at stepCompletion
        have activated (noticed : ref ∈ acc.1.rootGroups
            ++ pruned.2.map Execution.DeliveryNode.ref) :=
          (stepCompletion ref (List.mem_append_left _ noticed)).imp_right
            (List.mem_append_right
              ((startupControls acc.2.2.2.2).flatMap rawGroupClosureRefs))
        change ref ∈ started.1.rootGroups
          ∨ ref ∈ (startupControls (acc.2.2.2.2 ++ started.2)).flatMap rawGroupClosureRefs
        rw [startupControls, List.map_append, List.flatMap_append]
        rcases List.mem_append.mp mentioned with earlier | fresh
        · rcases tracked ref (List.mem_append_left _ earlier) with active | completed
          · exact activated (List.mem_append_left _ active)
          · exact .inr (List.mem_append_left _ completed)
        · exact activated (List.mem_append_right _ fresh)
  exact loop items (List.Subset.refl _) (queue, [], [], [], []) frame retired
    (.silent
      (by intro ref member; simpa only [List.map_nil, List.append_nil] using member))

/-- Stream-item notices retain exact completion through failed startup and ready release.
Pruned empty wrappers are unannounced. Each announced surviving group is either active or
has its own queued completion; forwarding those notices after immediate drain output
preserves the exact announced-group accounting.
-/
theorem LiveRootFrame.streamItems_groupNoticeCompletion {queue work parents stream items}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeCompletion queue.rootGroups
        (
          (queue.streamItems stream items available).1,
          (queue.streamItems stream items available).2.1
          ++ startupControls (queue.streamItems stream items available).2.2
        ) := by
  rw [queue.streamItems_eq stream items available]
  split
  · simp only [startupControls, List.map_nil, List.append_nil]
    exact .silent (List.Subset.refl _)
  · let final := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    have prepared := frame.preparedStreamItems_completion retired generated canonical matching
      available
    let leading := WorkQueueEvent.streamValues stream final.2.2.2.1 final.2.1 final.2.2.1
    have first : GroupNoticeCompletion queue.rootGroups
        (final.1, [leading] ++ startupControls final.2.2.2.2) := by
      intro ref member
      have mentioned : ref ∈ queue.rootGroups ++ final.2.1.map Execution.DeliveryNode.ref := by
        simpa only [List.flatMap_append, List.flatMap_singleton, leading,
          rawGroupNoticeRefs, startupControls_noticeRefs, List.append_nil]
          using member
      simpa only [List.flatMap_append, List.flatMap_singleton, leading,
        rawGroupClosureRefs, List.nil_append]
        using prepared.2.2 ref (List.mem_append_left _ mentioned)
    have later := prepared.1.drainReadyGroups_go_groupNoticeCompletion generated canonical
      final.1.groupNodes.length available
    have combined := first.append later
    apply combined.perm
    let drained := final.1.drainReadyGroups available
    change ([leading] ++ startupControls final.2.2.2.2
        ++ (drained.2.1 ++ startupControls drained.2.2)).Perm
      ((leading :: drained.2.1) ++ startupControls (final.2.2.2.2 ++ drained.2.2))
    simpa only [startupControls, List.map_append, List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append]
      using (List.perm_append_comm_assoc (startupControls final.2.2.2.2) drained.2.1
              (startupControls drained.2.2)).append_left
        [leading]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
