import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootCompletion

/-! Task-success group completion retains immediate and queued startup channels. -/

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

private theorem notice_supported {work event ref}
    (known : WorkQueueEvent.GroupNoticesLocated work event)
    (noticed : ref ∈ rawGroupNoticeRefs event)
    : ∃ dependencies, NodeHasDependencies work ref .group dependencies := by
  have groups (nodes : List Execution.DeliveryNode)
      (located : ∀ node ∈ nodes,
        ∃ dependencies producer, NodeAt work node .group dependencies producer)
      (member : ref ∈ nodes.map Execution.DeliveryNode.ref)
      : ∃ dependencies, NodeHasDependencies work ref .group dependencies := by
    obtain ⟨node, member, same⟩ := List.mem_map.mp member
    obtain ⟨dependencies, producer, present⟩ := located node member
    exact ⟨dependencies, node, producer, present, same⟩
  cases event <;> simp only [rawGroupNoticeRefs] at noticed
  case groupSuccess group nodes streams => exact groups nodes known noticed
  case streamValues stream values nodes streams => exact groups nodes known noticed
  all_goals cases noticed

/-- Task success completes every removed announced root through its actual two channels.
Witness: the owner fold retires successful roots; protected release startup completes
failed children in queued notices. The ready drain preserves the same exact accounting.
-/
theorem LiveRootFrame.taskSuccess_groupNoticeCompletion
    {queue work parents occurrence result} (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : GroupNoticeCompletion queue.rootGroups
        (
          (queue.taskSuccess occurrence result available).1,
          (queue.taskSuccess occurrence result available).2.1
          ++ startupControls (queue.taskSuccess occurrence result available).2.2
        ) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found, startupControls, List.map_nil, List.append_nil]
      exact .silent (List.Subset.refl _)
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      let stored := queue.putTaskNode { node with value := some result.value }
      let current := (stored.maybeIntegrateWork result.work (some occurrence)).1
      have supplied := (context.children node.task
        (context.started node (State.taskNode?_some found).1)).sourceChild
          (State.taskNode?_some found).2 matching
      have registered := stored.maybeIntegrateWork_registration frame.registered frame.tasks
        result.work supplied.contributors (some occurrence)
      have owners : ∀ task ∈ result.work.tasks, ∀ group ∈ task.groups,
          ∃ dependencies, NodeHasDependencies work group.ref .group dependencies := by
        intro task member group contributes
        obtain ⟨address, payload, same, located⟩ := matching.childTask_producer member
        have known : TaskMatches work task :=
          ⟨⟨address, payload, some occurrence, same, located⟩,
            matching.childTask_groupsExact member⟩
        exact known.contributorKnown (List.mem_map_of_mem contributes)
      have storedSupport : stored.GroupRefSupport
          (fun ref => ∃ dependencies, NodeHasDependencies work ref .group dependencies) :=
        ⟨frame.support.contents, frame.support.roots⟩
      have storedFrame : LiveRootFrame stored work parents :=
        ⟨frame.refs, frame.records, frame.links, frame.registered, frame.tasks, frame.roots,
          storedSupport, frame.present⟩
      have storedRetired : stored.UncancelledRetiredAncestors work := retired
      have prepared : LiveRootFrame current work parents :=
        ⟨storedFrame.refs.maybeIntegrateWork _ _,
          storedFrame.records.maybeIntegrateWork _
            (fun _ member => matching.taskChildGroups_recordAt member) _,
          storedFrame.links.maybeIntegrateWork _
            (fun _ member => matching.taskChildGroups_parentCanonical canonical member) _,
          registered.1, registered.2.1,
          storedFrame.roots.mono
            (by rw [State.maybeIntegrateWork_rootGroups]; exact List.Subset.refl _)
            (fun _ before => before.maybeIntegrateWork result.work (some occurrence)),
          storedSupport.maybeIntegrateWork _ owners _,
          storedFrame.present.maybeIntegrateWork _ _⟩
      let folded := node.task.groups.foldl successGroupStep (current, [], {})
      have retirement := successGroupFold_uncancelledRetirement
        (storedRetired.maybeIntegrateWork result.work (some occurrence) generated frame.registered
          (by
            intro candidate member
            obtain ⟨dependencies, known⟩ := matching.taskChildGroups_recordAt member
            exact ⟨dependencies, known,
              (matching.taskChildGroups_parentCanonical canonical member).trans
                (congrArg List.head? (canonical _ _ known)).symm⟩)
          supplied.parentRefs) generated prepared.records
        prepared.links canonical prepared.registered prepared.tasks prepared.roots node.task.groups
      have metadata := State.successGroupFold_noticeMetadata generated prepared.refs
        prepared.records prepared.support node.task.groups
      have presence := successGroupFold_supported_rootsPresent generated prepared.refs
        prepared.records prepared.links canonical prepared.registered prepared.tasks prepared.roots
        prepared.support prepared.present node.task.groups
      have ancestry := successGroupFold_ancestorsRetired generated prepared.records
        prepared.links canonical prepared.registered prepared.tasks prepared.roots node.task.groups
      have foldedFrame : LiveRootFrame folded.1 work parents :=
        ⟨metadata.1, retirement.1, retirement.2.1, retirement.2.2.1, retirement.2.2.2.1,
          retirement.2.2.2.2.1, metadata.2.2, presence.1⟩
      have supported : ∀ child ∈ folded.2.2.newGroups,
          ∃ dependencies, NodeHasDependencies work child.ref .group dependencies := by
        intro child member
        have notices := (successGroupFold_groupNotices current node.task.groups).symm
        have located := State.successGroupFold_groupNoticesLocated generated prepared.refs
          prepared.records prepared.support node.task.groups
        have mentioned : child.ref ∈ folded.2.1.flatMap rawGroupNoticeRefs := by
          rw [notices]
          exact List.mem_map_of_mem member
        obtain ⟨event, emitted, noticed⟩ := List.mem_flatMap.mp mentioned
        exact notice_supported (located event emitted) noticed
      have started := foldedFrame.rootClosureFrame.startNewWork_groupNoticeCompletion
        foldedFrame.support generated canonical folded.2.2 ancestry.2 supported available
      have active := foldedFrame.startNewWork folded.2.2 ancestry.2
        (fun child member => (presence.2 child member).2.1) supported available
      have first : GroupNoticeCompletion queue.rootGroups
          ((folded.1.startNewWork folded.2.2 available).1,
            folded.2.1 ++ startupControls (folded.1.startNewWork folded.2.2 available).2) := by
        intro ref member
        have mentioned : ref ∈ queue.rootGroups ++ folded.2.1.flatMap rawGroupNoticeRefs := by
          simpa only [List.flatMap_append, startupControls_noticeRefs, List.append_nil]
            using member
        have activated (member : ref ∈ folded.1.rootGroups
            ++ folded.2.2.newGroups.map Execution.DeliveryNode.ref) :=
          (started ref (List.mem_append_left _ member)).imp_right
            (List.mem_append_right (folded.2.1.flatMap rawGroupClosureRefs))
        rw [List.flatMap_append]
        rcases List.mem_append.mp mentioned with old | noticed
        · have oldRoot : ref ∈ current.rootGroups := by
            simpa only [current, State.maybeIntegrateWork_rootGroups, stored,
              State.putTaskNode]
              using old
          rcases current.successGroupFold_tracks_roots node.task.groups ref oldRoot with
            kept | closed
          · exact activated (List.mem_append_left _ kept)
          · exact .inr (List.mem_append_left _ closed)
        · exact activated (List.mem_append_right _
            ((successGroupFold_groupNotices current node.task.groups).symm ▸ noticed))
      have later := active.drainReadyGroups_go_groupNoticeCompletion generated canonical
        (folded.1.startNewWork folded.2.2 available).1.groupNodes.length available
      have combined := first.append later
      apply combined.perm
      let startedWork := folded.1.startNewWork folded.2.2 available
      let drained := startedWork.1.drainReadyGroups available
      change (folded.2.1 ++ startupControls startedWork.2
          ++ (drained.2.1 ++ startupControls drained.2.2)).Perm
        ((folded.2.1 ++ drained.2.1) ++ startupControls (startedWork.2 ++ drained.2.2))
      simpa only [startupControls, List.map_append, List.append_assoc]
        using (List.perm_append_comm_assoc
                (startupControls (folded.1.startNewWork folded.2.2 available).2)
                (((folded.1.startNewWork folded.2.2 available).1.drainReadyGroups
                    available).2.1)
                (startupControls
                  ((folded.1.startNewWork folded.2.2 available).1.drainReadyGroups
                    available).2.2)).append_left
          folded.2.1

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
