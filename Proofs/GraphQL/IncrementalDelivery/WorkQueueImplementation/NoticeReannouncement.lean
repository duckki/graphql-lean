import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawNoticeHistoryCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseHealth

/-! Permanent ancestor retirement prevents later group closures from reannouncing a child. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Earlier notices retain their ancestor certificates even after their own removal
-----------------------------------------------------------------------------------------

/-- Every initial or previously emitted group notice has permanently retired ancestors.
Witness: an indexed raw notice identifies its real source handler. That handler supplies
ancestor retirement, and every later input preserves it. Initial notices use generated
initialization. No active-root, cancellation, source-acceptance, or admission premise is used.
-/
theorem ExecutedWork.rawEventReplay_announcedAncestorsRetired
    {work : Execution.Work} (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : let initial := State.initialize (Work.fromExecution work)
      ∀ ref ∈
        initial.rootGroups
        ++ (initial.rawEventReplay events).2.flatMap rawGroupNoticeRefs,
        (initial.replayGraphEvents events).AncestorsRetired work ref := by
  intro initial ref announced
  rcases List.mem_append.mp announced with root | pending
  · exact (generated.initialRootAncestorsRetired ref root).mono
      (fun _ retired => retired.replayGraphEvents events)
  · obtain ⟨output, member, noticed⟩ := List.mem_flatMap.mp pending
    obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨before, event, after, position, same, carrier, _⟩ :=
      initial.rawEventReplay_output_prefix_at events selected
    have matched : event.MatchesWork work := by
      apply matching
      rw [same]
      exact List.mem_append_right _ List.mem_cons_self
    have prior : ∀ entry ∈ before, entry.MatchesWork work := by
      intro entry included
      apply matching
      rw [same]
      exact List.mem_append_left _ included
    have protectedRef := generated.replayGraphEvents_next_noticeAncestorsRetired prior matched
      ref (List.mem_flatMap.mpr ⟨output, List.mem_of_getElem? carrier, noticed⟩)
    have later := protectedRef.mono (fun _ retired => retired.replayGraphEvents after)
    simpa only [same, State.replayGraphEvents, List.foldl_append, List.foldl_cons,
      List.foldl_nil] using later

-----------------------------------------------------------------------------------------
-- A supported live closing ancestor cannot reach a previously protected child
-----------------------------------------------------------------------------------------

/-- A successful flush cannot release a child whose task-bearing ancestors already retired.
Witness: the actual release path makes the supported closing ref an ancestor or the child
itself. The first case contradicts its live lookup; the second contradicts its removal.
Taskless intermediate records are allowed, and the child need not still be an active root.
-/
theorem State.AncestorsRetired.not_released
    {queue : State} {work parents child}
    (protectedRef : queue.AncestorsRetired work child.ref)
    (generated : ExecutedWork work) (refs : queue.GroupRefsUnique)
    (records : queue.GroupNodesMatchWork work) (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (registered : queue.LiveGroupsRegistered)
    {group : GroupNode} (found : queue.groupNode? group.group.node.ref = some group)
    {occurrence owners} (task : TaskHasOwners work occurrence owners)
    (contributes : group.group.node.ref ∈ owners)
    : child ∉ (queue.finishGroupSuccess group).2.2.newGroups := by
  intro noticed
  have path := State.finishGroupSuccess_released_descendant found noticed
  have same := protectedRef.supported_path_eq generated records links canonical path
    task contributes
  have present := State.finishGroupSuccess_newGroupsPresent refs group child.ref
    (List.mem_map_of_mem noticed)
  have retired := queue.finishGroupSuccess_retires group
    (registered group (List.mem_of_find?_eq_some found))
  exact retired.2 (same ▸ present)

/-- A supported successful flush emits no previously protected group ref.
Witness: the output's notice list is precisely its release frontier; every descriptor
in that frontier contradicts the protected-child path theorem at the same queue boundary.
-/
theorem LiveRootFrame.finishGroupSuccess_noProtectedNotice
    {queue work parents ref} (frame : LiveRootFrame queue work parents)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {group : GroupNode} (found : queue.groupNode? group.group.node.ref = some group)
    (active : group.group.node.ref ∈ queue.rootGroups)
    (protectedRef : queue.AncestorsRetired work ref)
    : ref ∉ (queue.finishGroupSuccess group).2.1.flatMap rawGroupNoticeRefs := by
  intro member
  rw [← State.finishGroupSuccess_groupNotices] at member
  obtain ⟨child, noticed, sameRef⟩ := List.mem_map.mp member
  obtain ⟨dependencies, owner, producer, known, sameOwner⟩ := frame.support.roots _ active
  obtain ⟨occurrence, owners, payload, task, contributes⟩ := known.group_task
  exact (sameRef ▸ protectedRef).not_released generated frame.refs frame.records frame.links
    canonical frame.registered found ⟨producer, payload, task⟩
    (sameOwner ▸ contributes) noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
