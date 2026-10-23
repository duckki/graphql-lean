import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPreparedFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceNoticeAncestorRetirements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeUniqueness

/-! Actual cached handlers preserve notice separation and exclude earlier protected refs. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Uncancelled notice retirement also supplies permanent structural protection. -/
theorem State.NoticeAncestorRetirements.protected {queue work events}
    (retired : State.NoticeAncestorRetirements queue work events)
    : queue.GroupNoticeAncestorsRetired work events := by
  intro ref member record dependencies known same ancestor included occurrence owners task
  intro contributes
  exact (retired ref member record dependencies known same ancestor included occurrence owners
    task contributes).retired

/-- Task handling excludes any ref whose ancestors were already permanently retired. -/
theorem UncancelledReplayFrame.taskSuccess_noProtectedNotice
    {queue work parents before occurrence result ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat)) (protectedRef : queue.AncestorsRetired work ref)
    : ref
      ∉ (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1.flatMap
          rawGroupNoticeRefs := by
  let current := queue.cacheTaskFailures available
  have protectedCurrent := protectedRef.mono (fun _ retired => retired.cacheTaskFailures available)
  change ref ∉ (current.taskSuccess occurrence result available).2.1.flatMap rawGroupNoticeRefs
  cases found : current.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some incoming =>
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (folded.1.startNewWork folded.2.2 available).1
      have roots := (frame.taskSuccess_preparedFrames generated canonical occurrence result matching incoming
        available found).2
      have storedProtected : stored.AncestorsRetired work ref := protectedCurrent
      have protectedPrepared := storedProtected.mono (fun _ retired =>
        retired.maybeIntegrateWork result.work (some occurrence))
      have owner := roots.live.successGroupFold_noProtectedNotice generated canonical
        protectedPrepared incoming.task.groups
      have activeRoots := roots.successGroupFold_start generated canonical incoming.task.groups
        available
      have activeProtected := owner.2.1.mono (fun _ retired =>
        retired.startNewWork folded.2.2 available)
      have drain := activeRoots.live.drainReadyGroups_go_noProtectedNotice generated canonical
        activeProtected active.groupNodes.length available
      rw [current.taskSuccess_eq occurrence result incoming found available, List.flatMap_append,
        List.mem_append, not_or]
      exact ⟨owner.2.2, drain⟩

/-- Item handling excludes registered old notices with permanently retired ancestors. -/
theorem UncancelledReplayFrame.streamItems_noProtectedNotice
    {queue work parents before stream items ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat)) (registered : ref ∈ queue.registeredGroups)
    (protectedRef : queue.AncestorsRetired work ref)
    : ref
      ∉ (queue.handleGraphEvent (.streamItems stream items) available).2.1.flatMap
          rawGroupNoticeRefs := by
  let current := queue.cacheTaskFailures available
  have parent := frame.parent.cacheTaskFailures available
  have registeredCurrent : ref ∈ current.registeredGroups := by
    simpa only [current, State.cacheTaskFailures_registeredGroups] using registered
  have leading := current.streamItemFold_noRegisteredNotice parent.live parent.tasks parent.registration matching
    registeredCurrent available
  have protectedCurrent := protectedRef.mono (fun _ retired => retired.cacheTaskFailures available)
  have protectedPrepared := State.preparedStreamItems_preserves
    (fun current => current.AncestorsRetired work ref) protectedCurrent items available
    (fun _ item _ prior => prior.mono (fun _ retired =>
      ((retired.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available))
  have roots := (frame.streamItems_preparedFrames generated canonical matching available).2
  have drain := roots.live.drainReadyGroups_go_noProtectedNotice generated canonical
    protectedPrepared (current.preparedStreamItems items available).groupNodes.length available
  change ref ∉ (current.streamItems stream items available).2.1.flatMap rawGroupNoticeRefs
  rw [current.streamItems_eq stream items available]
  split
  · simp
  · rw [List.flatMap_cons, List.mem_append, not_or]
    exact ⟨leading, drain⟩

/-- Any actual handler excludes registered, structurally protected earlier notices. -/
theorem UncancelledReplayFrame.noProtectedNotice {queue work parents before event ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    (registered : ref ∈ queue.registeredGroups)
    (protectedRef : queue.AncestorsRetired work ref)
    : ref ∉ (queue.handleGraphEvent event available).2.1.flatMap rawGroupNoticeRefs := by
  cases event with
  | taskSuccess =>
      exact frame.taskSuccess_noProtectedNotice generated canonical matching available protectedRef
  | streamItems =>
      exact frame.streamItems_noProtectedNotice generated canonical matching available registered
        protectedRef
  | taskFailure => simp [State.handleGraphEvent, State.taskFailure_groupNoticeRefs]
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [rawGroupNoticeRefs]
  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp
      · split <;> simp [rawGroupNoticeRefs]

/-- Task owner output and its cached recursive drain have disjoint notice carriers. -/
theorem UncancelledReplayFrame.taskSuccess_noticeSeparation
    {queue work parents before occurrence result}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    : GroupNoticesSeparated
        (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1 := by
  let current := queue.cacheTaskFailures available
  change GroupNoticesSeparated (current.taskSuccess occurrence result available).2.1
  cases found : current.taskNode? occurrence with
  | none => simp [State.taskSuccess, found, GroupNoticesSeparated]
  | some incoming =>
      let prepared := ((current.putTaskNode
        { incoming with value := some result.value }).maybeIntegrateWork
        result.work (some occurrence)).1
      let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (folded.1.startNewWork folded.2.2 available).1
      have roots := (frame.taskSuccess_preparedFrames generated canonical occurrence result matching incoming
        available found).2
      have separated := roots.live.successGroupFold_noticeSeparation generated canonical
        incoming.task.groups
      have activeRoots := roots.successGroupFold_start generated canonical incoming.task.groups
        available
      rw [current.taskSuccess_eq occurrence result incoming found available]
      apply separated.2.2.append
        (activeRoots.live.drainReadyGroups_go_groupNoticesSeparated generated canonical _ available)
      intro ref noticed
      exact activeRoots.live.drainReadyGroups_go_noProtectedNotice generated canonical
        ((separated.2.1 ref noticed).mono (fun _ retired =>
          retired.startNewWork folded.2.2 available)) _ available

/-- Cached item preparation protects its leading frontier before the subsequent drain. -/
theorem UncancelledReplayFrame.streamItems_noticeSeparation
    {queue work parents before stream items}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : GroupNoticesSeparated
        (queue.handleGraphEvent (.streamItems stream items) available).2.1 := by
  let current := queue.cacheTaskFailures available
  let prepared := items.foldl (fun acc item => streamItemStep acc item available)
    (current, [], [], [], [])
  have matching := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  have roots := (frame.streamItems_preparedFrames generated canonical matching available).2
  have protection := (frame.streamItems_preparedNoticeAncestors generated canonical valid available
    licensed).protected
  change GroupNoticesSeparated (current.streamItems stream items available).2.1
  rw [current.streamItems_eq stream items available]
  split
  · simp [GroupNoticesSeparated]
  · apply (show GroupNoticesSeparated
      [.streamValues stream prepared.2.2.2.1 prepared.2.1 prepared.2.2.1]
        from by simp [GroupNoticesSeparated]).append
        (roots.live.drainReadyGroups_go_groupNoticesSeparated generated canonical _ available)
    intro ref noticed
    exact roots.live.drainReadyGroups_go_noProtectedNotice generated canonical
      (protection ref noticed) _ available

/-- Each actual cached handler has disjoint group-notice carriers. -/
theorem UncancelledReplayFrame.noticeSeparation {queue work parents before event}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : GroupNoticesSeparated (queue.handleGraphEvent event available).2.1 := by
  have matching := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  cases event with
  | taskSuccess =>
      exact frame.taskSuccess_noticeSeparation generated canonical matching available
  | streamItems =>
      exact frame.streamItems_noticeSeparation generated canonical valid available licensed
  | taskFailure => exact .of_noNotices (State.taskFailure_groupNoticeRefs _ _ _)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [GroupNoticesSeparated]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [GroupNoticesSeparated]
  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp [GroupNoticesSeparated]
      · split <;> simp [GroupNoticesSeparated]

/-- Every group list in an actual cached source output has unique refs. -/
theorem UncancelledReplayFrame.noticeLists_unique {queue work parents before event}
    (frame : UncancelledReplayFrame queue work parents before)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    : ∀ output ∈ (queue.handleGraphEvent event available).2.1,
        (rawGroupNoticeRefs output).Nodup := by
  let current := queue.cacheTaskFailures available
  have parent := frame.parent.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result =>
      exact current.taskSuccess_groupNoticesUnique parent.links parent.children occurrence result
        (fun _ member => matching.taskChildGroups_parentCanonical canonical member) available
  | streamItems stream items =>
      exact current.streamItems_groupNoticesUnique parent.keys parent.live parent.tasks parent.links
        parent.children parent.registration canonical matching available
  | taskFailure occurrence errors =>
      intro output member
      have empty := current.taskFailure_groupNoticeRefs occurrence errors
      have absent : rawGroupNoticeRefs output = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro ref noticed
        have impossible := List.mem_flatMap.mpr ⟨output, member, noticed⟩
        change ref ∈ (current.taskFailure occurrence errors).2.flatMap rawGroupNoticeRefs
          at impossible
        rw [empty] at impossible
        cases impossible
      rw [absent]
      exact List.nodup_nil
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [rawGroupNoticeRefs]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [rawGroupNoticeRefs]
  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp [rawGroupNoticeRefs]
      · split <;> simp [rawGroupNoticeRefs]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
