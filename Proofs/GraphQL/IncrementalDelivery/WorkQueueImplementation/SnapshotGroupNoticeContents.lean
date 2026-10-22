import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetainedNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SnapshotMembershipBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPreparedFrames

/-! Actual successful carrier phases retain unpublished contents before cached child startup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A task notice retains its exact unpublished task contents under the actual batch snapshot. -/
theorem UncancelledReplayFrame.taskSuccess_groupNotice_unpublished
    {queue work parents before occurrence result published prior available inputs w cut
      index group groups streams child failed received}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (memberships
      : HandlerMembershipCut queue (.taskSuccess occurrence result) published prior
          available)
    (producers
      : TaskProducersSucceeded work (queue.cacheTaskFailures available).tasks received)
    (input : GraphEvent.taskSuccess occurrence result ∈ received)
    {sourceQueue : State}
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published sourceQueue)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (selected
      : (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    (count
      : ((w.events.take cut).flatMap normalizedObjectValues).length
        = (prior.flatMap WorkQueueEvent.objectValues).length
          + (((queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1.take
                index).flatMap
              WorkQueueEvent.objectValues).length)
    : RetainedNoticeContents work w.matching (w.events.take cut) failed received
        child := by
  let current := queue.cacheTaskFailures available
  have atHandler : (current.taskSuccess occurrence result available).2.1[index]?
      = some (.groupSuccess group groups streams) := selected
  change ((w.events.take cut).flatMap normalizedObjectValues).length
    = (prior.flatMap WorkQueueEvent.objectValues).length
      + (((current.taskSuccess occurrence result available).2.1.take index).flatMap
          WorkQueueEvent.objectValues).length at count
  cases found : current.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found, List.getElem?_nil, reduceCtorEq] at atHandler
  | some incoming =>
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := (released.1.startNewWork released.2.2 available).1
      obtain ⟨_, preparedRoots⟩ := frame.taskSuccess_preparedFrames generated canonical occurrence result
        matching incoming available found
      have storedSound : stored.GroupMembershipSound :=
        (frame.tasks.cacheTaskFailures available).sound
      have storedMatching : stored.RegisteredTasksMatch work :=
        (frame.tasks.cacheTaskFailures available).matching
      have preparedSound := storedSound.maybeIntegrateWork result.work (some occurrence)
      have preparedMatching := storedMatching.maybeIntegrateWork result.work (by
        intro task member
        obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
        exact ⟨⟨address, payload, some occurrence, same, known⟩,
          matching.childTask_groupsExact member⟩) (some occurrence)
      have preparedReady := producers.taskSuccess_prepared matching input incoming
      have output : (current.taskSuccess occurrence result available).2.1
          = released.2.1 ++ (active.drainReadyGroups available).2.1 := by
        rw [current.taskSuccess_eq occurrence result incoming found available]
      rw [output] at atHandler count
      by_cases inFold : index < released.2.1.length
      · rw [List.getElem?_append_left inFold] at atHandler
        obtain ⟨steps, bounded, exactPrefix, located, node, lookup, same, contents⟩ :=
          State.successGroupFold_noticeContents generated preparedRoots.live.refs
            preparedRoots.live.records preparedRoots.live.support incoming.task.groups
            atHandler noticed
        obtain ⟨sound, registered⟩ := State.successGroupFold_noticeTaskProvenance preparedSound
          preparedMatching (incoming.task.groups.take (steps + 1))
        refine ⟨located, _, node, lookup, same, contents, sound, registered,
          preparedReady.successGroupFold (incoming.task.groups.take (steps + 1)), ?_⟩
        apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready sound registered
          (List.mem_of_find?_eq_some lookup)
        have boundaryCount : (((incoming.task.groups.take (steps + 1)).foldl successGroupStep
            (prepared, [], {})).2.1.flatMap WorkQueueEvent.objectValues).length
            = ((released.2.1.take index).flatMap WorkQueueEvent.objectValues).length := by
          rw [← exactPrefix, List.take_add_one, atHandler]
          simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
            WorkQueueEvent.objectValues, List.append_nil]
          rfl
        dsimp only [prepared, stored, current] at boundaryCount
        rw [List.take_append_of_le_length (Nat.le_of_lt inFold)] at count
        intro publication member
        apply memberships.taskSuccess_foldMemberships found (steps + 1) (by omega)
          publication ?_ node (List.mem_of_find?_eq_some lookup)
        simpa only [count, boundaryCount] using member
      · have inDrain : released.2.1.length ≤ index := by omega
        rw [List.getElem?_append_right inDrain] at atHandler
        have roots := preparedRoots.successGroupFold_start generated canonical
          incoming.task.groups available
        obtain ⟨foldedSound, foldedMatching⟩ := State.successGroupFold_noticeTaskProvenance
          preparedSound preparedMatching incoming.task.groups
        have activeSound := foldedSound.startNewWork released.2.2 available
        have activeMatching := foldedMatching.startNewWork released.2.2 available
        obtain ⟨steps, closing, _, _, _, located, node, lookup, same, contents, excluded⟩ :=
          State.drainReadyGroups_go_noticeContents_excluding generated roots.live.refs
            roots.live.records roots.live.support active.groupNodes.length available
            (memberships.taskSuccess_drainStartupMemberships found) atHandler noticed
        obtain ⟨segmentSound, segmentMatching⟩ := State.drainReadyGroups_go_noticeTaskProvenance
          activeSound activeMatching steps available
        have sound := segmentSound.finishGroupSuccess closing
        have registered := segmentMatching.finishGroupSuccess closing
        refine ⟨located, _, node, lookup, same, contents, sound, registered,
          (((preparedReady.successGroupFold incoming.task.groups).startNewWork released.2.2
            available).drainReadyGroups_go steps available).finishGroupSuccess closing, ?_⟩
        apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready sound registered
          (List.mem_of_find?_eq_some lookup)
        rw [List.take_append, List.take_of_length_le inDrain] at count
        intro publication member
        apply excluded publication ?_
        simpa only [count, List.flatMap_append, List.length_append, Nat.add_assoc,
          State.drainReadyGroups, active, released, prepared, stored, current] using member

/-- Item-handler drain notices retain contents at their exact pre-startup flush boundary. -/
theorem UncancelledReplayFrame.streamItems_groupNotice_unpublished
    {queue work parents before stream items published prior available inputs w cut index
      group groups streams child failed received}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (memberships
      : HandlerMembershipCut queue (.streamItems stream items) published prior available)
    (producers
      : TaskProducersSucceeded work (queue.cacheTaskFailures available).tasks received)
    (input : GraphEvent.streamItems stream items ∈ received)
    {sourceQueue : State}
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published sourceQueue)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (selected
      : (queue.handleGraphEvent (.streamItems stream items) available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    (count
      : ((w.events.take cut).flatMap normalizedObjectValues).length
        = (prior.flatMap WorkQueueEvent.objectValues).length
          + (((queue.handleGraphEvent (.streamItems stream items) available).2.1.take
                index).flatMap
              WorkQueueEvent.objectValues).length)
    : RetainedNoticeContents work w.matching (w.events.take cut) failed received
        child := by
  let current := queue.cacheTaskFailures available
  let prepared := current.preparedStreamItems items available
  have atHandler : (current.streamItems stream items available).2.1[index]?
      = some (.groupSuccess group groups streams) := selected
  change ((w.events.take cut).flatMap normalizedObjectValues).length
    = (prior.flatMap WorkQueueEvent.objectValues).length
      + (((current.streamItems stream items available).2.1.take index).flatMap
          WorkQueueEvent.objectValues).length at count
  obtain ⟨_, roots⟩ := frame.streamItems_preparedFrames generated canonical matching available
  have parent := frame.parent.cacheTaskFailures available
  have originalRoots := frame.roots.cacheTaskFailures available
  have preparedTasks := (frame.tasks.cacheTaskFailures available).prepareItems_of_registered
    parent.live parent.tasks originalRoots.live.present generated.declarations matching available
  have preparedReady := producers.preparedStreamItems matching input items (List.Subset.refl _)
    available
  rw [current.streamItems_eq stream items available] at atHandler count
  cases active : current.rootStreams.contains stream.ref with
  | false =>
      simp only [active, Bool.not_false, ↓reduceIte, List.getElem?_nil, reduceCtorEq] at atHandler
  | true =>
      simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at atHandler count
      cases index with
      | zero => cases atHandler
      | succ index =>
          obtain ⟨steps, closing, _, _, _, located, node, lookup, same, contents, excluded⟩ :=
            State.drainReadyGroups_go_noticeContents_excluding generated roots.live.refs
              roots.live.records roots.live.support prepared.groupNodes.length available
              (memberships.streamItems_drainStartupMemberships active) atHandler noticed
          obtain ⟨segmentSound, segmentMatching⟩ := State.drainReadyGroups_go_noticeTaskProvenance
            preparedTasks.sound preparedTasks.matching steps available
          have sound := segmentSound.finishGroupSuccess closing
          have registered := segmentMatching.finishGroupSuccess closing
          refine ⟨located, _, node, lookup, same, contents, sound, registered,
            (preparedReady.drainReadyGroups_go steps available).finishGroupSuccess closing, ?_⟩
          apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready sound
            registered
            (List.mem_of_find?_eq_some lookup)
          simp only [List.take_succ_cons, List.flatMap_cons, WorkQueueEvent.objectValues,
            List.nil_append] at count
          intro publication member
          apply excluded publication ?_
          simpa only [count, List.flatMap_append, List.length_append, State.drainReadyGroups,
            State.preparedStreamItems, prepared, current] using member

/-- Every actual successful group carrier has concrete unpublished contents before child startup. -/
theorem UncancelledReplayFrame.groupNotice_unpublished
    {queue work parents before event published prior available inputs w cut index
      group groups streams child failed received}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : event.MatchesWork work)
    (memberships : HandlerMembershipCut queue event published prior available)
    (producers
      : TaskProducersSucceeded work (queue.cacheTaskFailures available).tasks received)
    (input : event ∈ received)
    {sourceQueue : State}
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published sourceQueue)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (selected
      : (queue.handleGraphEvent event available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    (count
      : ((w.events.take cut).flatMap normalizedObjectValues).length
        = (prior.flatMap WorkQueueEvent.objectValues).length
          + (((queue.handleGraphEvent event available).2.1.take index).flatMap
              WorkQueueEvent.objectValues).length)
    : RetainedNoticeContents work w.matching (w.events.take cut) failed received
        child := by
  cases event with
  | taskSuccess occurrence result =>
      exact frame.taskSuccess_groupNotice_unpublished generated canonical matching memberships
        producers input ledger objects ready selected noticed count
  | streamItems stream items =>
      exact frame.streamItems_groupNotice_unpublished generated canonical matching memberships
        producers input ledger objects ready selected noticed count
  | taskFailure occurrence errors =>
      exact False.elim ((queue.cacheTaskFailures available).taskFailure_noGroupSuccess
        occurrence errors group groups streams (List.mem_of_getElem? selected))
  | streamSuccess stream =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member
  | groupFailure notice =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · cases member
      · split at member <;> simp at member

/-- A leading item notice retains its exact pruning contents before any object output. -/
theorem UncancelledReplayFrame.streamItems_leadingNotice_contents
    {queue work parents before stream items published prior available inputs w cut child
      failed received}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (memberships
      : HandlerMembershipCut queue (.streamItems stream items) published prior available)
    (producers
      : TaskProducersSucceeded work (queue.cacheTaskFailures available).tasks received)
    (input : GraphEvent.streamItems stream items ∈ received)
    {sourceQueue : State}
    (ledger : ObjectLedgerMatching work inputs w.events w.matching published sourceQueue)
    (objects : ConformancePlan.GroupPublicationAdmission work w)
    (ready : ConformancePlan.StreamPublicationReady work w)
    (noticed
      : child
        ∈ (items.foldl (fun acc item => streamItemStep acc item available)
            (queue.cacheTaskFailures available, [], [], [], [])).2.1)
    (count
      : ((w.events.take cut).flatMap normalizedObjectValues).length
        = (prior.flatMap WorkQueueEvent.objectValues).length)
    : RetainedNoticeContents work w.matching (w.events.take cut) failed received
        child := by
  let current := queue.cacheTaskFailures available
  obtain ⟨earlier, item, later, splitItems, introduced⟩ :=
    current.streamItemFold_noticeOrigin items available noticed
  have included : earlier.Subset items := by
    rw [splitItems]
    exact List.subset_append_left _ _
  have itemMember : item ∈ items := by simp [splitItems]
  have partialMatching : (GraphEvent.streamItems stream earlier).MatchesWork work :=
    fun next member => matching next (included member)
  let prefixQueue := current.preparedStreamItems earlier available
  let integrated := prefixQueue.maybeIntegrateWork item.work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have roots := (frame.streamItems_preparedFrames generated canonical partialMatching available).2
  obtain ⟨located, node, found, same, contents⟩ := State.integrateStreamItem_noticeContents
    generated roots.live.refs roots.live.records roots.live.support matching itemMember introduced
  have parent := frame.parent.cacheTaskFailures available
  have originalRoots := frame.roots.cacheTaskFailures available
  have prefixTasks := (frame.tasks.cacheTaskFailures available).prepareItems_of_registered
    parent.live parent.tasks originalRoots.live.present generated.declarations partialMatching available
  have sound := (prefixTasks.sound.maybeIntegrateWork item.work).pruneEmptyGroups
    integrated.2.newGroups
  have integratedMatching := prefixTasks.matching.maybeIntegrateWork item.work (by
    intro task member
    obtain ⟨address, payload, identity, known⟩ :=
      matching.streamItem_childTask_producer itemMember member
    exact ⟨⟨address, payload, some item.occurrence, identity, known⟩,
      matching.streamItem_childTask_groupsExact itemMember member⟩)
  have registered := integratedMatching.pruneEmptyGroups integrated.2.newGroups
  have prefixReady := producers.preparedStreamItems matching input earlier included available
  have afterReady := prefixReady.integrateStreamItem matching input itemMember available
  have boundaryReady : TaskProducersSucceeded work pruned.1.tasks received := by
    rw [State.pruneEmptyGroups_tasks, State.maybeIntegrateWork_tasks_append]
    rw [State.integrateStreamItem_tasks _ _ available] at afterReady
    exact afterReady
  refine ⟨located, _, node, found, same, contents, sound, registered, boundaryReady, ?_⟩
  apply ConformancePlan.retainedGroupMembers_unpublished ledger objects ready sound
    registered (List.mem_of_find?_eq_some found)
  intro publication member
  rw [count] at member
  obtain ⟨absent, fresh⟩ := memberships.before publication member
  have prefixAbsent := absent.preparedStreamItems earlier (by
    intro entry listed task member
    exact fresh task (List.mem_flatMap.mpr ⟨entry, included listed, member⟩)) available
  have integratedAbsent := prefixAbsent.maybeIntegrateWork item.work (by
    intro task member
    exact fresh task (List.mem_flatMap.mpr ⟨item, itemMember, member⟩))
  exact (integratedAbsent.pruneEmptyGroups integrated.2.newGroups) node
    (List.mem_of_find?_eq_some found)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
