import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InternalGroupNoticeSeparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSourceFreshness

/-! Complete matching replay never repeats a group notice in a different carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Handler phases compose without reannouncing pending releases
-----------------------------------------------------------------------------------------

/-- Distinct carriers of a matching task-success handler have disjoint group notices.
Witness: the actual prepared owner fold has separated carriers and protects every pending
release before activation; the following drain cannot repeat any such protected key.
-/
theorem ExecutedWork.taskSuccess_groupNoticesSeparated
    {work before occurrence result} (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : GroupNoticesSeparated
        ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskSuccess
            occurrence result).2) := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  change GroupNoticesSeparated (queue.taskSuccess occurrence result).2
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found, GroupNoticesSeparated]
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found]
      split
      · simp [GroupNoticesSeparated]
      · let stored := queue.putTaskNode { incoming with value := some result.value }
        let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
        let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
        let active := folded.1.startNewWork folded.2.2
        obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
          generated.replayGraphEvents_preparedRetirement before matching matched incoming
        obtain ⟨keys, _, support⟩ :=
          generated.taskSuccess_prepared_noticeMetadata matching matched incoming
        have storedPresent : stored.RootGroupsPresent :=
          generated.replayGraphEvents_rootsPresent before matching
        have frame : LiveRootFrame prepared work parents :=
          ⟨keys, records, links, live, tasks, roots, support,
            storedPresent.maybeIntegrateWork result.work (some occurrence)⟩
        have separated := frame.successGroupFold_noticeSeparation generated canonical
          incoming.task.groups
        obtain ⟨activeParents, activeCanonical, activeFrame⟩ :=
          generated.taskSuccess_drain_liveRootFrame matching matched incoming
            (generated.replayGraphEvents_rootsPresent before matching)
        change GroupNoticesSeparated (folded.2.1 ++ active.drainReadyGroups.2)
        apply separated.2.2.append
          (activeFrame.drainReadyGroups_go_groupNoticesSeparated generated activeCanonical _)
        intro key noticed
        exact activeFrame.drainReadyGroups_go_noProtectedNotice generated activeCanonical
          ((separated.2.1 key noticed).mono (fun _ retired => retired.startNewWork _)) _

/-- An item handler's leading group notices cannot recur in its subsequent drain.
Witness: preparation protects every leading notice before its carrier is emitted; the
drain excludes all those keys and independently separates its own later carriers.
-/
theorem ExecutedWork.streamItems_groupNoticesSeparated
    {work before stream items} (generated : ExecutedWork work)
    (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    : GroupNoticesSeparated
        ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).streamItems
            stream items).2) := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  let prepared := items.foldl streamItemStep (queue, [], [], [])
  have protection := generated.streamItems_prepared_noticeAncestorsRetired matching matched
  obtain ⟨parents, canonical, frame⟩ := generated.streamItems_prepared_liveRootFrame
    matching matched (generated.replayGraphEvents_rootsPresent before matching)
  change GroupNoticesSeparated (queue.streamItems stream items).2
  rw [queue.streamItems_eq stream items]
  split
  · simp [GroupNoticesSeparated]
  · change GroupNoticesSeparated
      ([.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]
        ++ prepared.1.drainReadyGroups.2)
    apply (show GroupNoticesSeparated
      [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]
      from by simp [GroupNoticesSeparated]).append
        (frame.drainReadyGroups_go_groupNoticesSeparated generated canonical _)
    intro key noticed
    simp only [List.flatMap_singleton, rawGroupNoticeKeys] at noticed
    obtain ⟨child, included, same⟩ := List.mem_map.mp noticed
    exact frame.drainReadyGroups_go_noProtectedNotice generated canonical
      (same ▸ protection child included) _

/-- Every matching handler separates its group-notice carriers.
Witness: task/item successes compose their real phases; all other handlers have no notices.
-/
theorem ExecutedWork.handleGraphEvent_groupNoticesSeparated {work before event}
    (generated : ExecutedWork work) (matching : ∀ entry ∈ before, entry.MatchesWork work)
    (matched : event.MatchesWork work)
    : GroupNoticesSeparated
        ((((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
            event).2) := by
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_groupNoticesSeparated matching matched
  | streamItems stream items =>
      exact generated.streamItems_groupNoticesSeparated matching matched
  | taskFailure occurrence errors =>
      exact .of_noNotices (State.taskFailure_groupNoticeKeys _ _ _)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp [GroupNoticesSeparated]
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp [GroupNoticesSeparated]

-----------------------------------------------------------------------------------------
-- Raw replay is fresh against initialization and every earlier carrier
-----------------------------------------------------------------------------------------

/-- Raw matching replay separates carriers and never repeats an initial group notice.
Witness: append one real handler, using its internal separation and cross-input exclusion.
No accepted-source, scheduler-history, or per-carrier uniqueness premise is required.
-/
theorem ExecutedWork.rawEventReplay_groupNoticeSeparation
    {work : Execution.Work} (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : let initial := State.initialize (Work.fromExecution work)
      GroupNoticesSeparated (initial.rawEventReplay events).2
      ∧ ∀ key ∈ initial.rootGroups,
          key ∉ (initial.rawEventReplay events).2.flatMap rawGroupNoticeKeys := by
  let initial := State.initialize (Work.fromExecution work)
  induction reversed : events.reverse generalizing events with
  | nil =>
      have empty : events = [] := by
        have same := congrArg List.reverse reversed
        simpa using same
      subst events
      simp [State.rawEventReplay, GroupNoticesSeparated]
  | cons event rest ih =>
      have same : events = rest.reverse ++ [event] := by
        have same := congrArg List.reverse reversed
        simpa using same
      subst events
      let before := rest.reverse
      have prior : ∀ entry ∈ before, entry.MatchesWork work :=
        fun _ member => matching _ (List.mem_append_left _ member)
      have matched := matching event (List.mem_append_right before List.mem_cons_self)
      obtain ⟨separated, initialFresh⟩ := ih before prior (by simp [before])
      have later := generated.handleGraphEvent_groupNoticesSeparated prior matched
      have excludes {key} := generated.handleGraphEvent_noEarlierGroupNotice
        (key := key) prior matched
      change GroupNoticesSeparated (initial.rawEventReplay (before ++ [event])).2
        ∧ ∀ key ∈ initial.rootGroups,
          key ∉ (initial.rawEventReplay (before ++ [event])).2.flatMap rawGroupNoticeKeys
      rw [State.rawEventReplay_append]
      dsimp only
      rw [State.rawEventReplay_state]
      change GroupNoticesSeparated
        ((initial.rawEventReplay before).2
          ++ ((initial.replayGraphEvents before).handleGraphEvent event).2)
        ∧ ∀ key ∈ initial.rootGroups,
          key ∉ ((initial.rawEventReplay before).2
            ++ ((initial.replayGraphEvents before).handleGraphEvent event).2).flatMap
              rawGroupNoticeKeys
      refine ⟨separated.append later (fun key noticed => excludes
        (List.mem_append_right _ noticed)), ?_⟩
      intro key root
      rw [List.flatMap_append, List.mem_append, not_or]
      exact ⟨initialFresh key root, excludes (List.mem_append_left _ root)⟩

/-- A selected carrier excludes every group-notice key from its strict event prefix.
Witness: pairwise separation compares the selected event with each earlier event by index.
-/
theorem GroupNoticesSeparated.freshAt {events index event key}
    (separated : GroupNoticesSeparated events) (selected : events[index]? = some event)
    (noticed : key ∈ rawGroupNoticeKeys event)
    : key ∉ (events.take index).flatMap rawGroupNoticeKeys := by
  induction events generalizing index with
  | nil => simp
  | cons first rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          obtain ⟨different, later⟩ := List.pairwise_cons.mp separated
          simp only [List.getElem?_cons_succ] at selected
          intro repeated
          rw [List.take_succ_cons, List.flatMap_cons] at repeated
          rcases List.mem_append.mp repeated with earlier | earlier
          · exact different event (List.mem_of_getElem? selected) key earlier noticed
          · exact ih later selected earlier

/-- Every raw group notice is fresh against initialization and all earlier raw outputs.
Witness: complete replay's two separation components at the exact selected carrier.
This does not assume or assert that the selected carrier's own notice list is duplicate-free.
-/
theorem ExecutedWork.rawEventReplay_groupNoticeFresh
    {work events index event key} (generated : ExecutedWork work)
    (matching : ∀ entry ∈ events, entry.MatchesWork work)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay events).2[index]?
        = some event)
    (noticed : key ∈ rawGroupNoticeKeys event)
    : key
      ∉ (State.initialize (Work.fromExecution work)).rootGroups
        ++ (((State.initialize (Work.fromExecution work)).rawEventReplay events).2.take
              index).flatMap
            rawGroupNoticeKeys := by
  obtain ⟨separated, initialFresh⟩ := generated.rawEventReplay_groupNoticeSeparation events matching
  intro repeated
  rcases List.mem_append.mp repeated with root | earlier
  · exact initialFresh key root (List.mem_flatMap.mpr
      ⟨event, List.mem_of_getElem? selected, noticed⟩)
  · exact separated.freshAt selected noticed earlier

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
