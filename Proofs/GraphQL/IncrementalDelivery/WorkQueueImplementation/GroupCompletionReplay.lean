import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRootCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Every announced group in actual generated replay stays active until its emitted closure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful handlers activate every notice before entering their final recursive drain
-----------------------------------------------------------------------------------------

/-- Actual task success tracks every old and newly announced root through its final drain.
Witness: the owner fold completes removed roots and accumulates exactly the pending notice
frontier; activation installs that frontier before the structurally protected drain.
-/
theorem ExecutedWork.taskSuccess_groupNoticeCompletion {work before occurrence result}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      GroupNoticeCompletion queue.rootGroups (queue.taskSuccess occurrence result) := by
  intro queue
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      exact .silent (List.Subset.refl _)
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found]
      split
      · exact .silent (List.Subset.refl _)
      · let prepared := ((queue.putTaskNode
          { incoming with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1
        let folded := incoming.task.groups.foldl successGroupStep (prepared, [], {})
        have roots : prepared.rootGroups = queue.rootGroups :=
          State.maybeIntegrateWork_rootGroups _ _ _
        have first : GroupNoticeCompletion queue.rootGroups
            (folded.1.startNewWork folded.2.2, folded.2.1) := by
          intro key member
          rw [(folded.1.startNewWork_groupCore _).2.2]
          rcases List.mem_append.mp member with old | noticed
          · rcases prepared.successGroupFold_tracks_roots incoming.task.groups key
                (roots.symm ▸ old) with active | closed
            · exact .inl (List.mem_append_left _ active)
            · exact .inr closed
          · exact .inl (List.mem_append_right _
              ((successGroupFold_groupNotices prepared incoming.task.groups).symm ▸ noticed))
        obtain ⟨parents, canonical, frame⟩ :=
          generated.taskSuccess_drain_liveRootFrame matching matched incoming
            (generated.replayGraphEvents_rootsPresent before matching)
        exact first.append (frame.drainReadyGroups_go_groupNoticeCompletion
          generated canonical _)

/-- An item handler's leading notices and its drain retain exact completion tracking.
Witness: item preparation appends its notice frontier to roots, then the independently
derived live-root frame prevents silent removal during the actual drain.
-/
theorem ExecutedWork.streamItems_groupNoticeCompletion {work before stream items}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      GroupNoticeCompletion queue.rootGroups (queue.streamItems stream items) := by
  intro queue
  rw [queue.streamItems_eq stream items]
  split
  · exact .silent (List.Subset.refl _)
  · let prepared := items.foldl streamItemStep (queue, [], [], [])
    have first : GroupNoticeCompletion queue.rootGroups
        (prepared.1, [.streamValues stream prepared.2.2.2 prepared.2.1 prepared.2.2.1]) := by
      intro key member
      exact .inl (by
        rw [queue.streamItemFold_rootGroups items]
        simpa only [List.flatMap_singleton, rawGroupNoticeKeys] using member)
    obtain ⟨parents, canonical, frame⟩ := generated.streamItems_prepared_liveRootFrame
      matching matched (generated.replayGraphEvents_rootsPresent before matching)
    exact first.append (frame.drainReadyGroups_go_groupNoticeCompletion generated canonical _)

-----------------------------------------------------------------------------------------
-- Every matching handler and complete raw replay preserve the same exact tracking
-----------------------------------------------------------------------------------------

/-- Every actual matching handler keeps announced groups active or emits their completion.
Witness: successful handlers activate notices before protected draining, failed tasks use
protected owner cleanup, and stream closures leave group roots alone.
-/
theorem ExecutedWork.handleGraphEvent_groupNoticeCompletion {work before event}
    (generated : ExecutedWork work) (matching : ∀ entry ∈ before, entry.MatchesWork work)
    (matched : event.MatchesWork work)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      GroupNoticeCompletion queue.rootGroups (queue.handleGraphEvent event) := by
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_groupNoticeCompletion matching matched
  | taskFailure occurrence errors =>
      obtain ⟨parents, canonical, frame⟩ := generated.replay_rootClosureFrame matching
      exact frame.taskFailure_groupNoticeCompletion generated canonical occurrence errors
  | streamItems stream items =>
      exact generated.streamItems_groupNoticeCompletion matching matched
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> intro key member <;> exact .inl (by simpa [rawGroupNoticeKeys] using member)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> intro key member <;> exact .inl (by simpa [rawGroupNoticeKeys] using member)

/-- Every initial or carried group notice remains active until an actual emitted completion.
Witness: concatenate the real source handlers and their protected-root tracking. This
holds for matching generated work without assuming accepted starts, source freshness, or
abstract scheduler admission; concrete cancellation is not a permitted silent endpoint.
-/
theorem ExecutedWork.rawEventReplay_groupNoticeCompletion {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : GroupNoticeCompletion (State.initialize (Work.fromExecution work)).rootGroups
        ((State.initialize (Work.fromExecution work)).rawEventReplay events) := by
  let initial := State.initialize (Work.fromExecution work)
  induction reversed : events.reverse generalizing events with
  | nil =>
      have empty : events = [] := by
        have same := congrArg List.reverse reversed
        simpa using same
      subst events
      exact .silent (List.Subset.refl _)
  | cons event rest ih =>
      have same : events = rest.reverse ++ [event] := by
        have same := congrArg List.reverse reversed
        simpa using same
      subst events
      let before := rest.reverse
      have prior : ∀ entry ∈ before, entry.MatchesWork work :=
        fun _ member => matching _ (List.mem_append_left _ member)
      have matched := matching event (List.mem_append_right before List.mem_cons_self)
      have earlier := ih before prior (by simp [before])
      have later := generated.handleGraphEvent_groupNoticeCompletion prior matched
      change GroupNoticeCompletion initial.rootGroups
        (initial.rawEventReplay (before ++ [event]))
      rw [State.rawEventReplay_append]
      dsimp only
      rw [State.rawEventReplay_state]
      exact earlier.append
        (by simpa only [State.rawEventReplay_state, initial] using later)

/-- Concrete termination completes every announced group, including failed groups.
Witness: exact replay tracking and empty final roots exclude the only noncompletion
alternative. Latent, unannounced node accounting remains a separate obligation.
-/
theorem ExecutedWork.terminalGroupCompleted {work inputs key}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ inputs.flatten, event.MatchesWork work)
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (announced
      : key
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawEventReplay
                inputs.flatten).2.flatMap
              rawGroupNoticeKeys)
    : key
      ∈ ((State.initialize (Work.fromExecution work)).rawEventReplay
          inputs.flatten).2.flatMap
          rawGroupClosureKeys := by
  have tracked := generated.rawEventReplay_groupNoticeCompletion inputs.flatten matching
    key announced
  have empty := (createWorkQueue_replayGraphEvents_terminalRoots started ended).1
  rw [State.rawEventReplay_state] at tracked
  exact tracked.resolve_left (by rw [empty]; simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
