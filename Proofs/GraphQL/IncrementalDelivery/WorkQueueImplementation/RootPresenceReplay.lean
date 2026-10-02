import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveRootPresence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FreshGroupPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Live active roots through every matching generated source-event prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Notice-producing handlers preserve live roots across every internal phase
-----------------------------------------------------------------------------------------

/-- The actual task-success drain starts with a complete live-root frame.
Witness: generated replay supplies structural facts; preparation preserves old roots,
the single-pass fold protects pending releases, and activation retains their live records.
-/
theorem ExecutedWork.taskSuccess_drain_liveRootFrame {work before occurrence result}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (incoming : TaskNode)
    (present
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RootGroupsPresent)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      let prepared :=
        ((queue.putTaskNode
            { incoming with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let active := released.1.startNewWork released.2.2
      ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
        ∧ LiveRootFrame active work parents := by
  intro queue prepared released active
  obtain ⟨parents, canonical, records, links, live, tasks, roots, retired⟩ :=
    generated.replayGraphEvents_preparedRetirement before matching matched incoming
  obtain ⟨keys, _, support⟩ :=
    generated.taskSuccess_prepared_noticeMetadata matching matched incoming
  have storedPresent :
      (queue.putTaskNode { incoming with value := some result.value }).RootGroupsPresent := present
  have preparedPresent := storedPresent.maybeIntegrateWork result.work (some occurrence)
  have presence := successGroupFold_supported_rootsPresent generated keys records links
    canonical live tasks roots support preparedPresent incoming.task.groups
  have folded := successGroupFold_uncancelledRetirement retired generated records links
    canonical live tasks roots incoming.task.groups
  have ancestry := successGroupFold_ancestorsRetired generated records links canonical
    live tasks roots incoming.task.groups
  have coverage := State.startNewWork_registration folded.2.2.1 folded.2.2.2.1 released.2.2
  obtain ⟨activeKeys, activeRecords, activeSupport⟩ :=
    generated.taskSuccess_drain_noticeMetadata matching matched incoming
  refine ⟨parents, canonical,
    ⟨activeKeys, activeRecords, folded.2.1.startNewWork _, coverage.1, coverage.2,
      folded.2.2.2.2.1.startNewWork _ ancestry.2, activeSupport, ?_⟩⟩
  exact presence.1.startNewWork _
    (by
      intro key member
      obtain ⟨node, included, same⟩ := List.mem_map.mp member
      exact same ▸ (presence.2 node included).2.1)

/-- Matching task success preserves live active roots, including ignored late settlements.
Witness: absent tasks do nothing, rejected tasks only lose memberships, and accepted tasks
use the independently certified preparation/owner/activation frame before recursive draining.
-/
theorem ExecutedWork.taskSuccess_rootsPresent {work before occurrence result}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (present
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RootGroupsPresent)
    : ((((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).taskSuccess
          occurrence result).1).RootGroupsPresent := by
  let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
  change (queue.taskSuccess occurrence result).1.RootGroupsPresent
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using present
  | some incoming =>
      rw [queue.taskSuccess_eq occurrence result incoming found]
      split
      · simpa only [State.RootGroupsPresent, State.removeTask, List.map_map,
          Function.comp_def]
          using present
      · obtain ⟨parents, canonical, frame⟩ :=
          generated.taskSuccess_drain_liveRootFrame matching matched incoming present
        exact (frame.drainReadyGroups generated canonical).present

/-- The leading item carrier and subsequent drain share a complete live-root frame.
Witness: matching replay supplies metadata, and fresh-path pruning preserves old roots
through every item while activating only live released children.
-/
theorem ExecutedWork.streamItems_prepared_liveRootFrame {work before stream items}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (present
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RootGroupsPresent)
    : ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.key)
        ∧ LiveRootFrame
            (((State.initialize (Work.fromExecution work)).replayGraphEvents
                before).preparedStreamItems
              items) work parents := by
  obtain ⟨parents, canonical, records, links, live, tasks, roots, _⟩ :=
    generated.replayGraphEvents_streamPreparedRetirement before matching matched
  obtain ⟨keys, _, support⟩ := generated.streamItems_prepared_noticeMetadata matching matched
  obtain ⟨priorKeys, _, _⟩ := generated.replay_noticeMetadata matching
  have registration := createWorkQueue_registration work
  have prior := State.replayGraphEvents_registration registration.1 registration.2 before matching
  exact ⟨parents, canonical, ⟨keys, records, links, live, tasks, roots, support,
    present.preparedStreamItems priorKeys prior.1 prior.2.1 matched⟩⟩

/-- Matching stream items preserve live active roots through preparation and draining.
Witness: inactive streams do nothing; accepted batches use the actual prepared frame.
-/
theorem ExecutedWork.streamItems_rootsPresent {work before stream items}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    (matched : (GraphEvent.streamItems stream items).MatchesWork work)
    (present
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RootGroupsPresent)
    : ((((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).streamItems
          stream items).1).RootGroupsPresent := by
  rw [State.streamItems_eq]
  split
  · exact present
  · obtain ⟨parents, canonical, frame⟩ :=
      generated.streamItems_prepared_liveRootFrame matching matched present
    exact (frame.drainReadyGroups generated canonical).present

-----------------------------------------------------------------------------------------
-- Source-prefix composition uses only matching, not accepted or admissible output histories
-----------------------------------------------------------------------------------------

/-- One matching input preserves root presence after every matching generated prefix.
Witness: the two notice-producing handlers use phase-aware presence; failure cleanup
preserves surviving roots, and stream finalization does not change group records.
-/
theorem ExecutedWork.next_rootsPresent {work before event}
    (generated : ExecutedWork work) (matching : ∀ past ∈ before, past.MatchesWork work)
    (matched : event.MatchesWork work)
    (present
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RootGroupsPresent)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        (before ++ [event])).RootGroupsPresent := by
  rw [State.replayGraphEvents_append]
  cases event with
  | taskSuccess occurrence result =>
      exact generated.taskSuccess_rootsPresent matching matched present
  | taskFailure occurrence errors => exact present.taskFailure occurrence errors
  | streamItems stream items =>
      exact generated.streamItems_rootsPresent matching matched present
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact present
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact present

/-- Every matching generated source prefix has a live record for each active group root.
Witness: start with actual pruning-based initialization and append matching inputs using
the checked handler theorem. No batching, source acceptance, or notice admission is assumed.
-/
theorem ExecutedWork.replayGraphEvents_rootsPresent {work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).RootGroupsPresent := by
  have loop (remaining : List GraphEvent) (before : List GraphEvent)
      (prior : ∀ event ∈ before, event.MatchesWork work)
      (later : ∀ event ∈ remaining, event.MatchesWork work)
      (present : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).RootGroupsPresent)
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          (before ++ remaining)).RootGroupsPresent := by
    induction remaining generalizing before with
    | nil => simpa only [List.append_nil] using present
    | cons event rest ih =>
        have next := generated.next_rootsPresent prior (later event List.mem_cons_self) present
        have extended : ∀ source ∈ before ++ [event], source.MatchesWork work := by
          intro source member
          rcases List.mem_append.mp member with earlier | added
          · exact prior source earlier
          · obtain rfl := List.mem_singleton.mp added
            exact later source List.mem_cons_self
        simpa only [List.append_assoc, List.singleton_append]
          using ih (before ++ [event]) extended
            (fun source member => later source (List.mem_cons_of_mem _ member)) next
  exact loop events [] (by simp) matching (createWorkQueue_rootGroupsPresent _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
