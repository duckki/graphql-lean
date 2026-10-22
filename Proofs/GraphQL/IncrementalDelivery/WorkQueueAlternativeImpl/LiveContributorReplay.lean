import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiveContributorStreamCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReferenceReplay

/-! Generated actual batches cover live contributors under early cached-failure visibility. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Cache exposure preserves permanent contributor paths and live-root coverage. -/
theorem State.LiveContributorsCovered.cacheTaskFailures {queue : State}
    (covered : queue.LiveContributorsCovered) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).LiveContributorsCovered := by
  intro task member key contributes live
  rw [State.cacheTaskFailures_tasks] at member
  have oldLive : ∃ node, queue.groupNode? key = some node := by
    simpa only [State.groupNode?, State.cacheTaskFailures_groupNodes] using live
  obtain ⟨root, active, path⟩ := covered task member key contributes oldLive
  exact ⟨
    root,
    by rwa [State.cacheTaskFailures_rootGroups],
    path.of_groupNodes_eq (queue := queue) (queue.cacheTaskFailures_groupNodes available)
  ⟩

/-- Pending internal controls leave live contributor paths unchanged. -/
theorem State.LiveContributorsCovered.withGroupFailures {queue : State}
    (covered : queue.LiveContributorsCovered)
    (groupFailureEvents : List GroupFailureEvent)
    : ({ queue with groupFailureEvents } : State).LiveContributorsCovered := by
  intro task member key contributes live
  obtain ⟨root, active, path⟩ := covered task member key contributes live
  exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩

private structure CoveredReplayFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent)
    : Prop where
  source : UncancelledReplayFrame queue work parents before
  covered : queue.LiveContributorsCovered

private theorem CoveredReplayFrame.coveredStep {queue work parents before}
    (frame : CoveredReplayFrame queue work parents before) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (_licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : (queue.handleGraphEvent event available).1.LiveContributorsCovered := by
  obtain ⟨_, matching, fresh⟩ := validGraphEvents_last valid
  let current := queue.cacheTaskFailures available
  have covered := frame.covered.cacheTaskFailures available
  have parent := frame.source.parent.cacheTaskFailures available
  have roots := frame.source.roots.cacheTaskFailures available
  have pending := frame.source.pending.cacheTaskFailures available
  have owners := frame.source.owners.cacheTaskFailures available
  have markers := frame.source.markers.cacheTaskFailures available
  have regions := frame.source.regions.cacheTaskFailures available
  have forest := State.RemovalForest.of_generated generated parent.children parent.links
    parent.records canonical
  cases event with
  | taskSuccess occurrence result =>
      exact covered.taskSuccess owners pending.matching generated parent.records roots.retired
        markers parent.safe parent.fields parent.complete parent.keys parent.live parent.tasks
        pending.started parent.closed parent.children parent.links parent.registration
        (frame.source.cancellations.cacheTaskFailures available) canonical
        (fun member => fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.groupSettlements_subsetIdentities before member)) matching available
  | taskFailure occurrence errors =>
      exact covered.taskFailure parent.keys forest parent.tasks occurrence errors
  | streamItems stream items =>
      exact covered.streamItems regions generated parent.complete parent.keys parent.live
        parent.tasks parent.closed parent.safe parent.fields parent.records parent.children
        parent.links parent.registration (frame.source.cancellations.cacheTaskFailures available) canonical matching fresh.1
        (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member)) available
  | streamSuccess stream =>
      change (current.streamSuccess stream).1.LiveContributorsCovered
      unfold State.streamSuccess
      split
      · intro task member key contributes live
        obtain ⟨root, active, path⟩ := covered task member key contributes live
        exact ⟨root, active, path.of_groupNodes_eq (queue := current) rfl⟩
      · exact covered
  | streamFailure stream errors =>
      change (current.streamFailure stream errors).1.LiveContributorsCovered
      unfold State.streamFailure
      split
      · intro task member key contributes live
        obtain ⟨root, active, path⟩ := covered task member key contributes live
        exact ⟨root, active, path.of_groupNodes_eq (queue := current) rfl⟩
      · exact covered

  | groupFailure notice =>
      change (current.groupFailure notice).1.LiveContributorsCovered
      unfold State.groupFailure
      split
      · exact covered
      · split
        · exact covered.withGroupFailures _
        · exact covered

/-- Source-derived topology and existing coverage survive one actual cached dispatch. -/
theorem UncancelledReplayFrame.liveContributorsCovered_handleGraphEvent
    {queue work parents before} (frame : UncancelledReplayFrame queue work parents before)
    (covered : queue.LiveContributorsCovered) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : (queue.handleGraphEvent event available).1.LiveContributorsCovered :=
  CoveredReplayFrame.coveredStep ⟨frame, covered⟩ generated canonical event valid
    available licensed

private theorem CoveredReplayFrame.handleGraphEvent {queue work parents before}
    (frame : CoveredReplayFrame queue work parents before) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    : CoveredReplayFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) := by
  exact ⟨frame.source.handleGraphEvent generated canonical event valid accepted available licensed,
    frame.coveredStep generated canonical event valid available licensed⟩

private theorem CoveredReplayFrame.replayGraphEvents {queue work parents before}
    (frame : CoveredReplayFrame queue work parents before) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (accepted : State.eventsStarted available queue events = true)
    : CoveredReplayFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  induction events generalizing queue before with
  | nil =>
      simpa only [List.append_nil, State.replayGraphEvents, List.foldl_nil] using frame
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have accepts : queue.acceptsGraphEvent event = true
          ∧ State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have handled := frame.handleGraphEvent generated canonical event (valid.prefix earlier)
        accepts.1 available licensed
      have next : CoveredReplayFrame (queue.dispatchGraphEvent event available).1 work parents
          (before ++ [event]) :=
        ⟨handled.source.withGroupFailures _, handled.covered.withGroupFailures _⟩
      have retained :=
        ih next (by simpa only [List.append_assoc, List.singleton_append] using valid)
          accepts.2
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using retained

private theorem CoveredReplayFrame.replayGraphEvents_admitted {queue work parents before}
    (frame : CoveredReplayFrame queue work parents before) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    : CoveredReplayFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  have sourceAt (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      UncancelledReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) := by
    obtain ⟨tail, joined⟩ := earlier
    apply frame.source.replayGraphEvents_admitted generated canonical fifo
      (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩) available licensed
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [joined] using accepted
  have loop (remaining fifo : List GraphEvent) (split : events = fifo ++ remaining)
      (covered : (queue.replayGraphEvents fifo available).LiveContributorsCovered)
      : (queue.replayGraphEvents events available).LiveContributorsCovered := by
    induction remaining generalizing fifo with
    | nil => simpa only [split, List.append_nil] using covered
    | cons event rest ih =>
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        have current : CoveredReplayFrame (queue.replayGraphEvents fifo available) work parents
            (before ++ fifo) := ⟨sourceAt fifo ⟨event :: rest, split.symm⟩, covered⟩
        have next : ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1.LiveContributorsCovered :=
          current.coveredStep generated canonical event (valid.prefix boundary)
            available licensed |>.withGroupFailures _
        exact ih (fifo ++ [event]) (by simp [split, List.append_assoc])
          (by simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil] using next)
  refine ⟨sourceAt events ⟨[], by simp⟩, ?_⟩
  exact loop events [] (by simp) (by simpa [State.replayGraphEvents] using frame.covered)

private theorem CoveredReplayFrame.withTerminated {queue work parents before}
    (frame : CoveredReplayFrame queue work parents before) (terminated : Bool)
    : CoveredReplayFrame { queue with terminated := terminated } work parents before := by
  refine ⟨frame.source.withTerminated terminated, ?_⟩
  intro task member key contributes live
  obtain ⟨root, active, path⟩ := frame.covered task member key contributes live
  exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩

private theorem CoveredReplayFrame.handleGraphEvents {queue work parents before}
    (frame : CoveredReplayFrame queue work parents before) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : CoveredReplayFrame (queue.handleGraphEvents events).1 work parents
        (before ++ events) := by
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures events →
        (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact valid.eachMatches (List.mem_append_right _ received)
  have replayed := frame.replayGraphEvents_admitted generated canonical events valid
    (GraphEvent.availableFailures events) licensed accepted
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact replayed.withTerminated terminal

/-- Eventwise empty-snapshot replay covers every live permanent contributor.
Witness: source accounting derives uncancelled owners and ancestor markers at each step;
the explicit empty-snapshot acceptance premise matches this eventwise proof language.
-/
theorem ExecutedWork.replayGraphEvents_liveContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).LiveContributorsCovered := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial : CoveredReplayFrame (State.initialize (Work.fromExecution work)) work parents [] :=
    ⟨initial_uncancelledReplayFrame generated canonical, generated.initial_liveContributorsCovered⟩
  exact (initial.replayGraphEvents (before := []) generated canonical events valid []
          (by intro occurrence errors impossible; cases impossible) started).covered

/-- Actual normalized host batches cover every surviving permanent contributor.
Witness: the source and coverage certificates follow each FIFO handler under its whole
batch snapshot; batch forwarding and termination change no contributor path.
-/
theorem ExecutedWork.runNormalized_liveContributorsCovered {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.LiveContributorsCovered := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have loop (remaining : List (List GraphEvent)) (queue : State) (before : List GraphEvent)
      (frame : CoveredReplayFrame queue work parents before)
      (valid : ValidGraphEvents work (before ++ remaining.flatten))
      (started : queue.batchesStarted remaining = true)
      : CoveredReplayFrame (queue.replayBatches remaining) work parents
          (before ++ remaining.flatten) := by
    induction remaining generalizing queue before with
    | nil =>
        simpa only [List.flatten_nil, List.append_nil, State.replayBatches,
          List.foldl_nil]
          using frame
    | cons batch rest ih =>
        obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
        have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
          ⟨rest.flatten, by simp [List.append_assoc]⟩
        have next := frame.handleGraphEvents generated canonical batch (valid.prefix earlier)
          running accepted
        have retained := ih _ _ next
          (by simpa only [List.flatten_cons, List.append_assoc] using valid) restStarted
        simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
          List.append_assoc]
          using retained
  have initial : CoveredReplayFrame (State.initialize (Work.fromExecution work)) work parents [] :=
    ⟨initial_uncancelledReplayFrame generated canonical, generated.initial_liveContributorsCovered⟩
  rw [State.runNormalized_replayBatches]
  exact (loop batches _ [] initial valid
          (by rwa [inputsStarted_eq_batchesStarted] at started)).covered

/-- Live contributor coverage at a FIFO prefix uses its complete host batch snapshot. -/
theorem ExecutedWork.batchPrefix_liveContributorsCovered {work inputs batch fifo tail}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (inputs.flatten ++ batch))
    (started : inputsStarted work (inputs ++ [batch]) = true)
    (partition : batch = fifo ++ tail)
    : let queue := (State.initialize (Work.fromExecution work)).replayBatches inputs
      (queue.replayGraphEvents fifo
        (GraphEvent.availableFailures batch)).LiveContributorsCovered := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayBatches inputs
  have recursive : initial.batchesStarted (inputs ++ [batch]) = true := by
    rwa [inputsStarted_eq_batchesStarted] at started
  rw [State.batchesStarted_append, Bool.and_eq_true] at recursive
  obtain ⟨running, accepted, _⟩ := queue.batchesStarted_cons batch [] recursive.2
  have priorValid := valid.prefix ⟨batch, rfl⟩
  have priorStarted : inputsStarted work inputs = true := by
    rw [inputsStarted_eq_batchesStarted]
    exact recursive.1
  have source := (initial_uncancelledReplayFrame generated canonical).runNormalized
    (before := []) generated canonical inputs priorValid recursive.1
  rw [State.runNormalized_replayBatches] at source
  have covered := generated.runNormalized_liveContributorsCovered inputs priorValid priorStarted
  rw [State.runNormalized_replayBatches] at covered
  have frame : CoveredReplayFrame queue work parents inputs.flatten := ⟨source, covered⟩
  have licensed (occurrence errors)
      (member : (occurrence, errors) ∈ GraphEvent.availableFailures batch)
      : (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact valid.eachMatches (List.mem_append_right _ received)
  exact (frame.replayGraphEvents_admitted generated canonical fifo
          (valid.prefix ⟨tail, by simp [partition, List.append_assoc]⟩)
          (GraphEvent.availableFailures batch) licensed
          (State.acceptsBatch_go_prefix (after := tail) (partition ▸ accepted))).covered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- Whole-replay live contributor coverage target, independent of acquired-resource inventory. -/
def GeneratedLiveContributorCoverage : Prop :=
  ∀ work inputs,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work inputs.flatten
    → ReferenceWorkQueue.inputsStarted work inputs = true
    → ((State.initialize work).runNormalized inputs).1.queue.LiveContributorsCovered

/-- Exact reference replay and terminal clearing discharge whole-replay contributor coverage. -/
theorem GeneratedLiveContributorCoverage_holds : GeneratedLiveContributorCoverage := by
  intro work inputs generated valid started
  rw [State.runNormalized_initialize work inputs generated valid started]
  simp only [State.fromReference]
  split
  · intro task member
    simp [State.clearRecords] at member
  · exact generated.runNormalized_liveContributorsCovered inputs valid started

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
