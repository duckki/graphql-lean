import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SnapshotNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Initialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchOutputReplay

/-! Permanent notice protection and uniqueness compose through actual cached host batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Proof evidence for the complete ordered inventory of already announced group refs. -/
structure NoticeHistoryFrame (queue : State) (work : Execution.Work) (refs : NodeRefs)
    : Prop where
  unique : refs.Nodup
  registered : refs.Subset queue.registeredGroups
  ancestry : ∀ ref ∈ refs, queue.AncestorsRetired work ref

/-- Pending internal notices change no accumulated announcement evidence. -/
theorem NoticeHistoryFrame.withGroupFailures {queue work refs}
    (history : NoticeHistoryFrame queue work refs)
    (groupFailureEvents : List GroupFailureEvent)
    : NoticeHistoryFrame { queue with groupFailureEvents } work refs :=
  ⟨history.unique, history.registered, history.ancestry⟩

/-- A valid FIFO input extends the same notice inventory without repetition. -/
theorem NoticeHistoryFrame.handleGraphEvent {queue work parents before refs event}
    (history : NoticeHistoryFrame queue work refs)
    (source : UncancelledReplayFrame queue work parents before)
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
    : NoticeHistoryFrame (queue.handleGraphEvent event available).1 work
        (refs
          ++ (queue.handleGraphEvent event available).2.1.flatMap
              rawGroupNoticeRefs) := by
  have matching := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
  have registration := queue.handleGraphEvent_registration source.parent.live source.parent.tasks
    event matching source.parent.registration available
  have noticed := queue.handleGraphEvent_groupNoticesRegistered source.parent.keys
    source.parent.live
    source.parent.tasks source.parent.registration event matching available
  have protection := (source.noticeAncestorRetirements generated canonical event valid available
    licensed).protected
  refine ⟨List.nodup_append.mpr ⟨history.unique, ?_, ?_⟩, ?_, ?_⟩
  · apply List.pairwise_flatMap.mpr
    refine ⟨source.noticeLists_unique canonical matching available, ?_⟩
    apply (source.noticeSeparation generated canonical valid available licensed).imp
    intro first later distinct ref member other included same
    subst other
    exact distinct ref member included
  · intro ref prior other member same
    subst other
    exact source.noProtectedNotice generated canonical matching available (history.registered prior)
      (history.ancestry ref prior) member
  · intro ref member
    rcases List.mem_append.mp member with old | fresh
    · exact registration.2.2 (history.registered old)
    · obtain ⟨output, emitted, included⟩ := List.mem_flatMap.mp fresh
      exact (noticed output emitted).ref included
  · intro ref member
    rcases List.mem_append.mp member with old | fresh
    · exact (history.ancestry ref old).mono (fun _ retired =>
        retired.handleGraphEvent event available)
    · exact protection ref fresh

/-- Fixed-snapshot FIFO replay retains the complete accumulated notice inventory. -/
theorem NoticeHistoryFrame.rawEventReplay {queue work parents before refs}
    (history : NoticeHistoryFrame queue work refs)
    (source : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
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
    : NoticeHistoryFrame (queue.replayGraphEvents events available) work
        (refs
          ++ (queue.rawEventReplay events available).2.flatMap rawGroupNoticeRefs) := by
  induction events generalizing queue before refs with
  | nil => simpa only [State.rawEventReplay, State.replayGraphEvents, List.foldl_nil,
      List.flatMap_nil, List.append_nil] using history
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp [List.append_assoc]⟩
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have firstValid := valid.prefix earlier
      have next : NoticeHistoryFrame (queue.dispatchGraphEvent event available).1 work
          (refs ++ (queue.dispatchGraphEvent event available).2.flatMap rawGroupNoticeRefs) :=
        history.handleGraphEvent source generated canonical firstValid available licensed |>.withGroupFailures _
      have nextSource : UncancelledReplayFrame (queue.dispatchGraphEvent event available).1 work parents
          (before ++ [event]) :=
        source.handleGraphEvent generated canonical event firstValid accepts.1 available licensed |>.withGroupFailures _
      have retained := ih next nextSource
        (by simpa only [List.append_assoc, List.singleton_append] using valid) accepts.2
      simpa only [State.rawEventReplay_cons, State.replayGraphEvents, List.foldl_cons,
        List.flatMap_append, List.append_assoc]
        using retained

/-- Buffered source-prefix frames preserve the complete ordered notice inventory.
The notice step needs source accounting at its real cut, not current callback eligibility.
-/
theorem NoticeHistoryFrame.rawEventReplay_admitted {queue work parents before refs}
    (history : NoticeHistoryFrame queue work refs)
    (source : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
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
    : NoticeHistoryFrame (queue.replayGraphEvents events available) work
        (refs
          ++ (queue.rawEventReplay events available).2.flatMap rawGroupNoticeRefs) := by
  have sourceAt (fifo : List GraphEvent) (earlier : fifo.IsPrefix events) :
      UncancelledReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo) := by
    obtain ⟨tail, joined⟩ := earlier
    apply source.replayGraphEvents_admitted generated canonical fifo
      (valid.prefix ⟨tail, by rw [List.append_assoc, joined]⟩) available licensed
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [joined] using accepted
  have loop (remaining fifo : List GraphEvent) (split : events = fifo ++ remaining)
      (noticed : NodeRefs)
      (current : NoticeHistoryFrame (queue.replayGraphEvents fifo available) work noticed)
      : NoticeHistoryFrame
          ((queue.replayGraphEvents fifo available).replayGraphEvents remaining available) work
          (noticed ++ ((queue.replayGraphEvents fifo available).rawEventReplay
            remaining available).2.flatMap rawGroupNoticeRefs) := by
    induction remaining generalizing fifo noticed with
    | nil => simpa only [State.rawEventReplay, State.replayGraphEvents, List.foldl_nil,
        List.flatMap_nil, List.append_nil] using current
    | cons event rest ih =>
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        have next : NoticeHistoryFrame
            ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1 work
            (noticed ++ ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).2.flatMap rawGroupNoticeRefs) :=
          current.handleGraphEvent (sourceAt fifo ⟨event :: rest, split.symm⟩)
          generated canonical (valid.prefix boundary) available licensed |>.withGroupFailures _
        have result := ih (fifo ++ [event]) (by simp [split, List.append_assoc])
          (noticed ++ ((queue.replayGraphEvents fifo available).dispatchGraphEvent event
            available).2.flatMap rawGroupNoticeRefs)
          (by simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
            List.foldl_append, List.foldl_cons, List.foldl_nil] using next)
        simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil, State.rawEventReplay_cons,
          List.flatMap_append, List.append_assoc]
          using result
  simpa only [State.replayGraphEvents, List.foldl_nil]
    using loop events [] (by simp) refs history

/-- Setting termination does not alter the notice-history certificate. -/
theorem NoticeHistoryFrame.withTerminated {queue work refs}
    (history : NoticeHistoryFrame queue work refs) (terminal : Bool)
    : NoticeHistoryFrame {queue with terminated := terminal} work refs :=
  ⟨history.unique, history.registered, history.ancestry⟩

/-- Batch-final startup diagnostics and termination add no group announcements. -/
theorem State.handleGraphEvents_groupNoticeRefs (queue : State) (events : List GraphEvent)
    (running : queue.terminated = false)
    : (queue.handleGraphEvents events).2.flatMap rawGroupNoticeRefs
      = (queue.rawEventReplay events (GraphEvent.availableFailures events)).2.flatMap
          rawGroupNoticeRefs := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [List.flatMap_append, rawGroupNoticeRefs]

/-- One host batch retains notice history under its actual availability snapshot. -/
theorem NoticeHistoryFrame.handleGraphEvents {queue work parents before refs}
    (history : NoticeHistoryFrame queue work refs)
    (source : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : NoticeHistoryFrame (queue.handleGraphEvents events).1 work
        (refs ++ (queue.handleGraphEvents events).2.flatMap rawGroupNoticeRefs) := by
  have licensed : ∀ occurrence errors, (occurrence, errors) ∈ GraphEvent.availableFailures events →
      (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact valid.eachMatches (List.mem_append_right _ received)
  have replayed := history.rawEventReplay_admitted source generated canonical events valid
    (GraphEvent.availableFailures events) licensed accepted
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same, queue.handleGraphEvents_groupNoticeRefs events running]
  exact replayed.withTerminated terminal

/-- Actual host batches retain one unique inventory through every cache boundary. -/
theorem NoticeHistoryFrame.rawBatches {queue work parents before refs}
    (history : NoticeHistoryFrame queue work refs)
    (source : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : NoticeHistoryFrame (queue.replayBatches batches) work
        (refs ++ (queue.rawBatches batches).2.flatMap rawGroupNoticeRefs) := by
  induction batches generalizing queue before refs with
  | nil => simpa only [State.rawBatches, State.replayBatches, List.foldl_nil,
      List.flatMap_nil, List.append_nil] using history
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := history.handleGraphEvents source generated canonical batch (valid.prefix earlier)
        running accepted
      have nextSource := source.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have retained :=
        ih next nextSource
          (by simpa only [List.flatten_cons, List.append_assoc] using valid) restStarted
      simpa only [State.rawBatches, State.replayBatches, List.foldl_cons,
        List.flatMap_append, List.append_assoc]
        using retained

/-- Initial and actual raw-batch group announcements are globally duplicate-free. -/
theorem ExecutedWork.rawBatches_groupRefs_nodup {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten inputs))
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).rootGroups
        ++ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
            rawGroupNoticeRefs).Nodup := by
  let initial := State.initialize (Work.fromExecution work)
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := initial_uncancelledReplayFrame generated canonical
  have history : NoticeHistoryFrame initial work initial.rootGroups := by
    refine ⟨?_, ?_, generated.initialRootAncestorsRetired⟩
    · rw [createWorkQueue_rootGroups]
      exact generated.initialGroups_unique
    · intro ref active
      obtain ⟨node, member, same⟩ := List.mem_map.mp (source.roots.live.present ref active)
      exact same ▸ source.parent.live node member
  exact (history.rawBatches source generated canonical inputs valid
          (by rwa [← inputsStarted_eq_batchesStarted])).unique

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
