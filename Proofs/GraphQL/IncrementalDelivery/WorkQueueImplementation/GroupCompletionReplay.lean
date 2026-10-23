import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRootCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FifoGroupCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Announced groups remain active until their own completion through actual host batches. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private def startupControls (failures : List GroupFailureEvent) : List WorkQueueEvent :=
  failures.map (fun failure => .groupFailure failure.group failure.errors)

private abbrev ChannelCompletion (initial : NodeRefs)
    (result : State × List WorkQueueEvent × List GroupFailureEvent)
    : Prop :=
  GroupNoticeCompletion initial (result.1, result.2.1 ++ startupControls result.2.2)

private theorem LiveRootFrame.cacheForCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents) (available : List (Occurrence × Nat))
    : LiveRootFrame (queue.cacheTaskFailures available) work parents := by
  have registered := queue.cacheTaskFailures_registration frame.registered frame.tasks available
  refine ⟨frame.refs.cacheTaskFailures _, frame.records.cacheTaskFailures _,
    frame.links.cacheTaskFailures _, registered.1, registered.2, ?_,
    frame.support.cacheTaskFailures _, ?_⟩
  · intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    exact (frame.roots ref active).mono (fun _ retired => retired.cacheTaskFailures available)
  · intro ref active
    rw [State.cacheTaskFailures_rootGroups] at active
    rw [State.cacheTaskFailures_groupNodes]
    exact frame.present ref active

/-- A matched handler retains exact announced-group completion in both output channels.
The source snapshot is exposed before dispatch; startup failure notices are local
enqueue effects. Structural root protection rules out collateral silent removal.
-/
theorem LiveRootFrame.handleGraphEvent_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : ChannelCompletion queue.rootGroups (queue.handleGraphEvent event available) := by
  have cached := frame.cacheForCompletion available
  have cachedRetired := retired.cacheTaskFailures available
  rw [← queue.cacheTaskFailures_rootGroups available]
  cases event with
  | taskSuccess occurrence result =>
      exact cached.taskSuccess_groupNoticeCompletion cachedRetired generated
        (context.cacheTaskFailures available) canonical matching
        available
  | streamItems stream items =>
      exact cached.streamItems_groupNoticeCompletion cachedRetired generated canonical matching
        available
  | taskFailure occurrence errors =>
      simpa only [ChannelCompletion, State.handleGraphEvent, startupControls,
        List.map_nil, List.append_nil]
        using cached.rootClosureFrame.taskFailure_groupNoticeCompletion generated
          canonical occurrence errors
  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · exact .silent (List.Subset.refl _)
      · split <;> intro ref member <;> exact .inl (by
          simpa [startupControls, rawGroupNoticeRefs] using member)
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> intro ref member <;> exact .inl (by simpa [startupControls, rawGroupNoticeRefs]
        using member)
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> intro ref member <;> exact .inl (by simpa [startupControls, rawGroupNoticeRefs]
        using member)

/-- Dispatch retains failed groups in pending support until their actual FIFO control. -/
theorem LiveRootFrame.dispatchGraphEvent_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (matching : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : FifoGroupNoticeCompletion queue.groupNoticeSupport
        (queue.dispatchGraphEvent event available) := by
  classical
  by_cases ordinary : ∀ failure, event ≠ .groupFailure failure
  · have removal := frame.handleGraphEvent_groupNoticeCompletion retired generated context
      canonical event matching available
    have tracked := removal.enqueueGroupFailures (queue.handleGraphEvent event available).2.2
    simpa only [State.groupNoticeSupport, State.pendingGroupFailureRefs,
      queue.handleGraphEvent_groupFailureEvents_eq event available ordinary,
      State.dispatchGraphEvent] using tracked
  · obtain ⟨failure, denied⟩ := Classical.not_forall.mp ordinary
    have same := Classical.not_not.mp denied
    subst event
    simpa only [State.dispatchGraphEvent, State.handleGraphEvent,
      State.enqueueGroupFailures, List.append_nil, State.groupNoticeSupport,
      State.cacheTaskFailures_rootGroups, State.pendingGroupFailureRefs,
      State.cacheTaskFailures_groupFailureEvents]
      using (queue.cacheTaskFailures available).groupFailure_fifoGroupNoticeCompletion
        failure

/-- Actual FIFO replay composes active, pending and emitted completion evidence. -/
theorem LiveRootFrame.rawEventReplay_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : FifoGroupNoticeCompletion queue.groupNoticeSupport
        (queue.rawEventReplay events available) := by
  induction events generalizing queue with
  | nil => exact .silent (List.Subset.refl _)
  | cons event rest ih =>
      have matched := matching event List.mem_cons_self
      have next := (show RootReplayFrame queue work parents from ⟨frame, retired⟩).dispatchGraphEvent
        generated context canonical event matched available
      have later := ih next.live next.retired (context.dispatchGraphEvent event matched available).1
        (fun _ member => matching _ (List.mem_cons_of_mem _ member))
      rw [State.rawEventReplay_cons queue event rest available]
      exact (frame.dispatchGraphEvent_groupNoticeCompletion retired generated context canonical
        event matched available).append later

/-- A host batch retains pending completion evidence through its optional terminal marker. -/
theorem LiveRootFrame.handleGraphEvents_groupNoticeCompletion {queue work parents}
    (frame : LiveRootFrame queue work parents)
    (retired : queue.UncancelledRetiredAncestors work) (generated : ExecutedWork work)
    (context : queue.RegistrationFrame work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : LiveRootFrame (queue.handleGraphEvents events).1 work parents
      ∧ (queue.handleGraphEvents events).1.UncancelledRetiredAncestors work
      ∧ FifoGroupNoticeCompletion queue.groupNoticeSupport
          (queue.handleGraphEvents events) := by
  have next := (show RootReplayFrame queue work parents from ⟨frame, retired⟩).handleGraphEvents
    generated context canonical events matching
  refine ⟨next.live, next.retired, ?_⟩
  cases running : queue.terminated with
  | true =>
      simp only [State.handleGraphEvents, running, ↓reduceIte]
      exact .silent (List.Subset.refl _)
  | false =>
      have tracked := frame.rawEventReplay_groupNoticeCompletion retired generated context canonical
        events matching (GraphEvent.availableFailures events)
      rw [State.handleGraphEvents_eq_rawEventReplay]
      simp only [running, Bool.false_eq_true, ↓reduceIte]
      split
      · have terminal : FifoGroupNoticeCompletion
            (queue.rawEventReplay events (GraphEvent.availableFailures events)).1.groupNoticeSupport
            ({ (queue.rawEventReplay events (GraphEvent.availableFailures events)).1 with
                terminated := true }, [.workQueueTermination]) := by
          intro ref member
          exact .inl (by simpa [rawGroupNoticeRefs, State.groupNoticeSupport,
            State.pendingGroupFailureRefs] using member)
        exact tracked.append terminal
      · exact tracked

/-- Generated host batches retain announced groups as active, queued or actually completed. -/
theorem ExecutedWork.rawBatches_groupNoticeCompletion {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : FifoGroupNoticeCompletion (State.initialize (Work.fromExecution work)).rootGroups
        ((State.initialize (Work.fromExecution work)).rawBatches batches) := by
  obtain ⟨parents, canonical, frame, retired⟩ := generated.runNormalized_liveRootFrame []
    (by intro event impossible; cases impossible)
  change LiveRootFrame (State.initialize (Work.fromExecution work)) work parents at frame
  change (State.initialize (Work.fromExecution work)).UncancelledRetiredAncestors work at retired
  have loop (remaining : List (List GraphEvent)) (included : remaining.Subset batches)
      (current : State) (live : LiveRootFrame current work parents)
      (closed : current.UncancelledRetiredAncestors work)
      (context : current.RegistrationFrame work)
      : FifoGroupNoticeCompletion current.groupNoticeSupport (current.rawBatches remaining) := by
    induction remaining generalizing current with
    | nil => exact .silent (List.Subset.refl _)
    | cons batch rest ih =>
        have sources : ∀ event ∈ batch, event.MatchesWork work := fun event member =>
          matching event (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩)
        have next := live.handleGraphEvents_groupNoticeCompletion closed generated context canonical
          batch sources
        exact next.2.2.append (ih (fun _ member => included (List.mem_cons_of_mem _ member))
          _ next.1 next.2.1 (context.handleGraphEvents batch sources).1)
  simpa only [State.groupNoticeSupport, State.pendingGroupFailureRefs,
    State.initialize_groupFailureEvents, List.map_nil, List.append_nil]
    using loop batches (List.Subset.refl _) _ frame retired
      (State.initialize_registrationFrame generated.declarations)

/-- Termination completes every announced group after all queued controls are consumed. -/
theorem ExecutedWork.terminalGroupCompleted {work inputs ref}
    (generated : ExecutedWork work)
    (matching : ∀ event ∈ inputs.flatten, event.MatchesWork work)
    (_started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (announced
      : ref
        ∈ (State.initialize (Work.fromExecution work)).rootGroups
          ++ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
              rawGroupNoticeRefs)
    : ref
      ∈ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
          rawGroupClosureRefs := by
  have pending : ((State.initialize (Work.fromExecution work)).rawBatches inputs).1.groupFailureEvents
      = [] := by
    rw [State.rawBatches_state, ← State.runNormalized_replayBatches]
    exact createWorkQueue_terminalPending _ _ ended
  have tracked := (generated.rawBatches_groupNoticeCompletion inputs matching).completed pending
    ref announced
  have empty := (createWorkQueue_replayBatches_terminalRoots ended).1
  exact tracked.resolve_left (by rw [State.rawBatches_state, empty]; simp)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
