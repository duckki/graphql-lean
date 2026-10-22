import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorRootPaths
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminalRoots

/-! Actual source replay derives root paths for every surviving registered contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Each actual accepted handler preserves coverage of all live registered contributors. -/
theorem UncancelledReplayFrame.contributorsCovered_handleGraphEvent
    {queue work parents before} (frame : UncancelledReplayFrame queue work parents before)
    (covered : queue.ContributorsCovered) (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.ContributorsCovered := by
  obtain ⟨_, matching, fresh⟩ := validGraphEvents_last valid
  let current := queue.cacheTaskFailures available
  have parent := frame.parent.cacheTaskFailures available
  have cached := covered.cacheTaskFailures available
  have old {task ref} (registered : task ∈ queue.tasks)
      (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
      (live : ∃ node, (queue.handleGraphEvent event available).1.groupNode? ref = some node)
      : ∃ root ∈ (queue.handleGraphEvent event available).1.rootGroups,
          (queue.handleGraphEvent event available).1.LiveDescendant root ref := by
    have beforeLive : ∃ node, queue.groupNode? ref = some node := by
      cases found : queue.groupNode? ref with
      | some node => exact ⟨node, rfl⟩
      | none =>
          have retired := (State.RetiredGroup.of_lookup_none
            (frame.parent.tasks task registered ref contributes) found).handleGraphEvent
              event available
          obtain ⟨node, lookup⟩ := live
          rw [retired.lookup_none] at lookup
          contradiction
    rcases frame.parent.handleGraphEvent_rootCoveredOrRetired generated canonical event matching
        (.inl (covered task registered ref contributes beforeLive)) available with path | retired
    · exact path
    · obtain ⟨node, lookup⟩ := live
      rw [retired.lookup_none] at lookup
      contradiction
  cases event with
  | taskSuccess occurrence result =>
      change (current.taskSuccess occurrence result available).1.ContributorsCovered
      cases found : current.taskNode? occurrence with
      | none => simpa only [State.taskSuccess, found] using cached
      | some incoming =>
          intro task registered ref contributes live
          rw [State.taskSuccess_tasks found available] at registered
          rcases List.mem_append.mp registered with prior | new
          · exact old (by rwa [State.cacheTaskFailures_tasks] at prior) contributes live
          · obtain ⟨node, lookup⟩ := live
            obtain ⟨child, childFound, _⟩ := State.taskSuccess_integration_groupEdgesFrom
              parent.keys found available ref node lookup
            have taskFresh : occurrence ∉ GraphEvent.groupSettlements before := fun member =>
              fresh.2.2.1 occurrence List.mem_cons_self
                (GraphEvent.groupSettlements_subsetIdentities before member)
            have incomingRegistered := (frame.pending.cacheTaskFailures available).started
              incoming (State.taskNode?_some found).1
            have paths := frame.taskSuccess_childGroup_integrated_root_coverage generated
              canonical matching taskFresh available found
              (fun ref contributes live =>
                cached incoming.task incomingRegistered ref contributes live)
              new contributes ⟨child, childFound⟩
            obtain ⟨preparedParent, _⟩ := frame.taskSuccess_preparedFrames generated canonical occurrence
              result
              matching incoming available found
            exact State.taskSuccess_integrated_root_coverage parent.keys found result available
              (State.RemovalForest.of_generated generated preparedParent.children
                preparedParent.links preparedParent.records canonical)
              paths ⟨node, lookup⟩
  | streamItems stream items =>
      exact cached.streamItems parent (frame.regions.cacheTaskFailures available) generated
        canonical matching fresh.1
        (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member)) available
  | taskFailure occurrence errors =>
      intro task registered ref contributes live
      change task ∈ (current.taskFailure occurrence errors).1.tasks at registered
      rw [State.taskFailure_tasks, State.cacheTaskFailures_tasks] at registered
      exact old registered contributes live
  | streamSuccess stream =>
      intro task registered ref contributes live
      change task ∈ (current.streamSuccess stream).1.tasks at registered
      unfold State.streamSuccess at registered
      split at registered <;> exact old (by rwa [State.cacheTaskFailures_tasks] at registered)
        contributes live
  | streamFailure stream errors =>
      intro task registered ref contributes live
      change task ∈ (current.streamFailure stream errors).1.tasks at registered
      unfold State.streamFailure at registered
      split at registered <;> exact old (by rwa [State.cacheTaskFailures_tasks] at registered)
        contributes live
  | groupFailure notice =>
      change (current.groupFailure notice).1.ContributorsCovered
      unfold State.groupFailure
      split
      · exact cached
      · split
        · exact cached.withGroupFailures _
        · exact cached

/-- Source and contributor-path evidence are indexed by the same consumed history. -/
structure ContributorRootFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent)
    : Prop where
  source : UncancelledReplayFrame queue work parents before
  covered : queue.ContributorsCovered

/-- FIFO replay retains source accounting and all live contributor paths together. -/
theorem ContributorRootFrame.replayGraphEvents {queue work parents before}
    (frame : ContributorRootFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task errors,
          (task, errors) ∈ available
          → (GraphEvent.taskFailure task errors).MatchesWork work)
    (accepted : State.eventsStarted available queue events = true)
    : ContributorRootFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using frame
  | cons event rest ih =>
      have prefixValid := valid.prefix (show (before ++ [event]).IsPrefix
        (before ++ event :: rest) from ⟨rest, by simp⟩)
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available (queue.dispatchGraphEvent event available).1 rest
            = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next : ContributorRootFrame (queue.dispatchGraphEvent event available).1 work parents
          (before ++ [event]) :=
        ⟨frame.source.handleGraphEvent generated canonical event prefixValid accepts.1 available
          licensed |>.withGroupFailures _,
          frame.source.contributorsCovered_handleGraphEvent frame.covered generated canonical
            event prefixValid available |>.withGroupFailures _⟩
      have result := ih next (by simpa [List.append_assoc] using valid) accepts.2
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using result

/-- Source-prefix frames retain live contributor paths without current callback eligibility. -/
theorem ContributorRootFrame.replayGraphEvents_admitted {queue work parents before}
    (frame : ContributorRootFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task errors,
          (task, errors) ∈ available
          → (GraphEvent.taskFailure task errors).MatchesWork work)
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    : ContributorRootFrame (queue.replayGraphEvents events available) work parents
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
      (covered : (queue.replayGraphEvents fifo available).ContributorsCovered)
      : (queue.replayGraphEvents events available).ContributorsCovered := by
    induction remaining generalizing fifo with
    | nil =>
        have same : events = fifo := by simpa only [List.append_nil] using split
        simpa only [same] using covered
    | cons event rest ih =>
        have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
          ⟨rest, by simp [split, List.append_assoc]⟩
        have next : ((queue.replayGraphEvents fifo available).dispatchGraphEvent event available).1.ContributorsCovered :=
          (sourceAt fifo ⟨event :: rest, split.symm⟩
          ).contributorsCovered_handleGraphEvent covered generated canonical event
            (valid.prefix boundary) available |>.withGroupFailures _
        apply ih (fifo ++ [event]) (by simp [split, List.append_assoc])
        simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
          using next
  exact ⟨sourceAt events (List.prefix_refl _), loop events [] (by simp) frame.covered⟩

/-- The batch terminal flag leaves the contributor path certificate unchanged. -/
theorem ContributorRootFrame.withTerminated {queue work parents before}
    (frame : ContributorRootFrame queue work parents before) (terminated : Bool)
    : ContributorRootFrame {queue with terminated := terminated} work parents before := by
  refine ⟨frame.source.withTerminated terminated, ?_⟩
  intro task registered ref contributes live
  obtain ⟨root, active, path⟩ := frame.covered task registered ref contributes live
  exact ⟨root, active, path.of_groupNodes_eq (queue := queue) rfl⟩

/-- A complete host batch uses its fixed cache snapshot and forwards its actual notices. -/
theorem ContributorRootFrame.handleGraphEvents {queue work parents before}
    (frame : ContributorRootFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : ContributorRootFrame (queue.handleGraphEvents events).1 work parents
        (before ++ events) := by
  have licensed : ∀ task errors, (task, errors) ∈ GraphEvent.availableFailures events →
      (GraphEvent.taskFailure task errors).MatchesWork work := by
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

/-- Actual normalized batch replay retains every registered live contributor's root path. -/
theorem ContributorRootFrame.runNormalized {queue work parents before}
    (frame : ContributorRootFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : ContributorRootFrame (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using frame
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := frame.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have result := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using result

/-- Valid started host batches derive unconditional live-contributor root coverage. -/
theorem ExecutedWork.runNormalized_contributorsCovered {work inputs}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        inputs).1.ContributorsCovered := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have initial : ContributorRootFrame (State.initialize (Work.fromExecution work)) work
      parents [] :=
    ⟨initial_uncancelledReplayFrame generated canonical,
      fun _ _ ref _ live => generated.initial_live_group_root_coverage ref live⟩
  exact (initial.runNormalized (before := []) generated canonical inputs valid
          (by rwa [inputsStarted_eq_batchesStarted] at started)).covered

/-- Empty terminal roots retire every registered contributor, including failed contributors. -/
theorem ExecutedWork.terminal_registeredContributor_retired {work inputs task ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.tasks)
    (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.RetiredGroup
        ref := by
  have registration := createWorkQueue_runNormalized_registration valid generated.declarations
  apply State.RetiredGroup.of_lookup_none
    (registration.2.1 task registered ref contributes)
  cases found
        : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.groupNode?
            ref with
  | none => rfl
  | some node =>
      obtain ⟨root, active, _⟩ := generated.runNormalized_contributorsCovered valid started
        task registered ref contributes ⟨node, found⟩
      rw [(createWorkQueue_terminalRoots (Work.fromExecution work) inputs ended).1] at active
      cases active

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
