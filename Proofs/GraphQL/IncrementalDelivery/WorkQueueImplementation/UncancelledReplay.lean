import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRetirementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceRegistrationAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamEligibility

/-! Source-valid actual host-batch replay derives cancellation-aware certificates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem matchedFailure_not_success {work occurrence errors}
    (failed : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (succeeds : TaskSucceeds work occurrence)
    : False := by
  obtain ⟨owners, producer, path, known⟩ := failed
  obtain ⟨otherOwners, birth, payload, descriptor, successful⟩ := succeeds
  have same := (known.unique descriptor).2.2
  subst payload
  simp [Payload.failure] at successful

/-- Derived source-accounting certificates at one actual consumed input cut. -/
structure UncancelledReplayFrame (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (before : List GraphEvent)
    : Prop where
  markers : queue.UncancelledRetiredMarkers work
  owners : queue.UncancelledTaskAccounting (GraphEvent.groupSettlements before)
  parent : ParentCutFrame queue work parents
  roots : RootReplayFrame queue work parents
  tasks : queue.TaskOwnerFrame work
  pending : queue.PendingAccounting work (GraphEvent.groupSettlements before)
  regions : queue.RegionInventory work (before.flatMap (fun event => event.identities.1))
  rejected
    : queue.TaskRejectionsSatisfy
        (fun occurrence errors =>
          (GraphEvent.taskFailure occurrence errors).MatchesWork work)
  failures
    : ∀ occurrence ∈ GraphEvent.failureSettlements before,
        ∃ task ∈ queue.tasks, task.occurrence = occurrence
  cancellations : queue.CancellationsRetired
  producerRegistrations : queue.ProducerRegistrationAccounting work before
  producers : TaskProducersSucceeded work queue.tasks before
  producerOrder : ProducerOrder work (queue.tasks.map Task.occurrence)

/-- A fresh started callback with an uncancelled owner still has a live task node.
A retired task has no group memberships, while uncancelled owner accounting requires one.
-/
theorem UncancelledReplayFrame.taskNode_of_uncancelledOwner
    {queue work parents before occurrence owners producer payload ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (tracked
      : queue.StartedTaskDisposition occurrence
        ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (known : TaskAt work occurrence owners producer payload)
    (fresh : occurrence ∉ GraphEvent.groupSettlements before)
    (contributes : ref ∈ owners) (uncancelled : ref ∉ queue.cancelledGroups)
    : ∃ node, queue.taskNode? occurrence = some node := by
  cases found : queue.taskNode? occurrence with
  | some node => exact ⟨node, rfl⟩
  | none =>
      have absent := tracked.1.absent found
      obtain ⟨task, registered, identity⟩ := tracked.2
      obtain ⟨address, value, birth, shape, descriptor⟩ :=
        (frame.pending.matching task registered).1
      have sameOwners := ((identity ▸ descriptor).unique known).1
      obtain ⟨node, live, same, member⟩ := frame.owners task registered
        (identity.symm ▸ fresh) ref (sameOwners.symm ▸ contributes) uncancelled
      exact (absent node live (identity ▸ member)).elim

theorem UncancelledReplayFrame.handleGraphEvent_ofDisposition {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (failureRegistered
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (itemsLive
      : ∀ stream items,
          event = .streamItems stream items
          → queue.acceptsGraphEvent (.streamItems stream items) = true)
    : UncancelledReplayFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) := by
  obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last valid
  let current := queue.cacheTaskFailures available
  have parent := frame.parent.cacheTaskFailures available
  have roots := frame.roots.cacheTaskFailures available
  have tasks := frame.tasks.cacheTaskFailures available
  have pending := frame.pending.cacheTaskFailures available
  have owners := frame.owners.cacheTaskFailures available
  have markers := frame.markers.cacheTaskFailures available
  have regions := frame.regions.cacheTaskFailures available
  have rejected := frame.rejected.cacheTaskFailures available licensed
  have rejectedFresh : current.TaskRejectionsSatisfy
      (fun occurrence _ => occurrence ∉ GraphEvent.groupSettlements (before ++ [event])) :=
    rejected.mono (fun _ _ known member =>
      matchedFailure_not_success known (valid.groupSettlements_succeed member))
  have availableFresh : ∀ occurrence errors, (occurrence, errors) ∈ available →
      occurrence ∉ GraphEvent.groupSettlements (before ++ [event]) :=
    fun _ _ member settled => matchedFailure_not_success (licensed _ _ member)
      (valid.groupSettlements_succeed settled)
  have certificates : (queue.handleGraphEvent event available).1.UncancelledRetiredMarkers work
      ∧ (queue.handleGraphEvent event available).1.UncancelledTaskAccounting
        (GraphEvent.groupSettlements (before ++ [event])) := by
    cases event with
    | taskSuccess occurrence result =>
        have taskFresh : occurrence ∉ GraphEvent.groupSettlements before := fun member =>
          fresh.2.2.1 occurrence List.mem_cons_self
            (GraphEvent.groupSettlements_subsetIdentities before member)
        rw [GraphEvent.groupSettlements_append] at rejectedFresh availableFresh ⊢
        have markerResult := markers.taskSuccess owners parent roots tasks pending generated
          canonical occurrence result matching taskFresh rejectedFresh available availableFresh
        refine ⟨markerResult, ?_⟩
        cases found : current.taskNode? occurrence with
        | none =>
            change (current.taskSuccess occurrence result available).1.UncancelledTaskAccounting _
            simpa only [State.taskSuccess, found, GraphEvent.groupSuccesses,
              List.singleton_append]
              using owners.weakenSettled
                (after := occurrence :: GraphEvent.groupSettlements before)
                (by intro task member; simp [member])
        | some node =>
            have registered := pending.started node (List.mem_of_find?_eq_some found)
            have same := (State.taskNode?_some found).2
            have storedContext := pending.registration.putTaskNode
              {node with value := some result.value} registered
            have childAvailable := (owners.putTaskNode {node with value := some result.value}).childGroupsPresent
              roots.retired (markers.putTaskNode _) generated pending.matching storedContext
              parent.closed canonical registered (same.symm ▸ taskFresh) (same.symm ▸ matching)
            exact owners.taskSuccess_ofPendingAccounting pending generated occurrence result
              matching node found taskFresh childAvailable available
    | taskFailure occurrence errors =>
        have taskFresh : occurrence ∉ GraphEvent.groupSettlements before := fun member =>
          fresh.2.2.1 occurrence List.mem_cons_self
            (GraphEvent.groupSettlements_subsetIdentities before member)
        rw [GraphEvent.groupSettlements_append]
        exact ⟨markers.taskFailure owners roots.retired parent.links parent.records
          pending.started pending.matching generated canonical occurrence errors taskFresh,
          owners.taskFailure occurrence errors⟩
    | streamItems stream items =>
        rw [GraphEvent.groupSettlements_append] at rejectedFresh availableFresh ⊢
        exact markers.streamItems owners parent roots tasks regions rejectedFresh pending.pending
          generated canonical matching fresh.1
          (fun item member => fresh.2.2.1 item.occurrence (List.mem_map_of_mem member))
          available availableFresh
    | streamSuccess stream =>
        rw [GraphEvent.groupSettlements_append]
        change (current.streamSuccess stream).1.UncancelledRetiredMarkers work
          ∧ (current.streamSuccess stream).1.UncancelledTaskAccounting _
        unfold State.streamSuccess
        split <;> exact ⟨markers, owners⟩
    | streamFailure stream errors =>
        rw [GraphEvent.groupSettlements_append]
        change (current.streamFailure stream errors).1.UncancelledRetiredMarkers work
          ∧ (current.streamFailure stream errors).1.UncancelledTaskAccounting _
        unfold State.streamFailure
        split <;> exact ⟨markers, owners⟩
    | groupFailure notice =>
        rw [GraphEvent.groupSettlements_append]
        change (current.groupFailure notice).1.UncancelledRetiredMarkers work
          ∧ (current.groupFailure notice).1.UncancelledTaskAccounting _
        unfold State.groupFailure
        split
        · exact ⟨markers, owners⟩
        · split <;> exact ⟨markers, owners⟩
  refine ⟨
    certificates.1,
    certificates.2,
    frame.parent.handleGraphEvent generated canonical event matching available,
    frame.roots.handleGraphEvent generated frame.pending.registration canonical event
      matching available,
    frame.tasks.handleGraphEvent frame.pending frame.roots.live.present event matching
      available,
    ?_,
    ?_,
    frame.rejected.handleGraphEvent event
      (by
        intro occurrence errors same
        cases same
        exact matching)
      available licensed,
    ?_,
    frame.cancellations.handleGraphEvent frame.parent.live frame.parent.tasks event
      matching available,
    frame.producerRegistrations.handleGraphEvent event matching available ?_ itemsLive,
    (State.handleGraphEvent_producerOrder frame.producers frame.producerOrder
      priorValid matching fresh available).1,
    (State.handleGraphEvent_producerOrder frame.producers frame.producerOrder
      priorValid matching fresh available).2
  ⟩
  · rw [GraphEvent.groupSettlements_append]
    exact frame.pending.handleGraphEvent_successes_ofMatching generated
      (GraphEvent.groupSettlements_subsetIdentities before) event matching fresh available
  · simpa only [List.flatMap_append, List.flatMap_singleton]
      using frame.regions.handleGraphEvent event matching available
  · intro occurrence recorded
    rw [GraphEvent.failureSettlements_append] at recorded
    have registered : ∃ task ∈ queue.tasks, task.occurrence = occurrence := by
      rcases List.mem_append.mp recorded with incoming | old
      · cases event with
        | taskFailure task errors =>
            have same : occurrence = task := List.mem_singleton.mp incoming
            subst occurrence
            exact failureRegistered task errors rfl
        | taskSuccess | streamItems | streamSuccess | streamFailure | groupFailure =>
            cases incoming
      · exact frame.failures occurrence old
    obtain ⟨task, member, same⟩ := registered
    exact ⟨task, queue.handleGraphEvent_tasks_subset event available member, same⟩

  · intro occurrence result same missing
    have absent := (tracked occurrence result same).1.absent missing
    obtain ⟨task, member, identity⟩ := (tracked occurrence result same).2
    obtain ⟨address, payload, producer, shape, descriptor⟩ :=
      (frame.pending.matching task member).1
    have occurrenceEq : occurrence = .executionGroup address := identity.symm.trans shape
    refine ⟨address, task.groups.map Execution.DeliveryNode.ref, congrArg some occurrenceEq,
      ⟨producer, payload, ?_⟩, ?_⟩
    · simpa only [shape] using descriptor
    · intro ref contributes
      apply Classical.byContradiction
      intro uncancelled
      have unsettled : task.occurrence ∉ GraphEvent.groupSettlements before := by
        rw [identity]
        subst event
        exact fun settled => fresh.2.2.1 occurrence List.mem_cons_self
          (GraphEvent.groupSettlements_subsetIdentities before settled)
      obtain ⟨node, live, refEq, linked⟩ :=
        frame.owners task member unsettled ref contributes uncancelled
      exact absent node live (identity ▸ linked)

theorem UncancelledReplayFrame.withGroupFailures {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (notices : List GroupFailureEvent)
    : UncancelledReplayFrame { queue with groupFailureEvents := notices } work parents
        before := by
  exact ⟨frame.markers, frame.owners,
    ⟨frame.parent.safe, frame.parent.keys, frame.parent.records, frame.parent.links,
      frame.parent.children, frame.parent.live, frame.parent.tasks, frame.parent.closed,
      frame.parent.fields, frame.parent.complete, frame.parent.cancelled,
      frame.parent.registration.withGroupFailures notices⟩,
    ⟨⟨frame.roots.live.refs, frame.roots.live.records, frame.roots.live.links,
        frame.roots.live.registered, frame.roots.live.tasks, frame.roots.live.roots,
        ⟨frame.roots.live.support.contents, frame.roots.live.support.roots⟩,
        frame.roots.live.present⟩, frame.roots.retired⟩,
    ⟨frame.tasks.owners, frame.tasks.disposition, frame.tasks.keys, frame.tasks.registered,
      frame.tasks.matching, frame.tasks.sound⟩,
    frame.pending.withGroupFailures notices,
    ⟨frame.regions.regions, frame.regions.matching, frame.regions.registrations, frame.regions.started⟩,
    frame.rejected, frame.failures, frame.cancellations, frame.producerRegistrations,
    frame.producers, frame.producerOrder⟩

/-- Realized enqueue effects retain cancellation-aware source certificates. -/
theorem UncancelledReplayFrame.dispatchGraphEvent_ofDisposition
    {queue work parents before} (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence
            ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (registered
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors
          → ∃ task ∈ queue.tasks, task.occurrence = occurrence)
    (itemsLive
      : ∀ stream items,
          event = .streamItems stream items
          → queue.acceptsGraphEvent (.streamItems stream items) = true)
    : UncancelledReplayFrame (queue.dispatchGraphEvent event available).1 work parents
        (before ++ [event]) :=
  (frame.handleGraphEvent_ofDisposition generated canonical event valid available licensed
    tracked registered itemsLive).withGroupFailures
    _

/-- Strict eventwise source eligibility supplies the buffered disposition evidence. -/
theorem UncancelledReplayFrame.handleGraphEvent {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
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
    : UncancelledReplayFrame (queue.handleGraphEvent event available).1 work parents
        (before ++ [event]) := by
  have registered (occurrence : Occurrence)
      (someTask : queue.taskNode? occurrence ≠ none) :
      queue.StartedTaskDisposition occurrence
        ∧ ∃ task ∈ queue.tasks, task.occurrence = occurrence := by
    cases found : queue.taskNode? occurrence with
    | none => exact (someTask found).elim
    | some node => exact ⟨.inl ⟨node, found⟩, node.task,
        frame.pending.started node (List.mem_of_find?_eq_some found),
        (State.taskNode?_some found).2⟩
  apply frame.handleGraphEvent_ofDisposition generated canonical event valid available
    licensed
  · intro occurrence result same
    subst event
    apply registered occurrence
    intro missing
    simp [State.acceptsGraphEvent, missing] at accepted
  · intro occurrence errors same
    subst event
    exact (registered occurrence (by
      intro missing
      simp [State.acceptsGraphEvent, missing] at accepted)).2
  · intro stream items same
    exact same ▸ accepted

theorem UncancelledReplayFrame.replayGraphEvents {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
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
    : UncancelledReplayFrame (queue.replayGraphEvents events available) work parents
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
      have next : UncancelledReplayFrame (queue.dispatchGraphEvent event available).1 work parents
          (before ++ [event]) :=
        (frame.handleGraphEvent generated canonical event (valid.prefix earlier)
          accepts.1 available licensed).withGroupFailures _
      have retained :=
        ih next (by simpa only [List.append_assoc, List.singleton_append] using valid)
          accepts.2
      simpa only [State.replayGraphEvents, List.foldl_cons, List.append_assoc,
        List.singleton_append]
        using retained

/-- Actual buffered replay preserves cancellation-aware source evidence, distinguishing
registered children from an ignored callback whose producer owners were all cancelled.
-/
theorem UncancelledReplayFrame.replayGraphEvents_admitted {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
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
    : UncancelledReplayFrame (queue.replayGraphEvents events available) work parents
        (before ++ events) := by
  apply prefix_invariant events
    (fun fifo =>
      UncancelledReplayFrame (queue.replayGraphEvents fifo available) work parents
        (before ++ fifo))
  · simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using frame
  · intro fifo event rest split past
    have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
      ⟨rest, by simp [split, List.append_assoc]⟩
    have validCut := valid.prefix boundary
    have validFifo := (validGraphEvents_last validCut).1
    have current := past fifo (List.prefix_refl _)
    have taskEvidence (occurrence : Occurrence)
        (kind : (∃ result, event = .taskSuccess occurrence result)
          ∨ ∃ errors, event = .taskFailure occurrence errors) :
        (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence
          ∧ ∃ task ∈ (queue.replayGraphEvents fifo available).tasks,
              task.occurrence = occurrence := by
      obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
        event available accepted ⟨rest, by simp [split]⟩
      have prior := past seen seenPrefix
      rcases kind with ⟨result, same⟩ | ⟨errors, same⟩ <;> subst event
      all_goals
        cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
        | none => simp [State.acceptsGraphEvent, found] at eligible
        | some node =>
            obtain ⟨remaining, history⟩ := seenPrefix
            have disposition := prior.pending.startedTaskDisposition_atPrefix found prior.producers
              prior.producerOrder remaining (by simpa [history, List.append_assoc] using validFifo) available
            rw [← history, State.replayGraphEvents_append queue seen remaining available]
            exact ⟨disposition, node.task,
              (queue.replayGraphEvents seen available).replayGraphEvents_tasks_subset remaining available
                (prior.pending.started node (List.mem_of_find?_eq_some found)),
              (State.taskNode?_some found).2⟩
    have itemsLive : ∀ stream items, event = .streamItems stream items →
        (queue.replayGraphEvents fifo available).acceptsGraphEvent (.streamItems stream items) = true := by
      intro stream items same
      subst event
      obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
        (.streamItems stream items) available accepted ⟨rest, by simp [split]⟩
      obtain ⟨remaining, history⟩ := seenPrefix
      obtain ⟨address, results, producer, dependencies, located, nonempty, unclosed, rest⟩ :=
        validCut.last_ready
      have unclosedRemaining : stream.ref ∉ remaining.flatMap (fun event => event.identities.2) := by
        intro member
        apply unclosed
        rw [← history, List.flatMap_append, List.flatMap_append]
        exact List.mem_append_right _ (List.mem_append_right _ member)
      rw [← history, State.replayGraphEvents_append queue seen remaining available]
      exact List.contains_iff_mem.mpr ((queue.replayGraphEvents seen available
        ).replayGraphEvents_retains_unclosed_stream remaining stream.ref
          (List.contains_iff_mem.mp eligible) unclosedRemaining available)
    have next := current.dispatchGraphEvent_ofDisposition generated canonical event validCut
      available licensed
      (fun occurrence result same => taskEvidence occurrence (.inl ⟨result, same⟩))
      (fun occurrence errors same => (taskEvidence occurrence (.inr ⟨errors, same⟩)).2)
      itemsLive
    simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc] using next

theorem UncancelledReplayFrame.withTerminated {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before) (terminated : Bool)
    : UncancelledReplayFrame { queue with terminated := terminated } work parents
        before := by
  exact ⟨frame.markers, frame.owners,
    ⟨frame.parent.safe, frame.parent.keys, frame.parent.records, frame.parent.links,
      frame.parent.children, frame.parent.live, frame.parent.tasks, frame.parent.closed,
      frame.parent.fields, frame.parent.complete, frame.parent.cancelled,
      frame.parent.registration.withTerminated terminated⟩,
    ⟨⟨frame.roots.live.refs, frame.roots.live.records, frame.roots.live.links,
        frame.roots.live.registered, frame.roots.live.tasks, frame.roots.live.roots,
        ⟨frame.roots.live.support.contents, frame.roots.live.support.roots⟩,
        frame.roots.live.present⟩, frame.roots.retired⟩,
    ⟨frame.tasks.owners, frame.tasks.disposition, frame.tasks.keys, frame.tasks.registered,
      frame.tasks.matching, frame.tasks.sound⟩,
    frame.pending.withTerminated terminated, frame.regions.withTerminated terminated,
    frame.rejected, frame.failures, frame.cancellations, frame.producerRegistrations,
    frame.producers, frame.producerOrder⟩

theorem UncancelledReplayFrame.handleGraphEvents {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : UncancelledReplayFrame (queue.handleGraphEvents events).1 work parents
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

theorem UncancelledReplayFrame.runNormalized {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : UncancelledReplayFrame (queue.runNormalized batches).1 work parents
        (before ++ batches.flatten) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil =>
      simpa only [List.flatten_nil, List.append_nil, State.replayBatches, List.foldl_nil]
        using frame
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := frame.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have retained := ih next (by simpa only [List.flatten_cons, List.append_assoc] using valid)
        restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using retained

theorem initial_uncancelledReplayFrame {work parents} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : UncancelledReplayFrame (State.initialize (Work.fromExecution work)) work parents
        [] := by
  exact ⟨
    .of_empty work (createWorkQueue_cancelledGroups_empty _),
    createWorkQueue_uncancelledTaskAccounting work generated,
    initial_parentCutFrame generated canonical,
    initialRootReplayFrame generated canonical,
    createWorkQueue_taskOwnerFrame work,
    createWorkQueue_pendingAccounting work generated.declarations,
    createWorkQueue_regionInventory work,
    createWorkQueue_taskRejections (Work.fromExecution work) _,
    (by intro occurrence impossible; cases impossible),
    createWorkQueue_cancellationsRetired _,
    createWorkQueue_producerRegistrationAccounting work,
    (createWorkQueue_producerOrder work).1,
    (createWorkQueue_producerOrder work).2
  ⟩

/-- Actual host-batch/FIFO prefixes derive the full cancellation-aware source frame.
Witness: completed earlier batches retain their own snapshots; the current FIFO prefix
uses the whole current batch's availability and exactly its consumed source identities.
-/
theorem ExecutedWork.uncancelledFrame_atBatchPrefix {work : Execution.Work}
    {parents : Nat → NodeRefs} (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (earlier : List (List GraphEvent)) (batch : List GraphEvent)
    (later : List (List GraphEvent)) (fifo : List GraphEvent)
    (valid : ValidGraphEvents work (earlier ++ batch :: later).flatten)
    (started : inputsStarted work (earlier ++ batch :: later) = true)
    (prefixOfBatch : fifo.IsPrefix batch)
    : UncancelledReplayFrame
        (((State.initialize (Work.fromExecution work)).replayBatches
            earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch))
        work parents (earlier.flatten ++ fifo) := by
  let initial := State.initialize (Work.fromExecution work)
  have checked : initial.batchesStarted (earlier ++ batch :: later) = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  rw [State.batchesStarted_append, Bool.and_eq_true] at checked
  have validEarlier : ValidGraphEvents work earlier.flatten :=
    valid.prefix ⟨(batch :: later).flatten, by simp [List.flatten_append]⟩
  have before := (initial_uncancelledReplayFrame generated canonical).runNormalized
    (before := []) generated canonical earlier validEarlier checked.1
  rw [State.runNormalized_replayBatches] at before
  simp only [List.nil_append] at before
  obtain ⟨_, accepted, _⟩ :=
    (initial.replayBatches earlier).batchesStarted_cons batch later checked.2
  obtain ⟨tail, same⟩ := prefixOfBatch
  have fifoAccepted : State.acceptsBatch.go (fun _ => false)
      (GraphEvent.availableFailures batch) (initial.replayBatches earlier) fifo = true := by
    apply State.acceptsBatch_go_prefix (after := tail)
    simpa only [State.acceptsBatch, same] using accepted
  have validFifo : ValidGraphEvents work (earlier.flatten ++ fifo) := by
    apply valid.prefix
    refine ⟨tail ++ later.flatten, ?_⟩
    simp only [List.flatten_append, List.flatten_cons, ← same, List.append_assoc]
  have licensed : ∀ occurrence errors,
      (occurrence, errors) ∈ GraphEvent.availableFailures batch →
        (GraphEvent.taskFailure occurrence errors).MatchesWork work := by
    intro occurrence errors member
    obtain ⟨event, received, identity⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at identity
    obtain ⟨rfl, rfl⟩ := identity
    apply valid.eachMatches
    simp only [List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  exact before.replayGraphEvents_admitted generated canonical fifo validFifo
    (GraphEvent.availableFailures batch) licensed fifoAccepted

private theorem UncancelledReplayFrame.failureFresh {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (valid : ValidGraphEvents work before) {occurrence}
    (recorded : occurrence ∈ GraphEvent.failureSettlements before)
    : ∃ task ∈ queue.tasks,
        task.occurrence = occurrence
        ∧ task.occurrence ∉ GraphEvent.groupSettlements before := by
  obtain ⟨task, registered, same⟩ := frame.failures occurrence recorded
  obtain ⟨owners, producer, path, errors, known⟩ :=
    valid.failureSettlements_known occurrence recorded
  refine ⟨task, registered, same, ?_⟩
  intro settled
  exact matchedFailure_not_success ⟨owners, producer, path, known⟩
    (valid.groupSettlements_succeed (same ▸ settled))

theorem UncancelledReplayFrame.retiredHealth {queue work parents before}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before)
    : queue.UncancelledRetiredHealthy work (GraphEvent.failureSettlements before)
      ∧ queue.RootAncestorsHealthy work (GraphEvent.failureSettlements before)
      ∧ queue.MissingParentAncestorsHealthy work
          (GraphEvent.failureSettlements before) := by
  have retiredHealth : queue.UncancelledRetiredHealthy work
      (GraphEvent.failureSettlements before) := by
    intro node dependencies known retired uncancelled
    have loop (failed : List Occurrence)
        (included : failed.Subset (GraphEvent.failureSettlements before))
        : ¬GroupRecordInvalidated work failed node.ref := by
      induction failed with
      | nil => exact fun invalid => invalid.nonempty rfl
      | cons occurrence rest ih =>
          obtain ⟨task, registered, same, fresh⟩ :=
            frame.failureFresh valid (included List.mem_cons_self)
          have healthy := ih (fun _ member => included (List.mem_cons_of_mem _ member))
          have enlarged := retired.healthy_cons_fresh_of_uncancelledAccounting
            (frame.roots.retired node.ref retired uncancelled) uncancelled
            (frame.markers node.ref retired uncancelled node dependencies known rfl)
            generated known healthy frame.owners registered
            (frame.pending.matching task registered) fresh
          simpa only [same] using enlarged
    exact loop _ (List.Subset.refl _)
  refine ⟨
    retiredHealth,
    ?_,
    retiredHealth.missingParent generated frame.parent.fields canonical
      (fun node member parent parentEq =>
        frame.parent.closed.parent_registered frame.parent.live frame.parent.fields member
          parentEq)
  ⟩
  intro ref active node dependencies known sameRef ancestor member invalid
  obtain ⟨liveNode, live, liveRef⟩ := List.mem_map.mp (frame.roots.live.present ref active)
  have ancestorMarkers := frame.markers.live_record_ancestors frame.parent.safe
    frame.parent.fields frame.parent.closed frame.parent.live canonical known
    ⟨liveNode, live, liveRef.trans sameRef.symm⟩
  have excludes {target} (failure : GroupRecordInvalidated work
      (GraphEvent.failureSettlements before) target) : target ∈ dependencies → False := by
    induction failure with
    | @task occurrence owners target descriptor contributes recorded =>
        intro inChain
        obtain ⟨task, registered, same, fresh⟩ := frame.failureFresh valid recorded
        obtain ⟨producer, payload, taskKnown⟩ := descriptor
        obtain ⟨⟨_, _, _, _, actual⟩, _⟩ := frame.pending.matching task registered
        rw [same] at actual
        have taskContributes : target ∈ task.groups.map Execution.DeliveryNode.ref :=
          (taskKnown.unique actual).1 ▸ contributes
        have retired := frame.roots.live.roots ref active node dependencies known sameRef
          target inChain occurrence owners ⟨producer, payload, taskKnown⟩ contributes
        have uncancelled := ancestorMarkers target inChain occurrence owners
          ⟨producer, payload, taskKnown⟩ contributes
        exact fresh (frame.owners.retired_contributor_settled registered taskContributes
          uncancelled retired)
    | @ancestor other otherDependencies target descriptor included failure ih =>
        intro inChain
        exact ih ((generated.groupRecordAncestors_trans known descriptor inChain) included)
  exact excludes invalid member

/-- Actual valid started host batches derive cancellation-aware owners and ancestor markers.
Witness: each batch uses its whole failure-availability snapshot while the success ledger
advances only at FIFO success consumption. No flattened-state equality or health premise
is assumed.
-/
theorem ExecutedWork.runNormalized_uncancelledCertificates {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      queue.UncancelledTaskAccounting (GraphEvent.groupSettlements batches.flatten)
      ∧ queue.UncancelledRetiredMarkers work := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replayed := (initial_uncancelledReplayFrame generated canonical).runNormalized (before := [])
    generated canonical batches valid (by rwa [inputsStarted_eq_batchesStarted] at started)
  exact ⟨replayed.owners, replayed.markers⟩

/-- Every consumed failed task remains in the actual queue's permanent task registry.
Witness: accepted FIFO failure lookup supplies registration, and all later handlers
retain task descriptors, even after their live computation records are removed.
-/
theorem ExecutedWork.runNormalized_failedTasksRegistered {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∀ occurrence ∈ GraphEvent.failureSettlements batches.flatten,
        ∃ task ∈
          ((State.initialize (Work.fromExecution work)).runNormalized batches).1.tasks,
          task.occurrence = occurrence := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replayed := (initial_uncancelledReplayFrame generated canonical).runNormalized (before := [])
    generated canonical batches valid (by rwa [inputsStarted_eq_batchesStarted] at started)
  exact replayed.failures

/-- Actual host-batch replay has healthy uncancelled retirements and protected root ancestry.
Witness: cancellation-aware owner and ancestor-marker certificates exclude each registered
failed cause from protected retired scopes. The failure inventory follows actual batches,
including their whole availability snapshots, rather than a flattened replay state.
-/
theorem ExecutedWork.runNormalized_retiredHealth {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      let failed :=
        (State.initialize
          (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
          batches
      queue.UncancelledRetiredHealthy work failed
      ∧ queue.RootAncestorsHealthy work failed
      ∧ queue.MissingParentAncestorsHealthy work failed := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replayed := (initial_uncancelledReplayFrame generated canonical).runNormalized (before := [])
    generated canonical batches valid (by rwa [inputsStarted_eq_batchesStarted] at started)
  have health := replayed.retiredHealth generated canonical valid
  have included := ((State.initialize (Work.fromExecution work)
    ).admittedObjectFailureContributionsForBatches_sublist batches).subset
  refine ⟨?_, ?_, ?_⟩
  · intro node dependencies known retired uncancelled invalid
    exact health.1 node dependencies known retired uncancelled (invalid.mono included)
  · intro ref active node dependencies known same ancestor member invalid
    exact health.2.1 ref active node dependencies known same ancestor member
      (invalid.mono included)
  · intro node member dependencies known parent parentEq missing uncancelled ancestor
      includedAncestor invalid
    exact health.2.2 node member dependencies known parent parentEq missing uncancelled
      ancestor includedAncestor (invalid.mono included)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
