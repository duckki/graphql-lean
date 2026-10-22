import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartedTaskRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyCounterPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationHandlers

/-! Exact healthy counters from generated work and the unchanged host-source contract. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Joint replay evidence keeps metadata independent of owner liveness
-----------------------------------------------------------------------------------------

/-- Internal evidence for healthy counters at a source prefix. `parents` is the fixed
execution-derived ancestry assignment. `events` supplies consumed settlements; `failed`
supplies available source failures and can include notifications later in the same batch.
All-group accounting is bounded, while only uninvalidated groups are exact. Cancellation
support and canonical child links are derived alongside those counters.
-/
structure State.HealthyCounterAccounting (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (events : List GraphEvent)
    (failed : List Occurrence)
    : Prop where
  pending : queue.PendingAccounting work (GraphEvent.taskSettlements events)
  healthy : queue.HealthyPendingTracks work (GraphEvent.taskSettlements events) failed
  supported : queue.CachedFailuresSupported work failed
  groups : queue.GroupNodesMatchWork work
  canonical : queue.GroupParentsCanonical parents
  cancelled : queue.CancelledRecordsSupported work failed
  childLinks : queue.ChildLinksCanonical parents
  producers : TaskProducersSucceeded work queue.tasks events
  producerOrder : ProducerOrder work (queue.tasks.map Task.occurrence)

/-- FIFO bookkeeping preserves every healthy-counter and producer certificate. -/
theorem State.HealthyCounterAccounting.withGroupFailures
    {queue work parents events failed}
    (prior : State.HealthyCounterAccounting queue work parents events failed)
    (notices : List GroupFailureEvent)
    : ({ queue with groupFailureEvents := notices }).HealthyCounterAccounting work parents
        events failed :=
  ⟨
    prior.pending.withGroupFailures notices,
    prior.healthy,
    prior.supported,
    prior.groups,
    prior.canonical,
    prior.cancelled,
    prior.childLinks,
    prior.producers,
    prior.producerOrder
  ⟩

/-- The two structural invariants provide the descriptors needed by the health guard.
Witness: the source's canonical dependency assignment identifies each live record's
parent with the first dependency of its contributor-or-ancestor registration record.
-/
theorem State.HealthyCounterAccounting.descriptors {queue work parents events failed}
    (prior : State.HealthyCounterAccounting queue work parents events failed)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : ∀ node ∈ queue.groupNodes,
        ∃ dependencies,
          GroupRecordAt work node.group.node dependencies
          ∧ node.group.parent = dependencies.head? := by
  intro node member
  obtain ⟨dependencies, known⟩ := prior.groups node member
  exact ⟨dependencies, known,
    (prior.canonical node member).trans (congrArg List.head? (canonical _ _ known)).symm⟩

/-- Initial lowering establishes exact healthy counts and their supporting metadata.
Witness: the existing initialization lemmas, with the same canonical parent assignment
that root execution supplies for all later child work.
-/
theorem createWorkQueue_healthyCounterAccounting (work : Execution.Work)
    (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (certified : DeclarationCoverage.Certified [] work)
    : (State.initialize (Work.fromExecution work)).HealthyCounterAccounting work parents
        [] [] :=
  ⟨
    createWorkQueue_pendingAccounting work certified,
    createWorkQueue_healthyPendingTracks work,
    createWorkQueue_cachedFailuresSupported _ _ _,
    createWorkQueue_groupNodesMatchWork work,
    createWorkQueue_groupParentsCanonical _ parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical_root canonical member),
    createWorkQueue_cancelledRecordsSupported _ _ _,
    createWorkQueue_childLinksCanonical _ parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical_root canonical member),
    (createWorkQueue_producerOrder work).1,
    (createWorkQueue_producerOrder work).2
  ⟩

/-- One accepted valid event preserves exact healthy counters without a root-health law.
Witness: cancellation-aware handler lemmas and independently preserved structural/cache
metadata. Fresh child tasks come from source validity, not from an extra implementation
or output-admission premise.
-/
theorem State.HealthyCounterAccounting.handleGraphEvent {queue work parents before}
    (prior
      : State.HealthyCounterAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    : (queue.handleGraphEvent event).1.HealthyCounterAccounting work parents
        (before ++ [event]) (GraphEvent.failureSettlements (before ++ [event])) := by
  have nextPending := prior.pending.handleGraphEvent generated
    (GraphEvent.taskSettlements_subsetIdentities before) event matching fresh accepted
  rw [← GraphEvent.taskSettlements_append] at nextPending
  have nextHealthy : (queue.handleGraphEvent event).1.HealthyPendingTracks work
      (GraphEvent.taskSettlements (before ++ [event]))
      (GraphEvent.failureSettlements (before ++ [event])) := by
    rw [GraphEvent.taskSettlements_append, GraphEvent.failureSettlements_append]
    cases event with
    | taskSuccess occurrence result =>
        cases found : queue.taskNode? occurrence with
        | none => simp [State.acceptsGraphEvent, found] at accepted
        | some node =>
            apply prior.healthy.taskSuccess_allOutcomes prior.pending occurrence result
              node found
            · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (GraphEvent.taskSettlements_subsetIdentities before member)
            · exact fun _ member earlier => matching.childTasksFresh valid fresh member
                (GraphEvent.taskSettlements_subsetIdentities before earlier)
            · exact prior.pending.matching.contributorsNodup generated
                (prior.pending.started node (List.mem_of_find?_eq_some found))
            · intro task member
              obtain ⟨address, payload, same, known⟩ := matching.childTask_producer member
              exact ⟨⟨address, payload, some occurrence, same, known⟩,
                matching.childTask_groupsExact member⟩
    | groupFailure failure =>
        dsimp only [State.handleGraphEvent, State.groupFailure, GraphEvent.recordTaskOutcome,
          GraphEvent.groupFailures, List.nil_append]
        split
        · exact prior.healthy
        · split <;> exact prior.healthy
    | taskFailure occurrence errors =>
        exact prior.healthy.taskFailure_allOutcomes prior.pending occurrence errors
    | streamItems stream items =>
        apply prior.healthy.streamItems_ofBound prior.pending.pending stream items
        intro item member task taskMember earlier
        exact matching.streamItem_childTasksFresh valid fresh member taskMember
          (GraphEvent.taskSettlements_subsetIdentities before earlier)
    | streamSuccess stream =>
        dsimp only [GraphEvent.recordTaskOutcome, GraphEvent.groupFailures, List.nil_append,
          State.handleGraphEvent, State.streamSuccess]
        split <;> exact prior.healthy
    | streamFailure stream errors =>
        dsimp only [GraphEvent.recordTaskOutcome, GraphEvent.groupFailures, List.nil_append,
          State.handleGraphEvent, State.streamFailure]
        split <;> exact prior.healthy
  have nextSupport : (queue.handleGraphEvent event).1.CachedFailuresSupported work
      (GraphEvent.failureSettlements (before ++ [event])) := by
    have earlier : (GraphEvent.failureSettlements before).Subset
        (GraphEvent.failureSettlements (before ++ [event])) := by
      rw [GraphEvent.failureSettlements_append]
      exact List.subset_append_right _ _
    apply (prior.supported.weaken earlier).handleGraphEvent prior.pending.started
      prior.pending.matching event
    intro occurrence errors equal
    subst event
    simp [GraphEvent.failureSettlements_append, GraphEvent.groupFailures]
  have included : (GraphEvent.failureSettlements before).Subset
      (GraphEvent.failureSettlements (before ++ [event])) := by
    rw [GraphEvent.failureSettlements_append]
    exact List.subset_append_right _ _
  have nextCancelled := (prior.cancelled.weaken included).handleGraphEvent
    (prior.supported.weaken included) prior.pending.started prior.pending.matching
    prior.groups prior.childLinks prior.pending.sound canonical event matching
    (by
      intro occurrence errors same node found
      subst event
      simp [GraphEvent.failureSettlements_append, GraphEvent.groupFailures])
  exact ⟨nextPending, nextHealthy, nextSupport,
    prior.groups.handleGraphEvent event matching,
    prior.canonical.handleGraphEvent event matching canonical,
    nextCancelled, prior.childLinks.handleGraphEvent event matching canonical,
    (State.handleGraphEvent_producerOrder prior.producers prior.producerOrder
      valid matching fresh).1,
    (State.handleGraphEvent_producerOrder prior.producers prior.producerOrder
      valid matching fresh).2⟩

-----------------------------------------------------------------------------------------
-- Lift the event invariant to batches and normalized source replay
-----------------------------------------------------------------------------------------

/-- Enqueue effects retain the same healthy-counter evidence. -/
theorem State.HealthyCounterAccounting.dispatchGraphEvent {queue work parents before}
    (prior
      : State.HealthyCounterAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    : (queue.dispatchGraphEvent event).1.HealthyCounterAccounting work parents
        (before ++ [event]) (GraphEvent.failureSettlements (before ++ [event])) :=
  (prior.handleGraphEvent generated canonical valid event matching fresh
    accepted).withGroupFailures
    _

/-- Sequential event replay retains the joint healthy-counter evidence.
Witness: list induction extracts each actual accepted source-prefix extension.
-/
theorem State.HealthyCounterAccounting.replayGraphEvents {queue work parents before}
    (prior
      : State.HealthyCounterAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.eventsStarted [] queue events = true)
    : (queue.replayGraphEvents events).HealthyCounterAccounting work parents
        (before ++ events) (GraphEvent.failureSettlements (before ++ events)) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted [] (queue.dispatchGraphEvent event).1 rest = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next := prior.dispatchGraphEvent generated canonical validBefore event matching
        fresh accepts.1
      have retained := ih next (by simpa [List.append_assoc] using valid) accepts.2
      simpa [State.replayGraphEvents, List.append_assoc] using retained

/-- Setting the terminal flag leaves every counter and metadata invariant unchanged.
Witness: the flag does not occur in any field of the joint proof-side record.
-/
theorem State.HealthyCounterAccounting.withTerminated {queue work parents events failed}
    (prior : State.HealthyCounterAccounting queue work parents events failed)
    (terminated : Bool)
    : ({queue with terminated := terminated}).HealthyCounterAccounting work parents
        events failed :=
  ⟨
    prior.pending.withTerminated terminated,
    prior.healthy,
    prior.supported,
    prior.groups,
    prior.canonical,
    prior.cancelled,
    prior.childLinks,
    prior.producers,
    prior.producerOrder
  ⟩

/-- Health may use a larger available-failure inventory than the consumed source prefix. -/
theorem State.HealthyCounterAccounting.weakenFailures
    {queue work parents events before after}
    (prior : State.HealthyCounterAccounting queue work parents events before)
    (included : before.Subset after)
    : queue.HealthyCounterAccounting work parents events after :=
  ⟨
    prior.pending,
    prior.healthy.weakenFailures included,
    prior.supported.weaken included,
    prior.groups,
    prior.canonical,
    prior.cancelled.weaken included,
    prior.childLinks,
    prior.producers,
    prior.producerOrder
  ⟩

/-- Exposing licensed caches preserves the consumed-prefix counter coordinate. -/
theorem State.HealthyCounterAccounting.cacheTaskFailures
    {queue work parents events failed}
    (prior : State.HealthyCounterAccounting queue work parents events failed)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    : (queue.cacheTaskFailures available).HealthyCounterAccounting work parents events
        failed := by
  have healthy : (queue.cacheTaskFailures available).HealthyPendingTracks work
      (GraphEvent.taskSettlements events) failed := by
    intro node member clear
    rw [State.cacheTaskFailures_groupNodes] at member
    exact prior.healthy node member clear
  have cancelled : (queue.cacheTaskFailures available).CancelledRecordsSupported work failed := by
    intro ref member
    rw [State.cacheTaskFailures_cancelledGroups] at member
    exact prior.cancelled ref member
  exact ⟨
    prior.pending.cacheTaskFailures available,
    healthy,
    prior.supported.cacheTaskFailures prior.pending.started prior.pending.matching
      available recorded,
    prior.groups.cacheTaskFailures available,
    prior.canonical.cacheTaskFailures available,
    cancelled,
    prior.childLinks.cacheTaskFailures available,
    (by simpa only [State.cacheTaskFailures_tasks] using prior.producers),
    (by simpa only [State.cacheTaskFailures_tasks] using prior.producerOrder)
  ⟩

/-- One FIFO step advances consumed settlements under a fixed available-failure inventory. -/
theorem State.HealthyCounterAccounting.handleGraphEvent_inInventory_ofDisposition
    {queue work parents before failed}
    (prior : State.HealthyCounterAccounting queue work parents before failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence)
    : (queue.handleGraphEvent event available).1.HealthyCounterAccounting work parents
        (before ++ [event]) failed := by
  let current := queue.cacheTaskFailures available
  have cached := prior.cacheTaskFailures available recorded
  have nextPending := prior.pending.handleGraphEvent_ofMatching generated
    (GraphEvent.taskSettlements_subsetIdentities before) event source fresh available
  rw [← GraphEvent.taskSettlements_append] at nextPending
  have nextHealthy : (queue.handleGraphEvent event available).1.HealthyPendingTracks work
      (GraphEvent.taskSettlements (before ++ [event])) failed := by
    rw [GraphEvent.taskSettlements_append]
    cases event with
    | taskSuccess occurrence result =>
        cases found : current.taskNode? occurrence with
        | none =>
            change (current.taskSuccess occurrence result available).1.HealthyPendingTracks
              work (occurrence :: GraphEvent.taskSettlements before) failed
            simp only [State.taskSuccess, found]
            have absent :=
              ((tracked occurrence result rfl).cacheTaskFailures available).absent found
            intro node member healthy
            rw [GroupNode.PendingTracks, unsettledCount_settle_absent node.tasks
              (GraphEvent.taskSettlements before) occurrence (absent node member)]
            exact cached.healthy node member healthy
        | some node =>
            apply cached.healthy.taskSuccess_allOutcomes cached.pending occurrence result
              node found (available := available)
            · exact fun member => fresh.2.2.1 occurrence (by simp [GraphEvent.identities])
                (GraphEvent.taskSettlements_subsetIdentities before member)
            · exact fun _ member earlier => source.childTasksFresh valid fresh member
                (GraphEvent.taskSettlements_subsetIdentities before earlier)
            · exact cached.pending.matching.contributorsNodup generated
                (cached.pending.started node (List.mem_of_find?_eq_some found))
            · intro task member
              obtain ⟨address, payload, same, known⟩ := source.childTask_producer member
              exact ⟨⟨address, payload, some occurrence, same, known⟩,
                source.childTask_groupsExact member⟩
    | groupFailure failure =>
        change (current.groupFailure failure).1.HealthyPendingTracks work
          (GraphEvent.taskSettlements before) failed
        unfold State.groupFailure
        split
        · exact cached.healthy
        · split <;> exact cached.healthy
    | taskFailure occurrence errors =>
        have enlarged := cached.healthy.taskFailure_allOutcomes cached.pending occurrence errors
        exact enlarged.weakenFailures
          (by
            intro task member
            rcases List.mem_cons.mp member with rfl | old
            · exact recorded _ _ (notified _ _ rfl)
            · exact old)
    | streamItems stream items =>
        apply cached.healthy.streamItems_ofBound cached.pending.pending stream items
          (available := available)
        intro item member task taskMember earlier
        exact source.streamItem_childTasksFresh valid fresh member taskMember
          (GraphEvent.taskSettlements_subsetIdentities before earlier)
    | streamSuccess stream =>
        change (current.streamSuccess stream).1.HealthyPendingTracks work
          (GraphEvent.taskSettlements before) failed
        unfold State.streamSuccess
        split <;> exact cached.healthy
    | streamFailure stream errors =>
        change (current.streamFailure stream errors).1.HealthyPendingTracks work
          (GraphEvent.taskSettlements before) failed
        unfold State.streamFailure
        split <;> exact cached.healthy
  exact ⟨
    nextPending,
    nextHealthy,
    prior.supported.handleGraphEvent_available prior.pending.started
      prior.pending.matching event source available recorded notified,
    prior.groups.handleGraphEvent event source available,
    prior.canonical.handleGraphEvent event source canonical available,
    prior.cancelled.handleGraphEvent prior.supported prior.pending.started
      prior.pending.matching prior.groups prior.childLinks prior.pending.sound canonical
      event source (fun occurrence errors same _ _ => recorded _ _ (notified _ _ same))
      available recorded,
    prior.childLinks.handleGraphEvent event source canonical available,
    (State.handleGraphEvent_producerOrder prior.producers prior.producerOrder
      valid source fresh available).1,
    (State.handleGraphEvent_producerOrder prior.producers prior.producerOrder
      valid source fresh available).2
  ⟩

/-- Enqueue effects retain the same healthy-counter evidence. -/
theorem State.HealthyCounterAccounting.dispatchGraphEvent_inInventory_ofDisposition
    {queue work parents before failed}
    (prior : State.HealthyCounterAccounting queue work parents before failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    (tracked
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → queue.StartedTaskDisposition occurrence)
    : (queue.dispatchGraphEvent event available).1.HealthyCounterAccounting work parents
        (before ++ [event]) failed :=
  (prior.handleGraphEvent_inInventory_ofDisposition generated canonical valid event source
    fresh available recorded notified tracked).withGroupFailures
    _

/-- The live-callback specialization of disposition-aware counter preservation. -/
theorem State.HealthyCounterAccounting.handleGraphEvent_inInventory
    {queue work parents before failed}
    (prior : State.HealthyCounterAccounting queue work parents before failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : (queue.handleGraphEvent event available).1.HealthyCounterAccounting work parents
        (before ++ [event]) failed := by
  apply prior.handleGraphEvent_inInventory_ofDisposition generated canonical valid event
    source fresh available recorded notified
  intro occurrence result same
  subst event
  cases found : queue.taskNode? occurrence with
  | none => simp [State.acceptsGraphEvent, found] at accepted
  | some node => exact .inl ⟨node, found⟩

/-- Enqueue effects retain the same healthy-counter evidence. -/
theorem State.HealthyCounterAccounting.dispatchGraphEvent_inInventory
    {queue work parents before failed}
    (prior : State.HealthyCounterAccounting queue work parents before failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (source : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          event = .taskFailure occurrence errors → (occurrence, errors) ∈ available)
    : (queue.dispatchGraphEvent event available).1.HealthyCounterAccounting work parents
        (before ++ [event]) failed :=
  (prior.handleGraphEvent_inInventory generated canonical valid event source fresh
    accepted available recorded notified).withGroupFailures
    _

/-- Every handler in a host batch uses that batch's complete availability snapshot. -/
theorem State.HealthyCounterAccounting.replayGraphEvents_inInventory
    {queue work parents before failed available}
    (prior : State.HealthyCounterAccounting queue work parents before failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.eventsStarted available queue events = true)
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          GraphEvent.taskFailure occurrence errors ∈ events
          → (occurrence, errors) ∈ available)
    : (queue.replayGraphEvents events available).HealthyCounterAccounting work parents
        (before ++ events) failed := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨validBefore, source, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true ∧
          State.eventsStarted available
            (queue.dispatchGraphEvent event available).1 rest = true := by
        simpa only [State.eventsStarted, Bool.and_eq_true] using accepted
      have next := prior.dispatchGraphEvent_inInventory generated canonical validBefore event
        source fresh accepts.1 available recorded (by
          intro occurrence errors same
          exact notified _ _ (same ▸ List.mem_cons_self))
      have retained := ih next (by simpa [List.append_assoc] using valid) accepts.2
        (fun _ _ member => notified _ _ (List.mem_cons_of_mem _ member))
      simpa [State.replayGraphEvents, List.append_assoc] using retained

/-- Initially eligible task callbacks retain exact healthy counters after retirement.
The original queue and full availability snapshot remain fixed throughout the FIFO fold.
-/
theorem State.HealthyCounterAccounting.replayGraphEvents_admitted
    {queue work parents before failed available}
    (prior : State.HealthyCounterAccounting queue work parents before failed)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : State.acceptsBatch.go (fun _ => false) available queue events = true)
    (recorded
      : ∀ occurrence errors, (occurrence, errors) ∈ available → occurrence ∈ failed)
    (notified
      : ∀ occurrence errors,
          GraphEvent.taskFailure occurrence errors ∈ events
          → (occurrence, errors) ∈ available)
    : (queue.replayGraphEvents events available).HealthyCounterAccounting work parents
        (before ++ events) failed := by
  apply prefix_invariant events
    (fun fifo =>
      (queue.replayGraphEvents fifo available).HealthyCounterAccounting work parents
        (before ++ fifo) failed)
  · simpa only [State.replayGraphEvents, List.foldl_nil, List.append_nil] using prior
  · intro fifo event rest split past
    have boundary : (before ++ fifo ++ [event]).IsPrefix (before ++ events) :=
      ⟨rest, by simp [split, List.append_assoc]⟩
    obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix boundary)
    have current := past fifo (List.prefix_refl _)
    have tracked : ∀ occurrence result, event = .taskSuccess occurrence result
        → (queue.replayGraphEvents fifo available).StartedTaskDisposition occurrence := by
      intro occurrence result same
      subst event
      obtain ⟨seen, seenPrefix, eligible⟩ := queue.acceptsBatch_go_eachAccepted events fifo
        (.taskSuccess occurrence result) available accepted ⟨rest, by simp [split]⟩
      have frame := past seen seenPrefix
      cases found : (queue.replayGraphEvents seen available).taskNode? occurrence with
      | none =>
          simp only [State.acceptsGraphEvent, found, Option.isSome_none, Bool.false_eq_true]
            at eligible
      | some node =>
          obtain ⟨remaining, history⟩ := seenPrefix
          have disposition := frame.pending.startedTaskDisposition_atPrefix found frame.producers
            frame.producerOrder remaining (by simpa [history, List.append_assoc] using validBefore) available
          rw [← history, State.replayGraphEvents_append queue seen remaining available]
          exact disposition
    have next := current.dispatchGraphEvent_inInventory_ofDisposition generated canonical
      validBefore event matching fresh available recorded
      (by intro occurrence errors same
          exact notified _ _ (same ▸ by simp [split])) tracked
    simpa only [State.replayGraphEvents_append, State.replayGraphEvents,
      List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_assoc]
      using next

/-- An accepted batch preserves healthy exactness through its termination check.
Witness: sequential event replay, followed by the control-only flag update.
-/
theorem State.HealthyCounterAccounting.handleGraphEvents {queue work parents before}
    (prior
      : State.HealthyCounterAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.HealthyCounterAccounting work parents
        (before ++ events) (GraphEvent.failureSettlements (before ++ events)) := by
  let failed := GraphEvent.failureSettlements (before ++ events)
  let available := GraphEvent.availableFailures events
  have included : (GraphEvent.failureSettlements before).Subset failed := by
    dsimp only [failed]
    rw [GraphEvent.failureSettlements_append_list]
    exact List.subset_append_right _ _
  have enlarged := prior.weakenFailures included
  have recorded : ∀ occurrence errors,
      (occurrence, errors) ∈ available → occurrence ∈ failed := by
    intro occurrence errors member
    obtain ⟨event, inEvents, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure _ _, List.mem_append_right before inEvents,
      by simp [GraphEvent.groupFailures]⟩
  have accounted := enlarged.replayGraphEvents_admitted generated canonical events valid
    accepted recorded (by
      intro occurrence errors member
      exact List.mem_filterMap.mpr ⟨.taskFailure occurrence errors, member, rfl⟩)
  obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
  rw [same]
  exact accounted.withTerminated terminal

/-- Normalized replay preserves healthy counters for every accepted valid source prefix.
Witness: batch induction follows the actual state fold; publisher normalization does not
mutate queue accounting or its canonical group records.
-/
theorem State.HealthyCounterAccounting.runNormalized {queue work parents before}
    (prior
      : State.HealthyCounterAccounting queue work parents before
          (GraphEvent.failureSettlements before))
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.HealthyCounterAccounting work parents
        (before ++ batches.flatten)
        (GraphEvent.failureSettlements (before ++ batches.flatten)) := by
  rw [State.runNormalized_replayBatches]
  induction batches generalizing queue before with
  | nil => simpa [State.replayBatches] using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ :=
        queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have retained := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa only [State.replayBatches, List.foldl_cons, List.flatten_cons,
        List.append_assoc]
        using retained

/-- Generated valid started replays retain exact counters on all uninvalidated groups.
Witness: execution supplies the canonical ancestry assignment, and the joint induction
derives both healthy exactness and all-group bounds from the empty source prefix.
-/
theorem ExecutedWork.runNormalized_healthyCounterLedger {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ parents,
        ((State.initialize (Work.fromExecution work)).runNormalized
          batches).1.HealthyCounterAccounting
          work parents batches.flatten
          (GraphEvent.failureSettlements batches.flatten) := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, ?_⟩
  exact (createWorkQueue_healthyCounterAccounting work parents canonical
          generated.declarations).runNormalized
    (before := []) generated canonical batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
