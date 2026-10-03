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
execution-derived ancestry assignment; `events` supplies the settlement and failure
ledgers. All-group accounting is bounded, while only uninvalidated groups are exact.
Cancellation support and canonical child links are derived alongside those counters.
-/
structure State.HealthyCounterAccounting (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (events : List GraphEvent)
    : Prop where
  pending : queue.PendingAccounting work (GraphEvent.taskSettlements events)
  healthy
    : queue.HealthyPendingTracks work (GraphEvent.taskSettlements events)
        (GraphEvent.failureSettlements events)
  supported : queue.CachedFailuresSupported work (GraphEvent.failureSettlements events)
  groups : queue.GroupNodesMatchWork work
  canonical : queue.GroupParentsCanonical parents
  cancelled : queue.CancelledRecordsSupported work (GraphEvent.failureSettlements events)
  childLinks : queue.ChildLinksCanonical parents

/-- The two structural invariants provide the descriptors needed by the health guard.
Witness: the source's canonical dependency assignment identifies each live record's
parent with the first dependency of its contributor-or-ancestor registration record.
-/
theorem State.HealthyCounterAccounting.descriptors {queue work parents events}
    (prior : State.HealthyCounterAccounting queue work parents events)
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
    : (State.initialize (Work.fromExecution work)).HealthyCounterAccounting work parents
        [] :=
  ⟨
    createWorkQueue_pendingAccounting work,
    createWorkQueue_healthyPendingTracks work,
    createWorkQueue_cachedFailuresSupported _ _ _,
    createWorkQueue_groupNodesMatchWork work,
    createWorkQueue_groupParentsCanonical _ parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical (Located.root (root := work))
          canonical member),
    createWorkQueue_cancelledRecordsSupported _ _ _,
    createWorkQueue_childLinksCanonical _ parents
      (fun _ member =>
        workFromSpec_groups_parentCanonical
          (Located.root (root := work)) canonical member)
  ⟩

/-- One accepted valid event preserves exact healthy counters without a root-health law.
Witness: cancellation-aware handler lemmas and independently preserved structural/cache
metadata. Fresh child tasks come from source validity, not from an extra implementation
or output-admission premise.
-/
theorem State.HealthyCounterAccounting.handleGraphEvent {queue work parents before}
    (prior : State.HealthyCounterAccounting queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    : (queue.handleGraphEvent event).1.HealthyCounterAccounting work parents
        (before ++ [event]) := by
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
            apply prior.healthy.taskSuccess_allOutcomes prior.pending prior.supported
              prior.cancelled generated (prior.descriptors canonical) occurrence result
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
    prior.groups prior.childLinks canonical event matching
    (by
      intro occurrence errors same node found healthy
      subst event
      simp [GraphEvent.failureSettlements_append, GraphEvent.groupFailures])
  exact ⟨nextPending, nextHealthy, nextSupport,
    prior.groups.handleGraphEvent event matching,
    prior.canonical.handleGraphEvent event matching canonical,
    nextCancelled, prior.childLinks.handleGraphEvent event matching canonical⟩

-----------------------------------------------------------------------------------------
-- Lift the event invariant to batches and normalized source replay
-----------------------------------------------------------------------------------------

/-- Sequential event replay retains the joint healthy-counter evidence.
Witness: list induction extracts each actual accepted source-prefix extension.
-/
theorem State.HealthyCounterAccounting.replayGraphEvents {queue work parents before}
    (prior : State.HealthyCounterAccounting queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (accepted : queue.acceptsBatch events = true)
    : (queue.replayGraphEvents events).HealthyCounterAccounting work parents
        (before ++ events) := by
  induction events generalizing queue before with
  | nil => simpa [State.replayGraphEvents] using prior
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) :=
        ⟨rest, by simp⟩
      obtain ⟨validBefore, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have accepts : queue.acceptsGraphEvent event = true ∧
          (queue.handleGraphEvent event).1.acceptsBatch rest = true := by
        simpa only [State.acceptsBatch, Bool.and_eq_true] using accepted
      have next := prior.handleGraphEvent generated canonical validBefore event matching
        fresh accepts.1
      have retained := ih next (by simpa [List.append_assoc] using valid) accepts.2
      simpa [State.replayGraphEvents, List.append_assoc] using retained

/-- Setting the terminal flag leaves every counter and metadata invariant unchanged.
Witness: the flag does not occur in any field of the joint proof-side record.
-/
theorem State.HealthyCounterAccounting.withTerminated {queue work parents events}
    (prior : State.HealthyCounterAccounting queue work parents events) (terminated : Bool)
    : ({queue with terminated := terminated}).HealthyCounterAccounting work parents
        events :=
  ⟨
    prior.pending.withTerminated terminated,
    prior.healthy,
    prior.supported,
    prior.groups,
    prior.canonical,
    prior.cancelled,
    prior.childLinks
  ⟩

/-- An accepted batch preserves healthy exactness through its termination check.
Witness: sequential event replay, followed by the control-only flag update.
-/
theorem State.HealthyCounterAccounting.handleGraphEvents {queue work parents before}
    (prior : State.HealthyCounterAccounting queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (running : queue.terminated = false) (accepted : queue.acceptsBatch events = true)
    : (queue.handleGraphEvents events).1.HealthyCounterAccounting work parents
        (before ++ events) := by
  have accounted := prior.replayGraphEvents generated canonical events valid accepted
  unfold State.handleGraphEvents
  simp only [running, Bool.false_eq_true, ↓reduceIte]
  split
  · simpa only [State.foldGraphEvents_state] using accounted.withTerminated true
  · simpa only [State.foldGraphEvents_state] using accounted

/-- Normalized replay preserves healthy counters for every accepted valid source prefix.
Witness: batch induction follows the actual state fold; publisher normalization does not
mutate queue accounting or its canonical group records.
-/
theorem State.HealthyCounterAccounting.runNormalized {queue work parents before}
    (prior : State.HealthyCounterAccounting queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work (before ++ batches.flatten))
    (started : queue.batchesStarted batches = true)
    : (queue.runNormalized batches).1.HealthyCounterAccounting work parents
        (before ++ batches.flatten) := by
  rw [State.runNormalized_stateFold]
  induction batches generalizing queue before with
  | nil => simpa using prior
  | cons batch rest ih =>
      obtain ⟨running, accepted, restStarted⟩ :=
        queue.batchesStarted_cons batch rest started
      have earlier : (before ++ batch).IsPrefix (before ++ (batch :: rest).flatten) :=
        ⟨rest.flatten, by simp [List.append_assoc]⟩
      have next := prior.handleGraphEvents generated canonical batch (valid.prefix earlier)
        running accepted
      have retained := ih next (by simpa [List.append_assoc] using valid) restStarted
      simpa [List.append_assoc] using retained

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
          work parents batches.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, ?_⟩
  exact (createWorkQueue_healthyCounterAccounting work parents canonical).runNormalized
    (before := []) generated canonical batches valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
