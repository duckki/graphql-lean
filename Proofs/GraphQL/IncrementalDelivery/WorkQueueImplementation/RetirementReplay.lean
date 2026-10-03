import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetirementHandlers

/-! Joint owner accounting and retired ancestry from generated source histories. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Owner existence and retired ancestry discharge each other's local obligations
-----------------------------------------------------------------------------------------

/-- Internal replay evidence combining owner accounting and retired-ancestor certificates.
`events` determines the exact settlement ledgers; no queue-state field or source law is added.
-/
structure State.OwnerAncestry (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (events : List GraphEvent)
    : Prop where
  accounting : queue.OwnerAccounting work parents events
  roots : queue.RootAncestorsRetired work
  retired : queue.HealthyRetiredAncestors work (GraphEvent.failureSettlements events)

/-- Initial generated work establishes owner accounting and both ancestry certificates.
Witness: covered lowering, ancestor-free initial candidates, and no preexisting retirement.
-/
theorem ExecutedWork.initialOwnerAncestry {work : Execution.Work}
    (generated : ExecutedWork work) (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (State.initialize (Work.fromExecution work)).OwnerAncestry work parents [] :=
  ⟨
    createWorkQueue_ownerAccounting work parents canonical,
    generated.initialRootAncestorsRetired,
    createWorkQueue_healthyRetiredAncestors generated
  ⟩

/-- One accepted source event preserves the joint invariant with only stream availability
supplied separately. Witness: retired ancestry derives task-child availability; exact
owner accounting and full-handler retirement preservation then advance together.
-/
theorem State.OwnerAncestry.handleGraphEvent {queue : State}
    {work parents before} (prior : queue.OwnerAncestry work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work before) (event : GraphEvent)
    (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (streamAvailable
      : ∀ stream items,
          event = .streamItems stream items
          → queue.StreamRegistrationsAvailable work (GraphEvent.failureSettlements before)
              items)
    : (queue.handleGraphEvent event).1.OwnerAncestry work parents
        (before ++ [event]) := by
  have available : queue.RegistrationsAvailable work
      (GraphEvent.failureSettlements before) event := by
    cases event with
    | taskSuccess occurrence result =>
        exact prior.accounting.taskSuccess_available generated prior.retired matching fresh
          accepted
    | streamItems stream items => exact streamAvailable stream items rfl
    | taskFailure | streamSuccess | streamFailure => trivial
  have next := prior.accounting.handleGraphEvent canonical generated valid event matching fresh
    accepted available
  have subset : (GraphEvent.failureSettlements before).Subset
      (GraphEvent.failureSettlements (before ++ [event])) := by
    rw [GraphEvent.failureSettlements_append]
    exact fun _ member => List.mem_append_right _ member
  have retired := prior.retired.mono_failures subset
  have supported := prior.accounting.supported.weaken subset
  have cancelled := prior.accounting.cancelled.weaken subset
  have certificates : (queue.handleGraphEvent event).1.RootAncestorsRetired work
      ∧ (queue.handleGraphEvent event).1.HealthyRetiredAncestors work
          (GraphEvent.failureSettlements (before ++ [event])) := by
    cases event with
    | taskSuccess occurrence result =>
        exact State.taskSuccess_retirement prior.roots retired generated prior.accounting.groups
          prior.accounting.links canonical prior.accounting.pending.liveGroups
          prior.accounting.pending.taskGroups supported cancelled matching
    | taskFailure occurrence errors =>
        exact ⟨
          prior.roots.taskFailure occurrence errors,
          retired.taskFailure prior.accounting.links prior.accounting.groups canonical
            prior.accounting.pending.started prior.accounting.pending.matching occurrence
            errors
            (by simp [GraphEvent.failureSettlements_append, GraphEvent.groupFailures])
        ⟩
    | streamItems stream items =>
        exact State.streamItems_retirement prior.roots retired prior.accounting.pending.refs
          generated prior.accounting.groups prior.accounting.links canonical
          prior.accounting.pending.liveGroups prior.accounting.pending.taskGroups supported
          cancelled matching
    | streamSuccess stream =>
        simp only [State.handleGraphEvent, State.streamSuccess]
        split <;> exact ⟨prior.roots, retired⟩
    | streamFailure stream errors =>
        simp only [State.handleGraphEvent, State.streamFailure]
        split <;> exact ⟨prior.roots, retired⟩
  exact ⟨next, certificates.1, certificates.2⟩

-----------------------------------------------------------------------------------------
-- Generated replay supplies stream availability at every actual earlier state
-----------------------------------------------------------------------------------------

/-- Healthy owner existence and retired ancestry follow from generated legal started replay.
Witness: induction on source-event validity; region separation derives sequential stream
availability, while the current retirement certificate derives object-task availability.
Neither availability nor active-root health is an additional premise.
-/
theorem ExecutedWork.replayGraphEvents_ownerAncestry {work : Execution.Work}
    (generated : ExecutedWork work) (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    {events : List GraphEvent} (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).acceptsGraphEvent
              event
            = true)
    : ((State.initialize (Work.fromExecution work)).replayGraphEvents
        events).OwnerAncestry
        work parents events := by
  induction valid with
  | nil => exact generated.initialOwnerAncestry parents canonical
  | @append before event validBefore matching fresh ready ih =>
      have earlier := ih (fun past next included =>
        acceptedAt past next (included.trans (List.prefix_append before [event])))
      rw [State.replayGraphEvents_append]
      apply earlier.handleGraphEvent generated canonical validBefore event matching fresh
        (acceptedAt before event (List.prefix_refl _))
      intro stream items same
      subst event
      exact createWorkQueue_replay_streamRegistrationsAvailable generated validBefore
        matching fresh

/-- Changing the terminal flag preserves all owner and ancestor evidence.
Witness: none of these internal certificates inspect batch-control state.
-/
theorem State.OwnerAncestry.withTerminated {queue : State} {work parents events}
    (prior : queue.OwnerAncestry work parents events) (terminated : Bool)
    : ({queue with terminated := terminated}).OwnerAncestry work parents events :=
  ⟨prior.accounting.withTerminated terminated, prior.roots, prior.retired⟩

/-- Normalized generated replay retains healthy owners without any availability premise.
Witness: the input start checker licenses each replay step, joint ancestry/owner induction
derives integration availability, and normalization changes only the final terminal flag.
This proves internal accounting, not yet output admission or full implementation conformance.
-/
theorem ExecutedWork.runNormalized_ownerAncestry {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.OwnerAncestry
            work parents batches.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replayed := generated.replayGraphEvents_ownerAncestry parents canonical valid
    (inputsStarted_eachAccepted work batches started)
  obtain ⟨terminated, same⟩ := createWorkQueue_runNormalized_stateCore started
  refine ⟨parents, canonical, ?_⟩
  rw [same]
  exact replayed.withTerminated terminated

/-- Both combined-outcome and success-only healthy ownership follow from source laws.
Witness: project the unconditional normalized owner/ancestry theorem and its ledger bridge.
-/
theorem ExecutedWork.runNormalized_healthyRegisteredOwners {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
      queue.HealthyRegisteredTaskAccounting work
        (GraphEvent.taskSettlements batches.flatten)
        (GraphEvent.failureSettlements batches.flatten)
      ∧ queue.HealthyRegisteredTaskAccounting work
          (GraphEvent.groupSettlements batches.flatten)
          (GraphEvent.failureSettlements batches.flatten) := by
  obtain ⟨_, _, replayed⟩ := generated.runNormalized_ownerAncestry batches valid started
  exact ⟨replayed.accounting.owners, replayed.accounting.healthyRegisteredTasks⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
