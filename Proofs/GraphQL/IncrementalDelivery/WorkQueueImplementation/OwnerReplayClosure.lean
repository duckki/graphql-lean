import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledRetirementReplay

/-! Close healthy-owner replay's contributor-availability obligation using retirement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Generated started replay retains healthy owner accounting without an availability
callback. Witness: induction over actual source settlements; the already-proved structural
retirement invariant licenses object-child registration, and stream-region separation
licenses item-child registration. Accounting uses the full source failure ledger here,
not the smaller accepted-failure inventory needed by guard reflection.
-/
theorem ExecutedWork.replayGraphEvents_ownerAccounting_of_eachAccepted
    {work : Execution.Work} (generated : ExecutedWork work) {parents}
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
        events).OwnerAccounting
        work parents events := by
  induction valid with
  | nil => exact createWorkQueue_ownerAccounting work parents canonical
  | @append before event valid matching fresh ready ih =>
      have included := List.prefix_append before [event]
      have earlier := ih (fun past next prefixOfBefore =>
        acceptedAt past next (prefixOfBefore.trans included))
      have accepted := acceptedAt before event (List.prefix_refl _)
      have retirement := (generated.replayGraphEvents_healthyRetiredAncestors before valid
        ).mono_failures
          ((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist before).subset
      have available : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RegistrationsAvailable work (GraphEvent.failureSettlements before) event := by
        cases event with
        | taskSuccess occurrence result =>
            exact earlier.taskSuccess_available generated retirement matching fresh accepted
        | streamItems stream items =>
            exact createWorkQueue_replay_streamRegistrationsAvailableAt generated
              (.append valid matching fresh ready) before stream items (List.prefix_refl _)
        | taskFailure | streamSuccess | streamFailure => trivial
      rw [State.replayGraphEvents_append]
      exact earlier.handleGraphEvent canonical generated valid event matching fresh
        accepted available

/-- A valid accepted source history has the full owner ledger at its actual final state.
Witness: the executable start checker supplies eventwise acceptance; retirement closes
all registration-availability obligations inside the induction.
-/
theorem ExecutedWork.replayGraphEvents_ownerAccounting_of_started
    {work : Execution.Work} (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            events).OwnerAccounting
            work parents events := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, canonical,
    generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical valid ?_⟩
  intro before event earlier
  obtain ⟨after, same⟩ := earlier
  apply State.acceptsBatch_atPrefix _ before event after
  simpa only [← same, List.append_assoc, List.singleton_append] using started

/-- Started normalized replay needs no caller-supplied contributor availability.
Witness: the unconditional eventwise owner induction and the checked termination-only
state correspondence between sequential and normalized replay.
-/
theorem ExecutedWork.runNormalized_ownerAccounting_of_started {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.OwnerAccounting
            work parents batches.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replayed := generated.replayGraphEvents_ownerAccounting_of_eachAccepted
    canonical valid (inputsStarted_eachAccepted work batches started)
  obtain ⟨terminated, same⟩ := createWorkQueue_runNormalized_stateCore started
  refine ⟨parents, canonical, ?_⟩
  rw [same]
  exact replayed.withTerminated terminated

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
