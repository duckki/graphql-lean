import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulReleaseReplay

/-! Successful group carriers have no unsettled registered contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Healthy retirement identifies an actual successful source settlement
-----------------------------------------------------------------------------------------

/-- A success-ledger token has an actual task-success event in that same source prefix.
Witness: reverse/flat-map membership and the object-only settlement projection.
-/
theorem groupSettlement_source {events : List GraphEvent}
    {occurrence : Occurrence} (settled : occurrence ∈ GraphEvent.groupSettlements events)
    : ∃ result, GraphEvent.taskSuccess occurrence result ∈ events := by
  obtain ⟨event, member, contains⟩ := List.mem_flatMap.mp (List.mem_reverse.mp settled)
  cases event with
  | taskSuccess task result =>
      have same : occurrence = task := List.mem_singleton.mp contains
      exact ⟨result, same.symm ▸ member⟩
  | taskFailure | groupFailure | streamItems | streamSuccess | streamFailure =>
      cases contains

/-- Every registered contributor to a healthy retired group has already succeeded.
Witness: generated replay derives the success-only owner ledger. Accepted/full-source
failure-closure equivalence transfers health; an unsettled contributor would require a
live owner, contradicting retirement. The resulting token names an actual source event.
-/
theorem ExecutedWork.replayGraphEvents_retiredContributor_succeeded
    {work events ref task} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks)
    (contributes : ref ∈ task.groups.map Execution.DeliveryNode.ref)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).RetiredGroup
          ref)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          ref)
    : ∃ result, GraphEvent.taskSuccess task.occurrence result ∈ events := by
  obtain ⟨_, _, ledger⟩ :=
    generated.replayGraphEvents_ownerAccounting_of_started events valid started
  have sourceHealthy : ¬GroupInvalidated work (GraphEvent.failureSettlements events) ref := by
    intro failed
    exact healthy ((generated.failureInventories_groupInvalidated_iff events valid started
      ref).mp failed).toRecordInvalidated
  exact groupSettlement_source
    (ledger.healthyRegisteredTasks.retired_contributor_settled registered contributes
      sourceHealthy retired)

/-- A successful carrier's registered contributors succeeded by that handler boundary.
Witness: actual successful closure supplies healthy retirement; replay's derived owner
ledger then excludes every still-unsettled contributor. This is a source-settlement fact,
not yet proof that its value was published before the particular output atom.
-/
theorem ExecutedWork.successfulCarrier_registeredContributor_succeeded
    {work before event group groups streams task} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work))
          (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2.1)
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            (before ++ [event])).tasks)
    (contributes : group.ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : ∃ result, GraphEvent.taskSuccess task.occurrence result ∈ before ++ [event] := by
  obtain ⟨_, _, retired, healthy, _⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy valid
      (State.eventsStarted_prefix started) carrier
  exact generated.replayGraphEvents_retiredContributor_succeeded valid started registered
    contributes retired healthy

-----------------------------------------------------------------------------------------
-- Root work has unconditional coverage, without a supplied registration witness
-----------------------------------------------------------------------------------------

/-- Every producer-free contributor to an actual successful carrier has already succeeded.
Witness: inverse lowering registers every root task, registry persistence carries it to
the closure handler, and healthy retirement forces its successful source settlement.
The statement does not assume task registration, a pending-counter invariant, or output
admission as an additional source premise.
-/
theorem ExecutedWork.successfulCarrier_rootContributor_succeeded
    {work before event group groups streams address owners payload}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work))
          (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2.1)
    (known : TaskAt work (.executionGroup address) owners none payload)
    (contributes : group.ref ∈ owners)
    : ∃ result,
        GraphEvent.taskSuccess (.executionGroup address) result ∈ before ++ [event] := by
  obtain ⟨task, registered, occurrence, groups⟩ :=
    TaskAt.executionGroup_replay_registered known (before ++ [event])
  obtain ⟨result, supplied⟩ := generated.successfulCarrier_registeredContributor_succeeded
    valid started carrier registered (groups.symm ▸ contributes)
  exact ⟨result, occurrence ▸ supplied⟩

/-- A normalized successful carrier's root contributors succeeded no later than its source
handler. Witness: recover the actual producing handler and its accepted source prefix;
apply root registration/settlement coverage at that boundary, regardless of host batching.
Later source events are not used to justify an earlier closure.
-/
theorem ExecutedWork.runNormalized_successfulCarrier_rootContributor_prefix
    {work batches group groups streams address owners payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    (known : TaskAt work (.executionGroup address) owners none payload)
    (contributes : group.ref ∈ owners)
    : ∃ earlier batch later fifo event after result,
        batches = earlier ++ batch :: later
        ∧ batch = fifo ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ ((((State.initialize (Work.fromExecution work)).replayBatches
                earlier).replayGraphEvents
                fifo (GraphEvent.availableFailures batch)).handleGraphEvent
              event (GraphEvent.availableFailures batch)).2.1
        ∧ GraphEvent.taskSuccess (.executionGroup address) result
          ∈ earlier.flatten ++ (fifo ++ [event]) := by
  obtain ⟨earlier, batch, later, fifo, event, after, partition, within, emitted⟩ :=
    createWorkQueue_runNormalized_groupSuccess_origin batches started carrier
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have sourceValid : ValidGraphEvents work (earlier ++ batch :: later).flatten :=
    partition ▸ valid
  have sourceStarted : inputsStarted work (earlier ++ batch :: later) = true :=
    partition ▸ started
  have before := generated.uncancelledFrame_atBatchPrefix canonical earlier batch later fifo
    sourceValid sourceStarted ⟨event :: after, within.symm⟩
  have next := generated.uncancelledFrame_atBatchPrefix canonical earlier batch later
    (fifo ++ [event]) sourceValid sourceStarted ⟨after, by
      simp only [List.append_assoc, List.singleton_append, within]⟩
  have matching : event.MatchesWork work := by
    apply sourceValid.eachMatches
    simp only [List.flatten_append, List.flatten_cons]
    apply List.mem_append_right
    apply List.mem_append_left
    rw [within]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨_, _, retired⟩ := State.handleGraphEvent_successfulRetirements before.parent
    before.cancellations generated canonical event matching (GraphEvent.availableFailures batch)
      group groups streams emitted
  obtain ⟨task, initialMember, sameOccurrence, sameOwners⟩ :=
    TaskAt.executionGroup_initial_registered known
  let initial := State.initialize (Work.fromExecution work)
  have registered := (initial.replayBatches earlier).replayGraphEvents_tasks_subset
    (fifo ++ [event]) (GraphEvent.availableFailures batch)
    (initial.replayBatches_tasks_subset earlier initialMember)
  rw [State.replayGraphEvents_append _ _ _ (GraphEvent.availableFailures batch)] at next registered
  have settled := next.owners.retired_contributor_settled registered (sameOwners.symm ▸ contributes)
    retired.uncancelled retired.retired
  obtain ⟨result, supplied⟩ := groupSettlement_source settled
  exact ⟨earlier, batch, later, fifo, event, after, result, partition, within, emitted,
    sameOccurrence ▸ supplied⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
