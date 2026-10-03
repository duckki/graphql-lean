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
private theorem groupSettlement_source {events : List GraphEvent}
    {occurrence : Occurrence} (settled : occurrence ∈ GraphEvent.groupSettlements events)
    : ∃ result, GraphEvent.taskSuccess occurrence result ∈ events := by
  obtain ⟨event, member, contains⟩ := List.mem_flatMap.mp (List.mem_reverse.mp settled)
  cases event with
  | taskSuccess task result =>
      have same : occurrence = task := List.mem_singleton.mp contains
      exact ⟨result, same.symm ▸ member⟩
  | taskFailure | streamItems | streamSuccess | streamFailure => cases contains

/-- Every registered contributor to a healthy retired group has already succeeded.
Witness: generated replay derives the success-only owner ledger. Accepted/full-source
failure-closure equivalence transfers health; an unsettled contributor would require a
live owner, contradicting retirement. The resulting token names an actual source event.
-/
theorem ExecutedWork.replayGraphEvents_retiredContributor_succeeded
    {work events ref task} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
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
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            (before ++ [event])).tasks)
    (contributes : group.ref ∈ task.groups.map Execution.DeliveryNode.ref)
    : ∃ result, GraphEvent.taskSuccess task.occurrence result ∈ before ++ [event] := by
  obtain ⟨_, _, retired, healthy, _⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy valid
      (State.acceptsBatch_prefix started) carrier
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
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
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
    : ∃ before event after result,
        batches.flatten = before ++ event :: after
        ∧ Execution.WorkQueueEvent.groupSuccess group groups streams
          ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
                before).handleGraphEvent
              event).2
        ∧ GraphEvent.taskSuccess (.executionGroup address) result
          ∈ before ++ [event] := by
  obtain ⟨before, event, after, same, emitted⟩ :=
    createWorkQueue_runNormalized_groupSuccess_origin batches started carrier
  have earlier : (before ++ [event]).IsPrefix batches.flatten :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted := (State.initialize (Work.fromExecution work)).batchesStarted_acceptsBatch batches
    (by rwa [← inputsStarted_eq_batchesStarted])
  have prefixStarted
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event]) = true := by
    apply State.acceptsBatch_prefix (after := after)
    simpa only [List.append_assoc, List.singleton_append, ← same] using accepted
  obtain ⟨result, supplied⟩ := generated.successfulCarrier_rootContributor_succeeded
    (valid.prefix earlier) prefixStarted emitted known contributes
  exact ⟨before, event, after, result, same, emitted, supplied⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
