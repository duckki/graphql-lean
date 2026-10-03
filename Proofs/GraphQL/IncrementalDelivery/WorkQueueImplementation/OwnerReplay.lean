import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OwnerAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAvailability

/-! Conditional healthy-owner replay, without an active-root health assumption. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Internal replay evidence for safe counters, exact healthy counts, and live owners.
`events` fixes the observed success/failure ledgers; `parents` is the source's canonical
defer ancestry. This proof bundle is not queue state or a premise of public conformance.
-/
structure State.OwnerAccounting (queue : State) (work : Execution.Work)
    (parents : Nat → NodeRefs) (events : List GraphEvent)
    : Prop
    extends queue.HealthyCounterAccounting work parents events where
  owners
    : queue.HealthyRegisteredTaskAccounting work (GraphEvent.taskSettlements events)
        (GraphEvent.failureSettlements events)
  links : queue.ChildLinksCanonical parents

/-- Initial lowering establishes the combined owner replay evidence.
Witness: immediate contributor coverage and the independently checked count/cache/metadata
initializers. Canonical ancestry is structural source evidence, not an execution policy.
-/
theorem createWorkQueue_ownerAccounting (work : Execution.Work) (parents : Nat → NodeRefs)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    : (State.initialize (Work.fromExecution work)).OwnerAccounting work parents [] := by
  exact ⟨createWorkQueue_healthyCounterAccounting work parents canonical,
    createWorkQueue_healthyRegisteredTaskAccounting
    work,
    createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
      (fun _ member => workFromSpec_groups_parentCanonical (Located.root (root := work))
        canonical member)⟩

/-- One source event updates all owner-replay evidence together.
Witness: all-outcome counter bounds, conditional owner preservation, cache provenance, and
canonical metadata each follow the executable handler. Only integration availability
remains conditional; no output-history admission or active-root health is assumed.
-/
theorem State.OwnerAccounting.handleGraphEvent {queue : State} {work : Execution.Work}
    {parents : Nat → NodeRefs} {before : List GraphEvent}
    (prior : queue.OwnerAccounting work parents before)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    (accepted : queue.acceptsGraphEvent event = true)
    (available
      : queue.RegistrationsAvailable work (GraphEvent.failureSettlements before) event)
    : (queue.handleGraphEvent event).1.OwnerAccounting work parents
        (before ++ [event]) := by
  exact ⟨
    prior.toHealthyCounterAccounting.handleGraphEvent generated canonical valid event
      matching fresh accepted,
    prior.owners.handleGraphEvent_ofPendingAccounting prior.pending prior.supported
      prior.cancelled prior.links prior.groups canonical generated valid event matching
      fresh accepted available,
    prior.links.handleGraphEvent event matching canonical
  ⟩

/-- The executable batch start check licenses every event at its actual replay state.
Witness: peel preceding accepted handlers from the recursive Boolean check.
-/
theorem State.acceptsBatch_atPrefix (queue : State) (before : List GraphEvent)
    (event : GraphEvent) (after : List GraphEvent)
    (accepted : queue.acceptsBatch (before ++ event :: after) = true)
    : (queue.replayGraphEvents before).acceptsGraphEvent event = true := by
  induction before generalizing queue with
  | nil =>
      have both : queue.acceptsGraphEvent event = true
          ∧ (queue.handleGraphEvent event).1.acceptsBatch after = true := by
        simpa [State.acceptsBatch] using accepted
      exact both.1
  | cons head tail ih =>
      have both : queue.acceptsGraphEvent head = true
          ∧ (queue.handleGraphEvent head).1.acceptsBatch (tail ++ event :: after) = true := by
        simpa [State.acceptsBatch] using accepted
      exact ih (queue.handleGraphEvent head).1 both.2

/-- Owner accounting composes along any valid accepted finite event history whose
integrations have available contributors. Witness: induction over source-event validity,
using each actual earlier replay state rather than a selected schedule or wire admission.
-/
theorem State.OwnerAccounting.replayGraphEvents
    {queue : State} {work : Execution.Work} {parents : Nat → NodeRefs}
    (initial : queue.OwnerAccounting work parents [])
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (generated : ExecutedWork work) {events : List GraphEvent}
    (valid : ValidGraphEvents work events)
    (acceptedAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → (queue.replayGraphEvents before).acceptsGraphEvent event = true)
    (availableAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → (queue.replayGraphEvents before).RegistrationsAvailable work
              (GraphEvent.failureSettlements before) event)
    : (queue.replayGraphEvents events).OwnerAccounting work parents events := by
  induction valid with
  | nil => exact initial
  | @append before event prior matching fresh ready ih =>
      have included := List.prefix_append before [event]
      have earlier := ih
        (fun past next prefixOfBefore => acceptedAt past next (prefixOfBefore.trans included))
        (fun past next prefixOfBefore => availableAt past next (prefixOfBefore.trans included))
      rw [State.replayGraphEvents_append]
      exact earlier.handleGraphEvent canonical generated prior event matching fresh
        (acceptedAt before event (List.prefix_refl _))
        (availableAt before event (List.prefix_refl _))

/-- Generated replay needs no extra root-health premise to retain healthy registered owners.
Witness: generated canonical ancestry, initial lowering, and the conditional replay theorem.
Contributor availability is explicitly retained as the remaining internal proof obligation.
-/
theorem ExecutedWork.replayGraphEvents_ownerAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (events : List GraphEvent)
    (valid : ValidGraphEvents work events)
    (accepted : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (availableAt
      : ∀ before event,
          (before ++ [event]).IsPrefix events
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).RegistrationsAvailable
              work (GraphEvent.failureSettlements before) event)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            events).OwnerAccounting
            work parents events := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  refine ⟨parents, canonical,
    (createWorkQueue_ownerAccounting work parents canonical).replayGraphEvents
      canonical generated valid ?_ availableAt⟩
  intro before event earlier
  obtain ⟨after, same⟩ := earlier
  have acceptedPrefix : (State.initialize (Work.fromExecution work)).acceptsBatch
      (before ++ event :: after) = true := by
    simpa only [← same, List.append_assoc, List.singleton_append] using accepted
  exact State.acceptsBatch_atPrefix _ before event after acceptedPrefix

/-- Changing only termination preserves every owner-replay invariant.
Witness: each field concerns task/group bookkeeping, not the batch-control flag.
-/
theorem State.OwnerAccounting.withTerminated {queue : State} {work : Execution.Work}
    {parents : Nat → NodeRefs} {events : List GraphEvent}
    (prior : queue.OwnerAccounting work parents events) (terminated : Bool)
    : ({queue with terminated := terminated}).OwnerAccounting work parents events :=
  ⟨prior.toHealthyCounterAccounting.withTerminated terminated, prior.owners, prior.links⟩

/-- Conditional owner replay applies to the actual normalized queue, including termination.
Witness: started-input checks supply eventwise acceptance, and the batch/state bridge
changes only the final control flag. Availability remains the sole extra replay obligation.
-/
theorem ExecutedWork.runNormalized_ownerAccounting {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (availableAt
      : ∀ before event,
          (before ++ [event]).IsPrefix batches.flatten
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).RegistrationsAvailable
              work (GraphEvent.failureSettlements before) event)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.OwnerAccounting
            work parents batches.flatten := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have replayed := (createWorkQueue_ownerAccounting work parents canonical).replayGraphEvents
    canonical generated valid (inputsStarted_eachAccepted work batches started) availableAt
  obtain ⟨terminated, same⟩ := createWorkQueue_runNormalized_stateCore started
  refine ⟨parents, canonical, ?_⟩
  rw [same]
  exact replayed.withTerminated terminated

/-- The combined ledger recovers healthy registered ownership in success-only coordinates.
Witness: any registered task with a healthy contributor is not a recorded failure, so
absence from successful settlements also implies absence from the combined outcome list.
-/
theorem State.OwnerAccounting.healthyRegisteredTasks {queue : State}
    {work : Execution.Work} {parents : Nat → NodeRefs} {events : List GraphEvent}
    (prior : queue.OwnerAccounting work parents events)
    : queue.HealthyRegisteredTaskAccounting work (GraphEvent.groupSettlements events)
        (GraphEvent.failureSettlements events) := by
  intro task member fresh ref contributor healthy
  have notFailed := (prior.pending.matching task member).not_failed_of_healthy
    contributor healthy
  apply prior.owners task member _ ref contributor healthy
  simp only [GraphEvent.mem_taskSettlements, fresh, notFailed, or_self, not_false_eq_true]

/-- Only object-task integrations remain conditional in normalized owner replay.
Witness: generated stream-region separation discharges every item integration, including
sequential integrations inside one event. The remaining callback is an internal proof
obligation, not an added premise of the public implementation conformance statement.
-/
theorem ExecutedWork.runNormalized_ownerAccounting_of_taskAvailability
    {work : Execution.Work} (generated : ExecutedWork work)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (availableTasks
      : ∀ before occurrence result,
          (before ++ [.taskSuccess occurrence result]).IsPrefix batches.flatten
          → ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).ChildGroupsAvailable
              work (GraphEvent.failureSettlements before) result.work)
    : ∃ parents : Nat → NodeRefs,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.OwnerAccounting
            work parents batches.flatten := by
  apply generated.runNormalized_ownerAccounting batches valid started
  intro before event earlier
  cases event with
  | taskSuccess occurrence result => exact availableTasks before occurrence result earlier
  | streamItems stream items =>
      exact createWorkQueue_replay_streamRegistrationsAvailableAt generated valid
        before stream items earlier
  | taskFailure | streamFailure | streamSuccess => trivial

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
