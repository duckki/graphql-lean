import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseOwners
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthStability

/-! A stream's successfully retired dependency remains usable at later source prefixes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful retirement is a durable boundary, not a repeatedly assumed live guard
-----------------------------------------------------------------------------------------

/-- Every later source handler preserves a previously retired group.
Witness: induction through the actual state fold using per-handler retirement preservation.
-/
theorem State.RetiredGroup.replayGraphEvents {queue : State} {key}
    (retired : queue.RetiredGroup key) (received : List GraphEvent)
    : (queue.replayGraphEvents received).RetiredGroup key := by
  induction received generalizing queue with
  | nil => exact retired
  | cons event rest ih => exact ih (retired.handleGraphEvent event)

/-- A group retired uncancelled at an earlier prefix is historically healthy later.
Witness: earlier replay supplies record health, started continuation preserves it, and
permanent registration exposes its region. Mixed causal reflection then excludes the
supplied historical failure. Only earlier successful-item safety remains inductive.
No health or uncancelledness premise is repeated at the later source boundary.
-/
theorem ExecutedWork.replayGraphEvents_retiredGroupHealthy_after_prefix
    {work received before matching events failures node dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (known : NodeAt work node .group dependencies producer)
    (earlier : before.IsPrefix received)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RetiredGroup
          node.key)
    (uncancelled
      : node.key
        ∉ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).cancelledGroups)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence
            ∈ (State.initialize (Work.fromExecution work)).objectFailureContributions
                received)
    (itemsSafe
      : ∀ source index,
          Occurrence.item source index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item source index))
    : ¬NodeFailed work matching events failures node.key := by
  have priorStarted : (State.initialize (Work.fromExecution work)).acceptsBatch before = true := by
    obtain ⟨after, same⟩ := earlier
    exact State.acceptsBatch_prefix (same ▸ started)
  have record := groupRecordAt_of_nodeAt known
  have prior := (generated.replayGraphEvents_retiredHealth before (valid.prefix earlier)
    priorStarted).1 node dependencies record retired uncancelled
  have durable := generated.retiredRecord_health_stable valid started record earlier retired prior
  have later : ((State.initialize (Work.fromExecution work)).replayGraphEvents
      received).RetiredGroup node.key := by
    obtain ⟨after, same⟩ := earlier
    rw [← same, State.replayGraphEvents, List.foldl_append]
    exact retired.replayGraphEvents after
  intro failure
  have exposed := (createWorkQueue_replay_regionInventory valid).registered_exposed later.1
  have invalid := generated.exposed_groupFailure_invalidated valid known exposed failedPayloads
    itemsSafe failure
  exact durable (invalid.toRecordInvalidated.restrict_objectFailures generated record
    objectsRecorded)

-----------------------------------------------------------------------------------------
-- Object-produced streams reuse the earlier retirement at every later item boundary
-----------------------------------------------------------------------------------------

/-- A previously retired contributing dependency protects a stream and its object producer.
Witness: exact stream/producer ownership locates the contributing group; durable retirement
supplies its historical health and the mixed stream bridge discharges both guards.
The earlier boundary may precede arbitrary further matched, started source events.
-/
theorem ExecutedWork.replayGraphEvents_objectStreamHealthy_after_retirement
    {work received before matching events failures stream dependencies source key}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (settled : Occurrence.executionGroup source ∈ received.flatMap GraphEvent.successes)
    (member : key ∈ dependencies) (earlier : before.IsPrefix received)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).RetiredGroup
          key)
    (uncancelled
      : key
        ∉ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).cancelledGroups)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (objectsRecorded
      : ∀ occurrence owners producer path result,
          TaskAt work occurrence owners producer (.object path result)
          → occurrence ∈ failedBefore failures events.length
          → occurrence
            ∈ (State.initialize (Work.fromExecution work)).objectFailureContributions
                received)
    (itemsSafe
      : ∀ address index,
          Occurrence.item address index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item address index))
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.key ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.key := by
  obtain ⟨ancestor, path, result, producer⟩ := NodeAt.stream_objectProducer_owners known
  obtain ⟨group, groupDependencies, descriptor, same⟩ :=
    TaskAt.executionGroup_owner producer member
  have healthy := generated.replayGraphEvents_retiredGroupHealthy_after_prefix valid started
    descriptor earlier (same.symm ▸ retired) (same.symm ▸ uncancelled)
    failedPayloads objectsRecorded itemsSafe
  exact generated.objectProducedStream_healthy_of_dependency valid known settled member
    failedPayloads itemsSafe (same ▸ healthy) contributors

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
