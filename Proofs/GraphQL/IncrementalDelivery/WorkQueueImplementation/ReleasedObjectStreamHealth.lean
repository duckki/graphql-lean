import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulReleaseReplay

/-! Actual stream release discharges the mixed object-stream proof's queue-side premises. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Actual release supplies both successful producer input and healthy contributing support
-----------------------------------------------------------------------------------------

/-- A group-carried stream's producer has an actual successful source settlement.
Witness: the existing joint release inventory places that producer before its carrier;
the inventory's source provenance identifies the corresponding task-success input.
No equality of response data is used to choose a producer occurrence.
-/
theorem ExecutedWork.runNormalized_releasedStreamProducer_succeeded
    {work batches group groups streams stream dependencies producer}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    (released : stream ∈ streams)
    (known : NodeAt work stream .stream dependencies producer)
    : ∃ occurrence,
        producer = some occurrence
        ∧ occurrence ∈ batches.flatten.flatMap GraphEvent.successes := by
  obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp carrier
  obtain ⟨published, _, inventory, support⟩ :=
    createWorkQueue_runNormalized_streamReleasePublications generated valid
  obtain ⟨occurrence, same, member⟩ := support index group groups streams atEvent stream
    released dependencies producer known
  obtain ⟨entry, earlier, equal⟩ := List.mem_map.mp member
  obtain ⟨result, source, _⟩ := inventory.provenance entry (List.mem_of_mem_take earlier)
  refine ⟨occurrence, same, ?_⟩
  exact List.mem_flatMap.mpr
    ⟨_, source, by simpa only [GraphEvent.successes, List.mem_singleton] using equal.symm⟩

/-- An actually released object-produced stream has healthy producer and stream guards.
Witness: release provenance supplies successful settlement; carrier replay supplies a
retired uncancelled contributing owner, including through later failures. The existing
mixed causal bridge then needs only cut alignment, real failed payloads, no direct stream
failure, and safety of earlier successful items. No queue-side health premise remains.
-/
theorem ExecutedWork.runNormalized_releasedObjectStreamHealthy_of_itemSafety
    {work batches matching events failures group groups streams stream dependencies
      source}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten)
    (released : stream ∈ streams)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
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
            ∈ (State.initialize
                (Work.fromExecution work)).admittedObjectFailureContributionsForBatches
                batches)
    (itemsSafe
      : ∀ address index,
          Occurrence.item address index ∈ batches.flatten.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item address index))
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.ref := by
  obtain ⟨occurrence, same, settled⟩ := generated.runNormalized_releasedStreamProducer_succeeded
    valid carrier released known
  cases Option.some.inj same
  have support := generated.runNormalized_streamHealthyDependency valid started carrier
    released known
  obtain ⟨ancestor, path, result, producer⟩ := NodeAt.stream_objectProducer_owners known
  obtain ⟨owner, ownerDependencies, descriptor, sameRef⟩ :=
    TaskAt.executionGroup_owner producer support.1
  have retired := sameRef.symm ▸ support.2.1
  have uncancelled := sameRef.symm ▸ support.2.2
  have healthy : ¬NodeFailed work matching events failures owner.ref := by
    intro failure
    have exposed := (createWorkQueue_runNormalized_regionInventory valid).registered_exposed
      retired.1
    have invalid := generated.exposed_groupFailure_invalidated valid descriptor exposed
      failedPayloads itemsSafe failure
    have recorded := invalid.toRecordInvalidated.restrict_objectFailures generated
      (groupRecordAt_of_nodeAt descriptor) objectsRecorded
    exact (generated.runNormalized_retiredHealth batches valid started).1 owner ownerDependencies
      (groupRecordAt_of_nodeAt descriptor) retired uncancelled recorded
  exact generated.objectProducedStream_healthy_of_dependency valid known settled support.1
    failedPayloads itemsSafe (sameRef ▸ healthy) contributors

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
