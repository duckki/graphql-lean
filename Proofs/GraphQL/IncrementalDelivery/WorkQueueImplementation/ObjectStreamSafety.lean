import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExposedGroupCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamItemSafety
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata

/-! One healthy registered contributor protects an object-produced stream and its producer. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream dependencies are exactly their object producer's contributing owners
-----------------------------------------------------------------------------------------

/-- An object-produced stream's defer dependencies are its producer task's owner list.
Witness: the existing located producer-context theorem; no generated-work or source
assumption is needed. This is exact ownership, not merely an overlapping support ref.
-/
theorem NodeAt.stream_objectProducer_owners {work stream dependencies source}
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    : ∃ ancestor path result,
        TaskAt work (.executionGroup source) dependencies ancestor
          (.object path result) := by
  obtain ⟨address, items, located⟩ := known
  exact Correctness.located_producer_context located

-----------------------------------------------------------------------------------------
-- One healthy dependency discharges both producer and enclosing-owner cancellation
-----------------------------------------------------------------------------------------

/-- One healthy dependency protects an object-produced stream and its successful producer.
Witness: dependencies are the producer's owners. Mixed object cancellation would fail
that owner; original-cut stream causality then excludes producer and dependency failure.
Earlier successful items remain the joint induction hypothesis, not a host-source law.
-/
theorem ExecutedWork.objectProducedStream_healthy_of_dependency
    {work received matching events failures stream dependencies source ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (settled : Occurrence.executionGroup source ∈ received.flatMap GraphEvent.successes)
    (member : ref ∈ dependencies)
    (failedPayloads
      : ∀ cut occurrence,
          (cut, occurrence) ∈ failures
          → ∃ owners producer payload,
              TaskAt work occurrence owners producer payload
              ∧ payload.failure.isSome = true)
    (itemsSafe
      : ∀ address index,
          Occurrence.item address index ∈ received.flatMap GraphEvent.successes
          → ¬TaskCancelled work matching events failures (.item address index))
    (healthy : ¬NodeFailed work matching events failures ref)
    (contributors
      : ∀ occurrence owners,
          TaskHasOwners work occurrence owners
          → stream.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.ref := by
  obtain ⟨ancestor, path, result, producer⟩ := NodeAt.stream_objectProducer_owners known
  have producerSafe : ¬TaskCancelled work matching events failures (.executionGroup source) := by
    intro cancelled
    apply healthy (generated.object_cancelled_owner_failed_of_itemSafety valid failedPayloads
      itemsSafe producer member ?_ cancelled)
    intro parent same
    subst ancestor
    exact valid.groupSettlement_producerBefore producer
      (GraphEvent.successes_mem_settled settled)
  refine ⟨
    producerSafe,
    generated.streamHealthy_of_producerSafety failedPayloads known ?_ ?_
      contributors (.inr ⟨ref, member, healthy⟩)
  ⟩
  · intro parent same
    cases same
    exact valid.successes_succeed settled
  · intro parent same
    cases same
    exact producerSafe

/-- A live healthy or uncancelled retired producer owner supplies both stream guards.
Witness: replay guard/retirement reflection proves the dependency healthy under the same
cut inventory; the preceding structural bridge then protects the producer and stream.
This retains item failures in the cuts and permits failed co-owners. Registration,
live or retired health, source/output inventory alignment, and earlier item safety remain
explicit local obligations for the general release/replay induction.
-/
theorem ExecutedWork.replayGraphEvents_objectStreamHealthy_of_itemSafety
    {work received matching events failures stream dependencies source ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work received)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch received = true)
    (known : NodeAt work stream .stream dependencies (some (.executionGroup source)))
    (settled : Occurrence.executionGroup source ∈ received.flatMap GraphEvent.successes)
    (member : ref ∈ dependencies)
    (registered
      : ref
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).registeredGroups)
    (healthyBoundary
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).groupIsHealthy
            ref
          = true
        ∨ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            received).RetiredGroup
            ref
          ∧ ref
            ∉ ((State.initialize (Work.fromExecution work)).replayGraphEvents
                received).cancelledGroups)
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
          → stream.ref ∈ owners
          → occurrence ∉ failedBefore failures events.length)
    : ¬TaskCancelled work matching events failures (.executionGroup source)
      ∧ ¬NodeFailed work matching events failures stream.ref := by
  obtain ⟨ancestor, path, result, producer⟩ := NodeAt.stream_objectProducer_owners known
  obtain ⟨group, groupDependencies, descriptor, same⟩ :=
    TaskAt.executionGroup_owner producer member
  have healthy : ¬NodeFailed work matching events failures group.ref := by
    rcases healthyBoundary with live | ⟨retired, uncancelled⟩
    · exact generated.replayGraphEvents_groupHealthy_of_itemSafety valid started
        descriptor (same.symm ▸ registered) (same.symm ▸ live)
        failedPayloads objectsRecorded itemsSafe
    · exact generated.replayGraphEvents_retiredGroupHealthy_of_itemSafety valid started
        descriptor (same.symm ▸ retired) (same.symm ▸ uncancelled)
        failedPayloads objectsRecorded itemsSafe
  exact generated.objectProducedStream_healthy_of_dependency valid known settled member
    failedPayloads itemsSafe (same ▸ healthy) contributors

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
