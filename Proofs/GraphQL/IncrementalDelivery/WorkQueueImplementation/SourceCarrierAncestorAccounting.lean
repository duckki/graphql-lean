import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedProducerSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention

/-! Actual carrier frames identify earlier ancestor-producer successes and exact buffers. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A released child's ancestor producer has an earlier success on this actual source cut. -/
theorem OwnerPublicationFrame.ancestorProducer_accounted
    {queue work parents before published event group groups streams address owners source
      payload dependencies ref parentOwners parentProducer parentPayload}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task errors,
          (task, errors) ∈ available
          → (GraphEvent.taskFailure task errors).MatchesWork work)
    (carrier
      : WorkQueueEvent.groupSuccess group groups streams
        ∈ (queue.handleGraphEvent event available).2.1)
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup source)) payload)
    (contributes : group.ref ∈ owners)
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (parentKnown
      : TaskAt work (.executionGroup source) parentOwners parentProducer parentPayload)
    (parentContributes : ref ∈ parentOwners)
    : UncancelledRetirement (queue.handleGraphEvent event available).1 ref
      ∧ ∃ result,
          GraphEvent.taskSuccess (.executionGroup source) result ∈ before
          ∧ ((Occurrence.executionGroup source, result.value) ∈ published
              ∨ ∃ node,
                  (queue.cacheTaskFailures available).taskNode? (.executionGroup source)
                    = some node
                  ∧ node.value = some result.value
                  ∧ TaskHasOwners work (.executionGroup source)
                      (node.task.groups.map Execution.DeliveryNode.ref)
                  ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
                  ∧ ref
                    ∈ (queue.cacheTaskFailures available).groupNodes.map
                        (fun owner => owner.group.node.ref)) := by
  have afterSource := frame.source.handleGraphEvent generated canonical event valid accepted
    available licensed
  obtain ⟨_, _, retired⟩ := State.handleGraphEvent_successfulRetirements frame.source.parent
    frame.source.cancellations generated canonical event
    (valid.eachMatches (List.mem_append_right _ List.mem_cons_self)) available group groups streams
    carrier
  have ancestorRetired := afterSource.roots.retired group.ref retired.retired retired.uncancelled
    group dependencies record rfl ref ancestor (.executionGroup source) parentOwners
    ⟨parentProducer, parentPayload, parentKnown⟩ parentContributes
  have ancestorUncancelled := afterSource.markers group.ref retired.retired retired.uncancelled
    group dependencies record rfl ref ancestor (.executionGroup source) parentOwners
    ⟨parentProducer, parentPayload, parentKnown⟩ parentContributes
  obtain ⟨task, registered, occurrence, sameOwners⟩ :=
    afterSource.retired_structuralContributor_registered generated valid known contributes
      retired.retired retired.uncancelled
  have settled := afterSource.owners.retired_contributor_settled registered
    (sameOwners.symm ▸ contributes) retired.uncancelled retired.retired
  rw [occurrence] at settled
  obtain ⟨childResult, succeeded⟩ := groupSettlement_source settled
  have prior := valid.prefix (List.prefix_append before [event])
  have parentSucceeded : ∃ result,
      GraphEvent.taskSuccess (.executionGroup source) result ∈ before := by
    apply prior.objectSuccess_input
    rcases List.mem_append.mp succeeded with earlier | current
    · exact prior.groupSettlement_producerBefore known
        (List.mem_flatMap.mpr ⟨_, earlier, List.mem_cons_self⟩)
    · have same := List.mem_singleton.mp current
      subst event
      obtain ⟨_, _, otherOwners, otherProducer, otherPayload, otherKnown, ready⟩ :=
        valid.atPrefix (before := before)
          (event := .taskSuccess (.executionGroup address) childResult) ⟨[], by simp⟩
      exact ready _ (TaskAt.unique known otherKnown).2.1.symm
  obtain ⟨result, succeeded⟩ := parentSucceeded
  refine ⟨⟨ancestorRetired, ancestorUncancelled⟩, result, succeeded, ?_⟩
  have uncancelled : ref ∉ queue.cancelledGroups := fun member => ancestorUncancelled
    (queue.handleGraphEvent_cancelledGroups_subset event available member)
  rcases frame.accounted (.executionGroup source) result succeeded parentOwners parentProducer
      parentPayload parentKnown ref parentContributes uncancelled with priorOutput | buffered
  · exact .inl priorOutput
  · obtain ⟨node, lookup, stored, owns, live⟩ := buffered
    have located := State.taskNode?_some lookup
    obtain ⟨_, _, _, _, descriptor⟩ := (frame.source.pending.matching node.task
      (frame.source.pending.started node located.1)).1
    have sameOwners := (TaskAt.unique (located.2 ▸ descriptor) parentKnown).1
    have notAvailable : ∀ errors, (Occurrence.executionGroup source, errors) ∉ available := by
      intro errors cached
      obtain ⟨_, _, success, _, _⟩ := prior.eachMatches succeeded
      obtain ⟨_, _, _, failure⟩ := licensed _ errors cached
      cases (success.unique failure).2.2
    exact .inr ⟨node, State.cacheTaskFailures_lookup_existing lookup available notAvailable,
      stored, sameOwners.symm ▸ ⟨parentProducer, parentPayload, parentKnown⟩, owns,
      by rwa [State.cacheTaskFailures_groupNodes]⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
