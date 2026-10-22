import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.UncancelledReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectProducerSafety
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExposedRegions

/-! Uncancelled retirement forces all structural contributors to have been registered. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem groupSettlement_success {events : List GraphEvent} {occurrence}
    (settled : occurrence ∈ GraphEvent.groupSettlements events)
    : occurrence ∈ events.flatMap GraphEvent.successes := by
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp (List.mem_reverse.mp settled)
  apply List.mem_flatMap.mpr
  refine ⟨event, member, ?_⟩
  cases event <;> simp_all [GraphEvent.groupSuccesses, GraphEvent.successes]

/-- A structural contributor of an uncancelled retired group is permanently registered.
Witness: producer-rank induction. Exposed item regions identify consumed item producers;
object producers have a retired uncancelled supporting owner and hence already succeeded.
The consumed-producer registration certificate then supplies the exact child task. -/
theorem UncancelledReplayFrame.retired_structuralContributor_registered
    {queue work parents before address owners producer payload ref}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work) (valid : ValidGraphEvents work before)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners) (retired : queue.RetiredGroup ref)
    (uncancelled : ref ∉ queue.cancelledGroups)
    : ∃ task ∈ queue.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  induction rank : (Occurrence.executionGroup address).dependencyRank
    using Nat.strongRecOn generalizing address owners producer payload ref with
  | ind rank ih =>
      cases producer with
      | none => exact frame.producerRegistrations.root_registered known
      | some birth =>
          obtain ⟨node, dependencies, descriptor, refEq⟩ :=
            TaskAt.executionGroup_owner known contributes
          cases birth with
          | item source index =>
              have seen := frame.regions.group_itemProducer_seen generated descriptor
                (refEq.symm ▸ retired.1)
              have observed := valid.itemIdentity_success seen
              exact frame.producerRegistrations.item_registered known observed
          | executionGroup source =>
              obtain ⟨parentOwners, ancestor, parentPayload, parentRef,
                parentKnown, parentContributes, support⟩ :=
                generated.group_objectProducer_support descriptor
              have parentRetired : queue.RetiredGroup parentRef := by
                rcases support with reused | dependency
                · exact (reused.trans refEq).symm ▸ retired
                · exact frame.roots.retired node.ref (refEq.symm ▸ retired)
                    (refEq.symm ▸ uncancelled) node dependencies
                    (groupRecordAt_of_nodeAt descriptor) rfl parentRef dependency
                    (.executionGroup source) parentOwners ⟨ancestor, parentPayload, parentKnown⟩
                    parentContributes
              have parentUncancelled : parentRef ∉ queue.cancelledGroups := by
                rcases support with reused | dependency
                · exact (reused.trans refEq).symm ▸ uncancelled
                · exact frame.markers node.ref (refEq.symm ▸ retired)
                    (refEq.symm ▸ uncancelled) node dependencies
                    (groupRecordAt_of_nodeAt descriptor) rfl parentRef dependency
                    (.executionGroup source) parentOwners ⟨ancestor, parentPayload, parentKnown⟩
                    parentContributes
              have lower := (TaskAt.producer_dependency known).1
              rw [rank] at lower
              obtain ⟨task, registered, occurrence, groups⟩ := ih _ lower parentKnown
                parentContributes parentRetired parentUncancelled rfl
              have settled := frame.owners.retired_contributor_settled registered
                (groups.symm ▸ parentContributes) parentUncancelled parentRetired
              rw [occurrence] at settled
              exact frame.producerRegistrations.object_registered known
                (groupSettlement_success settled) ⟨ancestor, parentPayload, parentKnown⟩
                parentContributes parentUncancelled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
