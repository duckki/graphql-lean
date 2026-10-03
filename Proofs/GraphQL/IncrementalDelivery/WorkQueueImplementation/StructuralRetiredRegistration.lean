import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProducedTaskRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectProducerSafety

/-! Healthy group retirement forces registration of all structural object contributors. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration follows producer support backward through the finite generated work
-----------------------------------------------------------------------------------------

/-- Every structural object task contributing to a healthy retired group is registered.
Witness: dependency-rank induction. Roots are initially lowered. An item producer is
already observed because its group's registered ref exposes that item region. An object
producer has a supporting healthy retired owner; induction registers it, accounting
forces its success, and final owner health forces actual child integration. No missing
lookup is treated as cancellation, and no extra host-source premise is assumed.
-/
theorem ExecutedWork.retired_structuralContributor_registered
    {work events address owners producer payload ref} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    (retired
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          events).RetiredGroup
          ref)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          ref)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  induction rank : (Occurrence.executionGroup address).dependencyRank
    using Nat.strongRecOn generalizing address owners producer payload ref with
  | ind rank ih =>
      cases producer with
      | none => exact TaskAt.executionGroup_replay_registered known events
      | some birth =>
          obtain ⟨node, dependencies, descriptor, refEq⟩ :=
            TaskAt.executionGroup_owner known contributes
          cases birth with
          | item source index =>
              have observed := generated.registered_group_itemProducer_succeeded valid
                descriptor (refEq.symm ▸ retired.1)
              exact TaskAt.executionGroup_registered_of_itemSuccess known valid started observed
          | executionGroup source =>
              obtain ⟨parentOwners, ancestor, parentPayload, parentRef,
                parentKnown, parentContributes, support⟩ :=
                generated.group_objectProducer_support descriptor
              have parentHealthy : ¬GroupRecordInvalidated work
                  ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
                  parentRef := by
                intro invalid
                apply healthy
                rcases support with reused | dependency
                · exact (reused.trans refEq) ▸ invalid
                · exact refEq ▸ GroupRecordInvalidated.ancestor
                    (groupRecordAt_of_nodeAt descriptor) dependency invalid
              have parentRetired :
                  ((State.initialize (Work.fromExecution work)).replayGraphEvents events).RetiredGroup
                    parentRef := by
                rcases support with reused | dependency
                · exact (reused.trans refEq).symm ▸ retired
                · have closure := generated.replayGraphEvents_healthyRetiredAncestors events valid
                  exact closure node.ref (refEq.symm ▸ retired) (refEq.symm ▸ healthy)
                    node dependencies (groupRecordAt_of_nodeAt descriptor) rfl
                    parentRef dependency (.executionGroup source) parentOwners
                    ⟨ancestor, parentPayload, parentKnown⟩ parentContributes
              have lower := (TaskAt.producer_dependency known).1
              rw [rank] at lower
              obtain ⟨parentTask, registered, occurrence, groups⟩ :=
                ih _ lower parentKnown parentContributes parentRetired parentHealthy rfl
              obtain ⟨result, succeeded⟩ :=
                generated.replayGraphEvents_retiredContributor_succeeded valid started
                  registered (groups.symm ▸ parentContributes) parentRetired parentHealthy
              rw [occurrence] at succeeded
              have matching := valid.eachMatches succeeded
              obtain ⟨before, after, split⟩ := List.mem_iff_append.mp succeeded
              obtain ⟨parentNode, found, eligible⟩ :=
                generated.success_with_finalHealthyOwner_processed valid started parentKnown
                  parentContributes parentHealthy split
              exact TaskAt.executionGroup_registered_after_object known matching
                ⟨after, by simp [split, List.append_assoc]⟩ found eligible

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
