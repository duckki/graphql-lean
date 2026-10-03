import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StructuralCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredContributorPublication

/-! A released object's ancestor producer has already published or remains exactly buffered. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Structural producer successes precede the handler releasing their object children
-----------------------------------------------------------------------------------------

/-- A successful object identity in the source inventory has an actual task-success input.
Witness: inspect its source event; matching forbids an object identity in a stream item.
-/
theorem ValidGraphEvents.objectSuccess_input {work events address}
    (valid : ValidGraphEvents work events)
    (success : Occurrence.executionGroup address ∈ events.flatMap GraphEvent.successes)
    : ∃ result, GraphEvent.taskSuccess (.executionGroup address) result ∈ events := by
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp success
  have matching := valid.eachMatches member
  cases event with
  | taskSuccess task result =>
      have identity := List.mem_singleton.mp included
      exact ⟨result, identity ▸ member⟩
  | streamItems stream items =>
      obtain ⟨item, selected, identity⟩ := List.mem_map.mp included
      obtain ⟨owners, producer, known, _⟩ := matching item selected
      rw [identity] at known
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
  | taskFailure | streamSuccess | streamFailure => cases included

/-- Every object producer settles strictly before the handler releasing its child.
Witness: successful-carrier accounting derives the child's source settlement. If it was
earlier, its prefix readiness supplies the producer; if it is the current input, that
input's own readiness does. Neither case may use the current input as its producer.
-/
theorem ExecutedWork.successfulCarrier_objectProducer_before
    {work before event group groups streams address owners source payload}
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
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup source)) payload)
    (contributes : group.ref ∈ owners)
    : ∃ result, GraphEvent.taskSuccess (.executionGroup source) result ∈ before := by
  obtain ⟨task, registered, occurrenceEq, groupsEq⟩ :=
    generated.successfulCarrier_structuralContributor_registered valid started carrier
      known contributes
  obtain ⟨result, succeeded⟩ := generated.successfulCarrier_registeredContributor_succeeded
    valid started carrier registered (groupsEq.symm ▸ contributes)
  rw [occurrenceEq] at succeeded
  have prior := valid.prefix (List.prefix_append before [event])
  apply prior.objectSuccess_input
  rcases List.mem_append.mp succeeded with earlier | current
  · apply prior.groupSettlement_producerBefore known
    exact List.mem_flatMap.mpr ⟨_, earlier, List.mem_cons_self⟩
  · have same := List.mem_singleton.mp current
    subst event
    obtain ⟨_, _, otherOwners, otherProducer, otherPayload, otherKnown, ready⟩ :=
      valid.atPrefix (before := before)
        (event := .taskSuccess (.executionGroup address) result) ⟨[], by simp⟩
    have producerEq := (TaskAt.unique known otherKnown).2.1
    exact ready _ producerEq.symm

-----------------------------------------------------------------------------------------
-- Healthy ancestor support removes the caller-supplied buffered lookup
-----------------------------------------------------------------------------------------

/-- A released child's ancestor producer is already delivered or exactly buffered at entry.
Witness: the carrier makes the contributing ancestor structurally healthy; source
readiness places the producer success before this handler. The common replay ledger
then conserves its exact value and live supporting owner up to that boundary.
-/
theorem ExecutedWork.successfulCarrier_ancestorProducer_published_or_buffered
    {work before event group groups streams address owners source payload dependencies
      ref parentOwners parentProducer parentPayload published}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (carrier
      : Execution.WorkQueueEvent.groupSuccess group groups streams
        ∈ (((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).handleGraphEvent
            event).2)
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup source)) payload)
    (contributes : group.ref ∈ owners)
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (parentKnown
      : TaskAt work (.executionGroup source) parentOwners parentProducer parentPayload)
    (parentContributes : ref ∈ parentOwners)
    : ∃ result,
        GraphEvent.taskSuccess (.executionGroup source) result ∈ before
        ∧ ((Occurrence.executionGroup source, result.value)
              ∈ published.take
                  (((State.initialize (Work.fromExecution work)).rawEventReplay
                      before).2.flatMap
                    WorkQueueEvent.objectValues).length
            ∨ ∃ node,
                ((State.initialize (Work.fromExecution work)).replayGraphEvents
                    before).taskNode?
                    (.executionGroup source)
                  = some node
                ∧ node.value = some result.value
                ∧ TaskHasOwners work (.executionGroup source)
                    (node.task.groups.map Execution.DeliveryNode.ref)
                ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
                ∧ ref
                  ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).groupNodes.map
                      (fun owner => owner.group.node.ref)) := by
  obtain ⟨result, succeeded⟩ := generated.successfulCarrier_objectProducer_before
    valid started carrier known contributes
  have accepted := State.acceptsBatch_prefix started
  have prior := valid.prefix (List.prefix_append before [event])
  obtain ⟨_, _, _, healthy, _⟩ :=
    generated.replayGraphEvents_successfulCarrier_retiredHealthy valid accepted carrier
  have ancestorHealthy : ¬GroupRecordInvalidated work
      ((State.initialize (Work.fromExecution work)).objectFailureContributions before) ref := by
    intro invalid
    apply healthy
    apply GroupRecordInvalidated.ancestor record ancestor
    apply invalid.mono
    rw [State.objectFailureContributions_append]
    exact List.subset_append_right _ _
  exact ⟨
    result,
    succeeded,
    generated.healthy_success_published_or_buffered prior accepted
      (covered.prefix before [event]) parentKnown parentContributes ancestorHealthy
      succeeded
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
