import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExposedRegions
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulSettlementAcceptance

/-! Successful source producers expose their exact structural child registrations. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful item identities have a concrete active source-handler boundary
-----------------------------------------------------------------------------------------

/-- A successful item identity belongs to a concrete item of a source stream batch.
Witness: invert the success inventory; source matching excludes object events carrying
item identities. Retain the source split rather than only whole-history membership.
-/
theorem ValidGraphEvents.itemSuccess_input {work events address index}
    (valid : ValidGraphEvents work events)
    (success : Occurrence.item address index ∈ events.flatMap GraphEvent.successes)
    : ∃ before stream items item after,
        events = before ++ .streamItems stream items :: after
        ∧ item ∈ items
        ∧ item.occurrence = .item address index := by
  obtain ⟨event, member, included⟩ := List.mem_flatMap.mp success
  have matching := valid.eachMatches member
  obtain ⟨before, after, same⟩ := List.mem_iff_append.mp member
  cases event with
  | taskSuccess task result =>
      have identity := List.mem_singleton.mp included
      obtain ⟨owners, producer, known, _⟩ := matching
      rw [← identity] at known
      cases StructuralEquivalence.taskAt_of_current known
  | streamItems stream items =>
      obtain ⟨item, selected, identity⟩ := List.mem_map.mp included
      exact ⟨before, stream, items, item, after, same, selected, identity⟩
  | taskFailure | groupFailure | streamSuccess | streamFailure => cases included

/-- An observed successful item registers all its immediate structural object children.
Witness: identify the exact item input, use batch acceptance to prove its stream active,
then apply inverse lowering and permanent-registry persistence. No lookup or activation
premise is supplied by the caller.
-/
theorem TaskAt.executionGroup_registered_of_itemSuccess
    {work address owners payload source index events}
    (known
      : TaskAt work (.executionGroup address) owners (some (.item source index)) payload)
    (valid : ValidGraphEvents work events)
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    (success : Occurrence.item source index ∈ events.flatMap GraphEvent.successes)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨before, stream, items, item, after, same, selected, identity⟩ :=
    valid.itemSuccess_input success
  have earlier : (before ++ [GraphEvent.streamItems stream items]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted := State.eventsStarted_atPrefix (State.initialize (Work.fromExecution work))
    before (.streamItems stream items) after [] (same ▸ started)
  have matching : (GraphEvent.streamItems stream items).MatchesWork work :=
    valid.eachMatches (by rw [same]; exact List.mem_append_right _ List.mem_cons_self)
  exact TaskAt.executionGroup_registered_after_item (identity.symm ▸ known) matching
    selected earlier accepted

-----------------------------------------------------------------------------------------
-- A healthy registered contributor's success cannot be silently ignored
-----------------------------------------------------------------------------------------

/-- A source success with an owner healthy at the final boundary was actually processed.
Witness: full-source/accepted-failure equivalence transports final owner health backward,
and the existing healthy-owner theorem forces the executable storing branch at that input.
-/
theorem ExecutedWork.success_with_finalHealthyOwner_processed
    {work events occurrence result owners producer payload ref before after}
    (_generated : ExecutedWork work) (_valid : ValidGraphEvents work events)
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) events = true)
    (_known : TaskAt work occurrence owners producer payload)
    (_contributes : ref ∈ owners)
    (_healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          ref)
    (split : events = before ++ .taskSuccess occurrence result :: after)
    : ∃ node,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some node := by
  have accepted : State.eventsStarted [] (State.initialize (Work.fromExecution work))
      (before ++ [.taskSuccess occurrence result]) = true := by
    apply State.eventsStarted_prefix (after := after)
    simpa only [List.append_assoc, List.singleton_append, ← split] using started
  exact ExecutedWork.replayGraphEvents_success_present accepted

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
