import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayOwnerConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StructuralRetiredRegistration

/-! Healthy retirement covers structural contributors without an observable closure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recover the initially live contributor at the actual source success
-----------------------------------------------------------------------------------------

/-- A source success retains every finally healthy contributing owner at its input boundary.
Witness: source freshness and generated owner accounting force a live record before the
success; exact structural task metadata identifies the same contributor ref. Final health
transports backward through the full source-failure inventory.
-/
theorem ExecutedWork.success_with_finalHealthyOwner_live
    {work events occurrence result owners producer payload ref before after}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (known : TaskAt work occurrence owners producer payload) (contributes : ref ∈ owners)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          ref)
    (split : events = before ++ .taskSuccess occurrence result :: after)
    : ∃ node,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
            occurrence
          = some node
        ∧ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).taskHasHealthyOwner
            node.task
          = true
        ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
        ∧ ref
          ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
              before).groupNodes.map
              (fun owner => owner.group.node.ref) := by
  let initial := State.initialize (Work.fromExecution work)
  have earlier : before.IsPrefix events := ⟨.taskSuccess occurrence result :: after, split.symm⟩
  have accepted : initial.acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := .taskSuccess occurrence result :: after)
    simpa only [← split] using started
  obtain ⟨_, _, ledger⟩ := generated.replayGraphEvents_ownerAccounting_of_started before
    (valid.prefix earlier) accepted
  obtain ⟨node, found, guard⟩ := generated.success_with_finalHealthyOwner_processed valid
    started known contributes healthy split
  obtain ⟨member, occurrenceEq⟩ := State.taskNode?_some found
  have registered := ledger.pending.started node member
  obtain ⟨_, _, _, _, descriptor⟩ := (ledger.pending.matching node.task registered).1
  have sameOwners := (TaskAt.unique (occurrenceEq ▸ descriptor) known).1
  have nodeContributes := sameOwners.symm ▸ contributes
  have prior : (before ++ [GraphEvent.taskSuccess occurrence result]).IsPrefix events :=
    ⟨after, by simp [split, List.append_assoc]⟩
  obtain ⟨_, fresh, _⟩ := valid.atPrefix prior
  have unsettled : node.task.occurrence ∉ GraphEvent.groupSettlements before := by
    rw [occurrenceEq]
    exact fun member => fresh.2.2.1 occurrence List.mem_cons_self
      (GraphEvent.groupSettlements_subsetIdentities before member)
  have sourceHealthy : ¬GroupInvalidated work (GraphEvent.failureSettlements before) ref := by
    intro invalid
    apply healthy
    apply GroupInvalidated.toRecordInvalidated
    apply (generated.failureInventories_groupInvalidated_iff events valid started ref).mp
    apply invalid.mono
    rw [split, GraphEvent.failureSettlements_append_list]
    exact List.subset_append_right _ _
  obtain ⟨owner, live, same, _⟩ := ledger.healthyRegisteredTasks node.task registered unsettled
    ref nodeContributes sourceHealthy
  exact ⟨node, found, guard, nodeContributes, List.mem_map.mpr ⟨owner, live, same⟩⟩

-----------------------------------------------------------------------------------------
-- The common ledger accounts for all data by a healthy retirement boundary
-----------------------------------------------------------------------------------------

/-- A structurally healthy contributor preserves an earlier success as output or a buffer.
Witness: source freshness establishes its initially live owner and accepted storing
branch. Shared-ledger owner conservation follows that exact value to the replay boundary;
generated task accounting supplies the retained node's structural ownership, if needed.
-/
theorem ExecutedWork.healthy_success_published_or_buffered
    {work events published occurrence result owners producer payload ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published)
    (known : TaskAt work occurrence owners producer payload) (contributes : ref ∈ owners)
    (healthy
      : ¬GroupRecordInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions events)
          ref)
    (succeeded : GraphEvent.taskSuccess occurrence result ∈ events)
    : (occurrence, result.value)
        ∈ published.take
            (((State.initialize (Work.fromExecution work)).rawEventReplay
                events).2.flatMap
              WorkQueueEvent.objectValues).length
      ∨ ∃ node,
          ((State.initialize (Work.fromExecution work)).replayGraphEvents
              events).taskNode?
              occurrence
            = some node
          ∧ node.value = some result.value
          ∧ TaskHasOwners work occurrence
              (node.task.groups.map Execution.DeliveryNode.ref)
          ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
          ∧ ref
            ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
                events).groupNodes.map
                (fun owner => owner.group.node.ref) := by
  let initial := State.initialize (Work.fromExecution work)
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp succeeded
  obtain ⟨node, found, guard, nodeContributes, present⟩ :=
    generated.success_with_finalHealthyOwner_live valid started known contributes healthy split
  have suffix : (initial.replayGraphEvents before).ReplayClosuresCovered
      (.taskSuccess occurrence result :: after)
      (published.drop ((initial.rawEventReplay before).2.flatMap
        WorkQueueEvent.objectValues).length) := by
    apply State.ReplayClosuresCovered.afterPrefix
    simpa only [← split] using covered
  have finalState : (initial.replayGraphEvents before).replayGraphEvents
      (.taskSuccess occurrence result :: after) = initial.replayGraphEvents events := by
    simp only [split, State.replayGraphEvents, List.foldl_append]
  have cancellation := generated.replayGraphEvents_cancelledRecordsSupported events valid
  have uncancelled := cancellation.healthy_not_mem healthy
  rcases suffix.success_published_or_buffered found guard nodeContributes present
      (finalState.symm ▸ uncancelled) with emitted | buffered
  · left
    change (occurrence, result.value) ∈ published.take
      ((initial.rawEventReplay events).2.flatMap WorkQueueEvent.objectValues).length
    rw [split, State.rawEventReplay_append]
    dsimp only
    rw [State.rawEventReplay_state, List.flatMap_append, List.length_append, List.take_add]
    exact List.mem_append_right _ emitted
  · right
    rw [finalState] at buffered
    obtain ⟨node, found, stored, nodeContributes, present⟩ := buffered
    have final := (createWorkQueue_pendingAccounting work).replayGraphEvents
      (before := []) generated events valid started
    have lookup := State.taskNode?_some found
    obtain ⟨_, nodePayload, nodeProducer, _, descriptor⟩ :=
      (final.matching node.task (final.started node lookup.1)).1
    exact ⟨node, found, stored, ⟨nodeProducer, nodePayload, lookup.2 ▸ descriptor⟩,
      nodeContributes, present⟩

/-- Every structural object contributor publishes by healthy retirement of its owner.
Witness: structural registration and owner accounting supply a processed source success.
Prepared/replay conservation follows that exact value to the retirement boundary on the
existing ledger. No storage, publication, or completion-notice premise is added.
-/
theorem ExecutedWork.retired_structuralContributor_published
    {work events published address owners producer payload ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published)
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
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            (((State.initialize (Work.fromExecution work)).rawEventReplay
                events).2.flatMap
              WorkQueueEvent.objectValues).length := by
  obtain ⟨task, registered, occurrenceEq, groupsEq⟩ :=
    generated.retired_structuralContributor_registered valid started known contributes
      retired healthy
  obtain ⟨result, succeeded⟩ := generated.replayGraphEvents_retiredContributor_succeeded
    valid started registered (groupsEq.symm ▸ contributes) retired healthy
  rw [occurrenceEq] at succeeded
  refine ⟨result.value, ?_⟩
  exact Or.resolve_right
    (generated.healthy_success_published_or_buffered valid started covered known contributes
      healthy succeeded)
    (fun ⟨_, _, _, _, _, present⟩ => retired.2 present)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
