import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PreparedCarrierReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulSettlementAcceptance

/-! Actual successful carriers publish every registered structural contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated source accounting removes the supplied storage premise
-----------------------------------------------------------------------------------------

/-- Every registered contributor publishes strictly before its actual successful carrier.
Witness: healthy retirement supplies a source success and forces its storing branch.
If it is the current input, prepared coverage applies; otherwise prepared conservation
and buffered-carrier coverage span the intervening handlers. One supplied replay ledger
fixes every occurrence label and strict output-prefix count throughout the argument.
-/
theorem ExecutedWork.successfulCarrier_registeredContributor_covered
    {work before event index group groups streams task published}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (carrier
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2[index]?
        = some (.groupSuccess group groups streams))
    (registered
      : task
        ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
            (before ++ [event])).tasks)
    (contributes : group.key ∈ task.groups.map Execution.DeliveryNode.key)
    : ∃ value,
        (task.occurrence, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).handleGraphEvent
                    event).2.take
                    index).flatMap
                  WorkQueueEvent.objectValues).length) := by
  let initial := State.initialize (Work.fromExecution work)
  have boundary (earlier : List GraphEvent) (prior : earlier.IsPrefix (before ++ [event]))
      : (initial.replayGraphEvents earlier).PendingAccounting work
          (GraphEvent.taskSettlements earlier) := by
    have accepts : initial.acceptsBatch earlier = true := by
      obtain ⟨later, same⟩ := prior
      apply State.acceptsBatch_prefix (after := later)
      rwa [same]
    exact (createWorkQueue_pendingAccounting work).replayGraphEvents
      (before := []) generated earlier (valid.prefix prior) accepts
  have final := boundary (before ++ [event]) ⟨[], by simp⟩
  obtain ⟨_, payload, producer, _, known⟩ := (final.matching task registered).1
  obtain ⟨result, supplied⟩ := generated.successfulCarrier_registeredContributor_succeeded
    valid started (List.mem_of_getElem? carrier) registered contributes
  have accepted (earlier : List GraphEvent)
      (prior : (earlier ++ [GraphEvent.taskSuccess task.occurrence result]).IsPrefix
        (before ++ [event]))
      : ∃ node,
          (initial.replayGraphEvents earlier).taskNode? task.occurrence = some node
          ∧ (initial.replayGraphEvents earlier).taskHasHealthyOwner node.task = true
          ∧ group.key ∈ node.task.groups.map Execution.DeliveryNode.key := by
    obtain ⟨node, found, healthy⟩ :=
      generated.successfulCarrier_contributorSuccess_accepted valid started
        (List.mem_of_getElem? carrier) prior known contributes
    have earlierPrefix := (List.prefix_append earlier
      [GraphEvent.taskSuccess task.occurrence result]).trans prior
    have ledger := boundary earlier earlierPrefix
    have lookup := State.taskNode?_some found
    obtain ⟨_, _, _, _, descriptor⟩ :=
      (ledger.matching node.task (ledger.started node lookup.1)).1
    have sameOwners := (TaskAt.unique (lookup.2 ▸ descriptor) known).1
    exact ⟨node, found, healthy, sameOwners.symm ▸ contributes⟩
  rcases List.mem_append.mp supplied with earlier | current
  · obtain ⟨prefixInputs, middle, sameBefore⟩ := List.mem_iff_append.mp earlier
    have prior : (prefixInputs ++ [GraphEvent.taskSuccess task.occurrence result]).IsPrefix
        (before ++ [event]) :=
      ⟨middle ++ [event], by simp [sameBefore, List.append_assoc]⟩
    obtain ⟨node, found, healthy, contributes⟩ := accepted prefixInputs prior
    have prefixBoundary := boundary prefixInputs
      ((List.prefix_append prefixInputs [GraphEvent.taskSuccess task.occurrence result]).trans
        prior)
    have suffix : (initial.replayGraphEvents prefixInputs).ReplayClosuresCovered
        (.taskSuccess task.occurrence result :: middle ++ [event])
        (published.drop ((initial.rawEventReplay prefixInputs).2.flatMap
          WorkQueueEvent.objectValues).length) := by
      apply State.ReplayClosuresCovered.afterPrefix
      simpa only [sameBefore, List.append_assoc, List.cons_append] using covered
    have matchingLater :
        ∀ input ∈ GraphEvent.taskSuccess task.occurrence result :: middle ++ [event],
        input.MatchesWork work := by
      intro input member
      apply valid.eachMatches
      rw [sameBefore, List.append_assoc, List.cons_append]
      exact List.mem_append_right _ member
    have states : initial.replayGraphEvents before
        = ((initial.replayGraphEvents prefixInputs).taskSuccess
            task.occurrence result).1.replayGraphEvents middle := by
      simp only [sameBefore, State.replayGraphEvents, List.foldl_append,
        List.foldl_cons, State.handleGraphEvent]
    have atCarrier : ((((initial.replayGraphEvents prefixInputs).taskSuccess
        task.occurrence result).1.replayGraphEvents middle).handleGraphEvent event).2[index]?
        = some (.groupSuccess group groups streams) := by
      change ((initial.replayGraphEvents before).handleGraphEvent event).2[index]?
        = some (.groupSuccess group groups streams) at carrier
      rwa [states] at carrier
    have delivered := suffix.success_before_carrier prefixBoundary.liveGroups
      prefixBoundary.taskGroups prefixBoundary.started matchingLater found healthy
      atCarrier contributes
    refine ⟨result.value, ?_⟩
    change (task.occurrence, result.value) ∈ published.take
      (((initial.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
        + ((((initial.replayGraphEvents before).handleGraphEvent event).2.take index).flatMap
          WorkQueueEvent.objectValues).length)
    rw [states, sameBefore]
    simp only [State.rawEventReplay_append, State.rawEventReplay_state,
      State.rawEventReplay_cons, List.flatMap_append, List.length_append,
      State.handleGraphEvent, Nat.add_assoc]
    rw [List.take_add]
    exact List.mem_append_right _
      (by simpa only [Nat.add_assoc, State.handleGraphEvent] using delivered)
  · have same := List.mem_singleton.mp current
    subst event
    obtain ⟨node, found, healthy, contributes⟩ := accepted before ⟨[], by simp⟩
    have suffix := covered.afterPrefix before [GraphEvent.taskSuccess task.occurrence result]
    have delivered := suffix.success_at_carrier found healthy carrier contributes
    refine ⟨result.value, ?_⟩
    rw [List.take_add]
    exact List.mem_append_right _ delivered

/-- Every root structural contributor publishes before its actual successful carrier.
Witness: inverse lowering supplies registration without an extra premise, and the general
registered-contributor theorem supplies strict-prefix publication on the existing ledger.
-/
theorem ExecutedWork.successfulCarrier_rootContributor_covered
    {work before event index group groups streams address owners payload published}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [event]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch (before ++ [event])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [event]) published)
    (carrier
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).handleGraphEvent
          event).2[index]?
        = some (.groupSuccess group groups streams))
    (known : TaskAt work (.executionGroup address) owners none payload)
    (contributes : group.key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
                WorkQueueEvent.objectValues).length
              + (((((State.initialize (Work.fromExecution work)).replayGraphEvents
                      before).handleGraphEvent
                    event).2.take
                    index).flatMap
                  WorkQueueEvent.objectValues).length) := by
  obtain ⟨task, registered, occurrence, groups⟩ :=
    TaskAt.executionGroup_replay_registered known (before ++ [event])
  simpa only [occurrence]
    using generated.successfulCarrier_registeredContributor_covered valid started covered
      carrier registered (groups.symm ▸ contributes)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
