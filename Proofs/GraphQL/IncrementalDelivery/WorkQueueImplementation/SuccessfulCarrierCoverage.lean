import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PreparedCarrierReplay

/-! Structural contributors publish strictly before their actual successful handler carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every contributor is in the earlier ledger or the strict prefix of this handler's ledger.
Retirement establishes structural registration and consumed success. Earlier successes use
buffer accounting; the incoming success uses its exact prepared value certificate. -/
theorem OwnerPublicationFrame.successfulCarrier_structuralContributor_covered
    {queue work parents before published localPublications index group groups streams
      address owners producer payload}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (event : GraphEvent) (valid : ValidGraphEvents work (before ++ [event]))
    (accepted : queue.acceptsGraphEvent event = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ occurrence errors,
          (occurrence, errors) ∈ available
          → (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (covered : queue.ReplayClosuresCovered [event] localPublications available)
    (selected
      : (queue.handleGraphEvent event available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (known : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : group.ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value) ∈ published
        ∨ (Occurrence.executionGroup address, value)
          ∈ localPublications.take
              (((queue.handleGraphEvent event available).2.1.take index).flatMap
                WorkQueueEvent.objectValues).length := by
  have afterSource := frame.source.handleGraphEvent generated canonical event valid accepted
    available licensed
  obtain ⟨_, _, retired⟩ := State.handleGraphEvent_successfulRetirements frame.source.parent
    frame.source.cancellations generated canonical event
    (valid.eachMatches (List.mem_append_right _ List.mem_cons_self)) available group groups streams
    (List.mem_of_getElem? selected)
  obtain ⟨task, registered, occurrence, sameOwners⟩ :=
    afterSource.retired_structuralContributor_registered generated valid known contributes
      retired.retired retired.uncancelled
  have settled := afterSource.owners.retired_contributor_settled registered
    (sameOwners.symm ▸ contributes) retired.uncancelled retired.retired
  rw [occurrence] at settled
  obtain ⟨source, received, included⟩ := List.mem_flatMap.mp (List.mem_reverse.mp settled)
  cases source with
  | taskSuccess task result =>
      have same : task = .executionGroup address := (List.mem_singleton.mp included).symm
      subst task
      refine ⟨result.value, ?_⟩
      rcases List.mem_append.mp received with earlier | current
      · have uncancelled : group.ref ∉ queue.cancelledGroups := fun member =>
          retired.uncancelled (queue.handleGraphEvent_cancelledGroups_subset event available member)
        rcases frame.accounted (.executionGroup address) result earlier owners producer payload
            known group.ref contributes uncancelled with emitted | ⟨node, found, stored, owns, _⟩
        · exact .inl emitted
        · apply Or.inr
          have delivered := covered.1 index group groups streams selected
            (.executionGroup address) node result.value found stored owns
          rw [List.take_take] at delivered
          exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered
      · have same : event = .taskSuccess (.executionGroup address) result :=
          (List.mem_singleton.mp current).symm
        subst event
        have cached := frame.source.pending.cacheTaskFailures available
        have cachedAccepted : (queue.cacheTaskFailures available).acceptsGraphEvent
            (.taskSuccess (.executionGroup address) result) = true := by
          rwa [State.cacheTaskFailures_acceptsGraphEvent]
        obtain ⟨node, found⟩ : ∃ node,
                                (queue.cacheTaskFailures available).taskNode?
                                  (.executionGroup address)
                                = some node := by
          cases found
                : (queue.cacheTaskFailures available).taskNode?
                    (.executionGroup address) with
          | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
              Bool.false_eq_true] at cachedAccepted
          | some node => exact ⟨node, rfl⟩
        have lookup := State.taskNode?_some found
        obtain ⟨_, _, _, _, descriptor⟩ :=
          (cached.matching node.task (cached.started node lookup.1)).1
        have aligned := (TaskAt.unique (lookup.2 ▸ descriptor) known).1
        apply Or.inr
        exact covered.success_at_carrier found selected (aligned.symm ▸ contributes)
  | taskFailure | groupFailure | streamItems | streamSuccess | streamFailure =>
      cases included

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
