import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceCarrierAncestorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPreparedFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskPublicationBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainAncestorCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawPublicationClosures

/-! Ancestor producer ordering in an actual task handler with cached startup failures. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Task handlers publish ancestor producers before the child's exact value block. -/
theorem OwnerPublicationFrame.taskSuccess_ancestorProducer_beforeValue
    {queue work parents before published localPublications occurrence result position
      group values address owners source payload dependencies ref parentOwners
      parentProducer parentPayload}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [.taskSuccess occurrence result]))
    (accepted : queue.acceptsGraphEvent (.taskSuccess occurrence result) = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task errors,
          (task, errors) ∈ available
          → (GraphEvent.taskFailure task errors).MatchesWork work)
    (covered
      : queue.ReplayClosuresCovered [.taskSuccess occurrence result]
          localPublications available)
    (selected
      : (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1[position]?
        = some (.groupValues group values))
    (known
      : TaskAt work (.executionGroup address) owners
          (some (.executionGroup source)) payload)
    (contributes : group.ref ∈ owners)
    (record : GroupRecordAt work group dependencies) (ancestor : ref ∈ dependencies)
    (parentKnown
      : TaskAt work (.executionGroup source) parentOwners parentProducer parentPayload)
    (parentContributes : ref ∈ parentOwners)
    : ∃ value,
        (Occurrence.executionGroup source, value) ∈ published
        ∨ (Occurrence.executionGroup source, value)
          ∈ localPublications.take
              (((queue.handleGraphEvent (.taskSuccess occurrence result)
                  available).2.1.take
                  position).flatMap
                WorkQueueEvent.objectValues).length := by
  let current := queue.cacheTaskFailures available
  obtain ⟨groups, streams, next⟩ := (queue.handleGraphEvent_publicationPairs
    (.taskSuccess occurrence result) available).next selected
  obtain ⟨retired, parentResult, succeeded, prior | buffered⟩ := frame.ancestorProducer_accounted
    generated canonical valid accepted available licensed (List.mem_of_getElem? next)
    known contributes record ancestor parentKnown parentContributes
  · exact ⟨parentResult.value, .inl prior⟩
  · obtain ⟨node, lookup, stored, taskOwners, owns, present⟩ := buffered
    by_cases active : group.ref ∈ current.rootGroups
    · have sourceActive : group.ref ∈ queue.rootGroups := by
        have same := congrArg State.rootGroups (queue.cacheTaskFailures_frame available)
        rwa [show current.rootGroups = queue.rootGroups from same] at active
      have oldRetired := frame.source.roots.live.roots group.ref sourceActive group dependencies
        record rfl ref ancestor (.executionGroup source) parentOwners
        ⟨parentProducer, parentPayload, parentKnown⟩ parentContributes
      have oldUncancelled : ref ∉ queue.cancelledGroups := fun member => retired.uncancelled
        (queue.handleGraphEvent_cancelledGroups_subset _ available member)
      obtain ⟨value, delivered⟩ := frame.retired_structuralContributor_published generated
        (valid.prefix (List.prefix_append before [_])) parentKnown parentContributes
        oldRetired oldUncancelled
      exact ⟨value, .inl delivered⟩
    · obtain ⟨incoming, found, index, atDrain, prefixEq⟩ :=
        current.taskSuccess_inactiveValue_drain occurrence result available selected active
      let prepared := ((current.putTaskNode { incoming with value := some result.value }
        ).maybeIntegrateWork result.work (some occurrence)).1
      let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
      let activated := (released.1.startNewWork released.2.2 available).1
      have fresh := (validGraphEvents_last valid).2.2
      have different : occurrence ≠ .executionGroup source := by
        intro same
        apply fresh.2.2.1 occurrence List.mem_cons_self
        rw [same]
        exact GraphEvent.successes_mem_settled
          (List.mem_flatMap.mpr ⟨_, succeeded, List.mem_cons_self⟩)
      have retained := State.putTaskNode_lookup_other lookup
        { incoming with value := some result.value }
        ((State.taskNode?_some found).2 ▸ different)
      have preparedLookup := State.maybeIntegrateWork_lookup_other retained result.work
        (some occurrence) (fun same => different (Option.some.inj same))
      have preparedPresent := State.maybeIntegrateWork_includesRefs
        (current.putTaskNode { incoming with value := some result.value }) result.work
        (some occurrence) ref present
      obtain ⟨_, preparedRoots⟩ := frame.source.taskSuccess_preparedFrames generated canonical occurrence
        result (valid.eachMatches (List.mem_append_right _ List.mem_cons_self)) incoming available found
      have roots := preparedRoots.successGroupFold_start generated canonical
        incoming.task.groups available
      have finalUncancelled : ref ∉ (activated.drainReadyGroups available).1.cancelledGroups := by
        have safe := retired.uncancelled
        change ref ∉ (current.taskSuccess occurrence result available).1.cancelledGroups at safe
        rw [current.taskSuccess_eq occurrence result incoming found available] at safe
        exact safe
      have prefixes := covered.2.2.2.2.2.2.1 incoming found
      have delivered :=
        State.drainReadyGroups_go_ancestorValue_atOffset available
          (released.2.1.flatMap WorkQueueEvent.objectValues).length generated
          roots.live.records roots.live.links canonical roots.live.registered
          roots.live.tasks roots.live.roots roots.retired
          (by
            simpa only [State.ReleaseDrainOwners, List.flatMap_append, List.length_append]
              using prefixes.drain)
          atDrain record ancestor preparedLookup stored taskOwners owns preparedPresent
          finalUncancelled
      refine ⟨parentResult.value, .inr ?_⟩
      change (Occurrence.executionGroup source, parentResult.value) ∈ localPublications.take
        (((current.taskSuccess occurrence result available).2.1.take position).flatMap
          WorkQueueEvent.objectValues).length
      rw [prefixEq, List.flatMap_append, List.length_append]
      rw [List.take_take] at delivered
      exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
