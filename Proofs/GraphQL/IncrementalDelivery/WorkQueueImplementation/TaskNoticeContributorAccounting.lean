import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeContributorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredValueRetention

/-! Actual task notices identify exact prepared ancestor buffers on the shared ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An actual task-notice ancestor contributor is prior output or an exact prepared buffer.
Earlier source successes cannot be in the rejection snapshot or be this fresh task input.
The current success installs its own value and retains each uncancelled contributor. -/
theorem OwnerPublicationFrame.taskSuccess_noticeAncestor_prepared_or_published
    {queue work parents before published occurrence result output child dependencies ref
      address owners producer payload incoming}
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
    (emitted
      : output ∈ (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    (found : (queue.cacheTaskFailures available).taskNode? occurrence = some incoming)
    : let current := queue.cacheTaskFailures available
      let stored := current.putTaskNode { incoming with value := some result.value }
      let prepared := (stored.maybeIntegrateWork result.work (some occurrence)).1
      UncancelledRetirement
        (queue.handleGraphEvent (.taskSuccess occurrence result) available).1 ref
      ∧ ∃ value,
          (Occurrence.executionGroup address, value) ∈ published
          ∨ ∃ node,
              prepared.taskNode? (.executionGroup address) = some node
              ∧ node.value = some value
              ∧ TaskHasOwners work (.executionGroup address)
                  (node.task.groups.map Execution.DeliveryNode.ref)
              ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
              ∧ ref ∈ prepared.groupNodes.map (fun owner => owner.group.node.ref) := by
  intro current stored prepared
  obtain ⟨retired, sourceResult, currentSource | ⟨earlier, emittedBefore | buffered⟩⟩ :=
    frame.noticeAncestor_contributor_accounted generated canonical (.taskSuccess occurrence result)
      valid accepted available licensed emitted noticed known ancestor task contributes
  · obtain ⟨rfl, rfl⟩ := GraphEvent.taskSuccess.inj currentSource
    have cached := frame.source.pending.cacheTaskFailures available
    have lookup := State.taskNode?_some found
    have registered := cached.started incoming lookup.1
    obtain ⟨_, birthPayload, birth, _, descriptor⟩ := (cached.matching incoming.task registered).1
    have sameOwners := (TaskAt.unique (lookup.2 ▸ descriptor) task).1
    have incomingOwns := sameOwners.symm ▸ contributes
    have fresh := (validGraphEvents_last valid).2.2
    have unsettled : incoming.task.occurrence ∉ GraphEvent.groupSettlements before := by
      rw [lookup.2]
      exact fun member => fresh.2.2.1 _ List.mem_cons_self
        (GraphEvent.groupSettlements_subsetIdentities before member)
    have uncancelled : ref ∉ current.cancelledGroups := by
      rw [State.cacheTaskFailures_cancelledGroups]
      exact fun member => retired.uncancelled
        (queue.handleGraphEvent_cancelledGroups_subset _ available member)
    obtain ⟨owner, live, sameRef, _⟩ := (frame.source.owners.cacheTaskFailures available)
      incoming.task registered unsettled ref incomingOwns uncancelled
    have present : ref ∈ current.groupNodes.map (fun owner => owner.group.node.ref) :=
      List.mem_map.mpr ⟨owner, live, sameRef⟩
    have taskOwners : TaskHasOwners work (.executionGroup address)
        (incoming.task.groups.map Execution.DeliveryNode.ref) :=
      ⟨birth, birthPayload, lookup.2 ▸ descriptor⟩
    obtain ⟨node, installed, sameTask, storedValue⟩ := State.taskSuccess_prepared_value found result
    exact ⟨retired, result.value, .inr ⟨node, installed, storedValue,
      sameTask.symm ▸ taskOwners, sameTask.symm ▸ incomingOwns,
      State.maybeIntegrateWork_includesRefs
        (current.putTaskNode { incoming with value := some result.value }) result.work
        (some (.executionGroup address)) ref present⟩⟩
  · exact ⟨retired, sourceResult.value, .inl emittedBefore⟩
  · obtain ⟨node, lookup, stored, taskOwners, owns, present⟩ := buffered
    have notAvailable : ∀ errors, (Occurrence.executionGroup address, errors) ∉ available := by
      intro errors cached
      obtain ⟨_, _, success, _, _⟩ := valid.eachMatches (List.mem_append_left _ earlier)
      obtain ⟨_, _, _, failure⟩ := licensed _ errors cached
      cases (success.unique failure).2.2
    have cachedLookup := State.cacheTaskFailures_lookup_existing lookup available notAvailable
    have fresh := (validGraphEvents_last valid).2.2
    have different : occurrence ≠ .executionGroup address := by
      intro same
      apply fresh.2.2.1 occurrence List.mem_cons_self
      rw [same]
      exact GraphEvent.successes_mem_settled
        (List.mem_flatMap.mpr ⟨_, earlier, List.mem_cons_self⟩)
    have retained := State.putTaskNode_lookup_other cachedLookup
      { incoming with value := some result.value }
      ((State.taskNode?_some found).2 ▸ different)
    have currentPresent : ref ∈ current.groupNodes.map (fun owner => owner.group.node.ref) := by
      rwa [State.cacheTaskFailures_groupNodes]
    exact ⟨retired, sourceResult.value, .inr ⟨node,
      State.maybeIntegrateWork_lookup_other retained result.work (some occurrence)
        (fun same => different (Option.some.inj same)), stored, taskOwners, owns,
      State.maybeIntegrateWork_includesRefs
        (current.putTaskNode { incoming with value := some result.value }) result.work
        (some occurrence) ref currentPresent⟩⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
