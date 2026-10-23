import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskProducerSnapshotPublication

/-! Actual item-handler drains publish ancestor producers before their child value blocks. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Stream preparation conserves the earlier producer on the same strict drain ledger. -/
theorem OwnerPublicationFrame.streamItems_ancestorProducer_beforeValue
    {queue work parents before published localPublications stream items position group
      values address owners source payload dependencies ref parentOwners parentProducer
      parentPayload}
    (frame : OwnerPublicationFrame queue work parents before published)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (accepted : queue.acceptsGraphEvent (.streamItems stream items) = true)
    (available : List (Occurrence × Nat))
    (licensed
      : ∀ task errors,
          (task, errors) ∈ available
          → (GraphEvent.taskFailure task errors).MatchesWork work)
    (covered
      : queue.ReplayClosuresCovered [.streamItems stream items]
          localPublications available)
    (selected
      : (queue.handleGraphEvent (.streamItems stream items) available).2.1[position]?
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
              (((queue.handleGraphEvent (.streamItems stream items) available).2.1.take
                  position).flatMap
                WorkQueueEvent.objectValues).length := by
  let current := queue.cacheTaskFailures available
  obtain ⟨groups, streams, next⟩ := (queue.handleGraphEvent_publicationPairs
    (.streamItems stream items) available).next selected
  obtain ⟨retired, parentResult, succeeded, prior | buffered⟩ := frame.ancestorProducer_accounted
    generated canonical valid accepted available licensed (List.mem_of_getElem? next)
    known contributes record ancestor parentKnown parentContributes
  · exact ⟨parentResult.value, .inl prior⟩
  · obtain ⟨node, lookup, stored, taskOwners, owns, present⟩ := buffered
    obtain ⟨active, index, atDrain, prefixEq, finalEq⟩ :=
      current.streamItems_value_boundary stream items available selected
    obtain ⟨_, roots⟩ := frame.source.streamItems_preparedFrames generated canonical
      (valid.eachMatches (List.mem_append_right _ List.mem_cons_self)) available
    have uncancelled : ref ∉ ((current.preparedStreamItems items available).drainReadyGroups
        available).1.cancelledGroups := by
      rw [← finalEq]
      exact retired.uncancelled
    have prefixes := covered.2.2.2.2.2.2.1
    have delivered := State.drainReadyGroups_go_ancestorValue_before available generated
      roots.live.records roots.live.links canonical roots.live.registered roots.live.tasks
      roots.live.roots roots.retired (prefixes active) atDrain record ancestor lookup
      stored taskOwners owns present uncancelled
    refine ⟨parentResult.value, .inr ?_⟩
    change (Occurrence.executionGroup source, parentResult.value) ∈ localPublications.take
      (((current.streamItems stream items available).2.1.take position).flatMap
        WorkQueueEvent.objectValues).length
    rw [prefixEq]
    rw [List.take_take] at delivered
    exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

/-- Either successful handler preserves strict ancestor-producer publication order. -/
theorem OwnerPublicationFrame.ancestorProducer_beforeValue
    {queue work parents before published localPublications event position group values
      address owners source payload dependencies ref parentOwners parentProducer
      parentPayload}
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
    (covered : queue.ReplayClosuresCovered [event] localPublications available)
    (selected
      : (queue.handleGraphEvent event available).2.1[position]?
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
              (((queue.handleGraphEvent event available).2.1.take position).flatMap
                WorkQueueEvent.objectValues).length := by
  cases event with
  | taskSuccess occurrence result =>
      exact frame.taskSuccess_ancestorProducer_beforeValue generated canonical valid accepted
        available licensed covered selected known contributes record ancestor parentKnown
        parentContributes
  | streamItems stream items =>
      exact frame.streamItems_ancestorProducer_beforeValue generated canonical valid accepted
        available licensed covered selected known contributes record ancestor parentKnown
        parentContributes
  | taskFailure occurrence errors =>
      obtain ⟨groups, streams, next⟩ := (queue.handleGraphEvent_publicationPairs
        (.taskFailure occurrence errors) available).next selected
      exact False.elim ((queue.cacheTaskFailures available).taskFailure_noGroupSuccess
        occurrence errors group groups streams (List.mem_of_getElem? next))
  | streamSuccess stream =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamSuccess] at member
      split at member <;> simp at member
  | streamFailure stream errors =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.streamFailure] at member
      split at member <;> simp at member
  | groupFailure notice =>
      have member := List.mem_of_getElem? selected
      simp only [State.handleGraphEvent, State.groupFailure] at member
      split at member
      · cases member
      · split at member <;> simp at member

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
