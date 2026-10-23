import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNoticeSnapshotPublication

/-! Stream-carried notice ancestors use actual cached entry buffers and drain prefixes. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A stream notice's earlier successful contributor survives exact rejection caching. -/
theorem OwnerPublicationFrame.streamItems_noticeAncestor_cached_or_published
    {queue work parents before published stream items output child dependencies ref
      address owners producer payload}
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
    (emitted
      : output ∈ (queue.handleGraphEvent (.streamItems stream items) available).2.1)
    (noticed : child.ref ∈ rawGroupNoticeRefs output)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : UncancelledRetirement
        (queue.handleGraphEvent (.streamItems stream items) available).1 ref
      ∧ ∃ value,
          (Occurrence.executionGroup address, value) ∈ published
          ∨ ∃ node,
              (queue.cacheTaskFailures available).taskNode? (.executionGroup address)
                = some node
              ∧ node.value = some value
              ∧ TaskHasOwners work (.executionGroup address)
                  (node.task.groups.map Execution.DeliveryNode.ref)
              ∧ ref ∈ node.task.groups.map Execution.DeliveryNode.ref
              ∧ ref
                ∈ (queue.cacheTaskFailures available).groupNodes.map
                    (fun owner => owner.group.node.ref) := by
  obtain ⟨retired, result, impossible | ⟨earlier, prior | buffered⟩⟩ :=
    frame.noticeAncestor_contributor_accounted generated canonical (.streamItems stream items)
      valid accepted available licensed emitted noticed known ancestor task contributes
  · cases impossible
  · exact ⟨retired, result.value, .inl prior⟩
  · obtain ⟨node, lookup, stored, taskOwners, owns, present⟩ := buffered
    have notAvailable : ∀ errors, (Occurrence.executionGroup address, errors) ∉ available := by
      intro errors cached
      obtain ⟨_, _, success, _, _⟩ := valid.eachMatches (List.mem_append_left _ earlier)
      obtain ⟨_, _, _, failure⟩ := licensed _ errors cached
      cases (success.unique failure).2.2
    exact ⟨retired, result.value, .inr ⟨node,
      State.cacheTaskFailures_lookup_existing lookup available notAvailable, stored,
      taskOwners, owns, by rwa [State.cacheTaskFailures_groupNodes]⟩⟩

/-- A stream-handler successful notice publishes each ancestor buffer before its carrier. -/
theorem OwnerPublicationFrame.streamItems_noticeAncestor_contributor_before
    {queue work parents before published localPublications stream items index group groups
      streams child dependencies ref address owners producer payload}
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
      : queue.ReplayClosuresCovered [.streamItems stream items] localPublications
          available)
    (selected
      : (queue.handleGraphEvent (.streamItems stream items) available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value) ∈ published
        ∨ (Occurrence.executionGroup address, value)
          ∈ localPublications.take
              (((queue.handleGraphEvent (.streamItems stream items) available).2.1.take
                  index).flatMap
                WorkQueueEvent.objectValues).length := by
  obtain ⟨retired, value, prior | ⟨node, lookup, stored, taskOwners, owns, present⟩⟩ :=
    frame.streamItems_noticeAncestor_cached_or_published generated canonical valid accepted
      available licensed (List.mem_of_getElem? selected) (List.mem_map_of_mem noticed)
      known ancestor task contributes
  · exact ⟨value, .inl prior⟩
  · let current := queue.cacheTaskFailures available
    have atHandler : (current.streamItems stream items available).2.1[index]?
        = some (.groupSuccess group groups streams) := selected
    have uncancelled : ref ∉ (current.streamItems stream items available).1.cancelledGroups :=
      retired.uncancelled
    change ∃ value, (Occurrence.executionGroup address, value) ∈ published ∨
      (Occurrence.executionGroup address, value) ∈ localPublications.take
        (((current.streamItems stream items available).2.1.take index).flatMap
          WorkQueueEvent.objectValues).length
    rw [current.streamItems_eq stream items available] at atHandler uncancelled ⊢
    cases openStream : current.rootStreams.contains stream.ref with
    | false =>
        simp only [openStream, Bool.not_false, ↓reduceIte, List.getElem?_nil,
          reduceCtorEq] at atHandler
    | true =>
        simp only [openStream, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          at atHandler uncancelled ⊢
        cases index with
        | zero => cases atHandler
        | succ index =>
            have frames := frame.source.streamItems_preparedFrames generated canonical
              (valid.eachMatches (List.mem_append_right _ List.mem_cons_self)) available
            have roots := frames.2
            have prefixes : current.StreamDrainOwners stream items
                (localPublications.take
                  ((queue.handleGraphEvent (.streamItems stream items) available).2.1.flatMap
                    WorkQueueEvent.objectValues).length) available := covered.2.2.2.2.2.2.1
            have delivered :=
              State.drainReadyGroups_go_noticeAncestorValue_atSnapshot (offset := 0)
                generated roots.live.records roots.live.links canonical
                roots.live.registered roots.live.tasks roots.live.roots roots.retired
                available
                (by
                  simpa only [Nat.zero_add, State.preparedStreamItems, current]
                    using prefixes openStream)
                atHandler noticed known ancestor lookup stored taskOwners owns present
                uncancelled
            refine ⟨value, .inr ?_⟩
            rw [List.take_take] at delivered
            simpa only [Nat.zero_add, List.take_succ_cons, List.flatMap_cons,
              WorkQueueEvent.objectValues, List.nil_append, State.drainReadyGroups,
              State.preparedStreamItems, current]
              using List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

/-- Leading item notices account for ancestor values before any object-producing drain. -/
theorem OwnerPublicationFrame.streamItems_leadingAncestor_contributor_before
    {queue work parents before published localPublications stream items child dependencies
      ref address owners producer payload}
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
      : queue.ReplayClosuresCovered [.streamItems stream items] localPublications
          available)
    (active : (queue.cacheTaskFailures available).rootStreams.contains stream.ref = true)
    (noticed
      : child
        ∈ (items.foldl (fun acc item => streamItemStep acc item available)
            (queue.cacheTaskFailures available, [], [], [], [])).2.1)
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ value, (Occurrence.executionGroup address, value) ∈ published := by
  let current := queue.cacheTaskFailures available
  change current.rootStreams.contains stream.ref = true at active
  let folded := items.foldl (fun acc item => streamItemStep acc item available)
    (current, [], [], [], [])
  have emitted : WorkQueueEvent.streamValues stream folded.2.2.2.1 folded.2.1 folded.2.2.1
      ∈ (queue.handleGraphEvent (.streamItems stream items) available).2.1 := by
    change _ ∈ (current.streamItems stream items available).2.1
    rw [current.streamItems_eq stream items available]
    simp only [active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact List.mem_cons_self
  obtain ⟨_, value, prior | ⟨node, lookup, stored, taskOwners, owns, present⟩⟩ :=
    frame.streamItems_noticeAncestor_cached_or_published generated canonical valid accepted
      available licensed emitted (List.mem_map_of_mem noticed) known ancestor task contributes
  · exact ⟨value, prior⟩
  · have certificates := frame.source.streamItems_preparedNoticeAncestors generated
      canonical valid available licensed
    have retired := certificates child.ref
      (List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_map_of_mem noticed⟩)
      child dependencies known rfl ref ancestor (.executionGroup address) _ taskOwners owns
    have prefixes : current.StreamDrainOwners stream items
        (localPublications.take
          ((queue.handleGraphEvent (.streamItems stream items) available).2.1.flatMap
            WorkQueueEvent.objectValues).length) available := covered.2.2.2.2.2.2.1
    have retained := prefixes active 0 (Nat.zero_le _)
      (.executionGroup address) node value lookup stored ref owns present retired.uncancelled
    rcases retained with impossible | retained
    · simp [State.drainReadyGroups.go] at impossible
    · exact False.elim (retired.retired.2 retained.2)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
