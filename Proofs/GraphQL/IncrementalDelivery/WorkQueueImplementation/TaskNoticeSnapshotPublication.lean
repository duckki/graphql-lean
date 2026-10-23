import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNoticeContributorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerPreparedFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorDrainPublication

/-! Strict task-notice publication at an actual source cut and batch snapshot. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Prepared ancestor buffers precede their task-success notice under the actual snapshot. -/
theorem UncancelledReplayFrame.taskSuccess_noticeAncestor_bufferBefore
    {queue work parents before occurrence result incoming published}
    {index group groups streams child dependencies ref buffered node value}
    (frame : UncancelledReplayFrame queue work parents before)
    (generated : ExecutedWork work)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (matched : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    (known : GroupRecordAt work child dependencies) (ancestor : ref ∈ dependencies)
    (task : TaskHasOwners work buffered (node.task.groups.map Execution.DeliveryNode.ref))
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (stored : node.value = some value)
    : let current := queue.cacheTaskFailures available
      let storedQueue := current.putTaskNode { incoming with value := some result.value }
      let prepared := (storedQueue.maybeIntegrateWork result.work (some occurrence)).1
      current.PreparedReleaseOwners (.taskSuccess occurrence result) published available
      → current.taskNode? occurrence = some incoming
      → prepared.taskNode? buffered = some node
      → ref ∈ prepared.groupNodes.map (fun owner => owner.group.node.ref)
      → (current.taskSuccess occurrence result available).2.1[index]?
        = some (.groupSuccess group groups streams)
      → child ∈ groups
      → ref ∉ (current.taskSuccess occurrence result available).1.cancelledGroups
      → (buffered, value)
        ∈ published.take
            (((current.taskSuccess occurrence result available).2.1.take index).flatMap
              WorkQueueEvent.objectValues).length := by
  intro current storedQueue prepared prefixes found lookup present selected noticed uncancelled
  let released := incoming.task.groups.foldl successGroupStep (prepared, [], {})
  let active := (released.1.startNewWork released.2.2 available).1
  have equation : current.taskSuccess occurrence result available
      = (active.drainReadyGroups available |>.1,
          released.2.1 ++ (active.drainReadyGroups available).2.1,
          (released.1.startNewWork released.2.2 available).2
            ++ (active.drainReadyGroups available).2.2) := by
    rw [current.taskSuccess_eq occurrence result incoming found available]
  obtain ⟨preparedParent, preparedRoots⟩ := frame.taskSuccess_preparedFrames generated canonical
    occurrence result matched incoming available found
  have activeRoots := preparedRoots.successGroupFold_start generated canonical
    incoming.task.groups available
  rw [equation] at selected uncancelled ⊢
  dsimp only at selected uncancelled ⊢
  by_cases inFold : index < released.2.1.length
  · rw [List.getElem?_append_left inFold] at selected
    rw [List.take_append_of_le_length (Nat.le_of_lt inFold)]
    have preparedUncancelled : ref ∉ prepared.cancelledGroups := by
      intro member
      apply uncancelled
      apply State.drainReadyGroups_go_cancelledGroups_subset
      apply State.startNewWork_cancelledGroups_subset
      simpa only [released, successGroupFold_cancelledGroups] using member
    exact (prefixes incoming found).ownerCarrier_ancestorValue generated preparedParent.records
      preparedParent.links canonical preparedParent.live preparedParent.tasks
      preparedRoots.live.roots selected noticed known ancestor lookup stored task
      contributes present preparedUncancelled
  · have inDrain : released.2.1.length ≤ index := by omega
    rw [List.getElem?_append_right inDrain] at selected
    rw [List.take_append, List.take_of_length_le inDrain]
    have conserved : ∀ steps, steps ≤ active.groupNodes.length →
        prepared.StoredOwnersConserved
          (published.take ((released.2.1.flatMap WorkQueueEvent.objectValues).length
            + ((State.drainReadyGroups.go available steps active).2.1.flatMap
              WorkQueueEvent.objectValues).length))
          (State.drainReadyGroups.go available steps active).1 := by
      simpa only [State.ReleaseDrainOwners, List.flatMap_append, List.length_append]
        using (prefixes incoming found).drain
    have delivered := State.drainReadyGroups_go_noticeAncestorValue_atSnapshot generated
      activeRoots.live.records activeRoots.live.links canonical activeRoots.live.registered
      activeRoots.live.tasks activeRoots.live.roots activeRoots.retired available
      conserved selected noticed known ancestor lookup stored task contributes present uncancelled
    simpa only [List.flatMap_append, List.length_append, State.drainReadyGroups]
      using delivered

/-- Every task-notice ancestor contributor precedes the carrier on the actual two ledgers. -/
theorem OwnerPublicationFrame.taskSuccess_noticeAncestor_contributor_before
    {queue work parents before published localPublications occurrence result index
      group groups streams child dependencies ref address owners producer payload}
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
      : (queue.handleGraphEvent (.taskSuccess occurrence result) available).2.1[index]?
        = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : ref ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : ref ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value) ∈ published
        ∨ (Occurrence.executionGroup address, value)
          ∈ localPublications.take
              (((queue.handleGraphEvent (.taskSuccess occurrence result)
                  available).2.1.take
                  index).flatMap
                WorkQueueEvent.objectValues).length := by
  let current := queue.cacheTaskFailures available
  have currentSelected : (current.taskSuccess occurrence result available).2.1[index]?
      = some (.groupSuccess group groups streams) := selected
  cases found : current.taskNode? occurrence with
  | none => simp [State.taskSuccess, found] at currentSelected
  | some incoming =>
      obtain ⟨retired, value, prior | ⟨node, lookup, stored, taskOwners, owns, present⟩⟩ :=
        frame.taskSuccess_noticeAncestor_prepared_or_published generated canonical valid
          accepted available licensed (List.mem_of_getElem? selected)
          (List.mem_map_of_mem noticed) known ancestor task contributes found
      · exact ⟨value, .inl prior⟩
      · refine ⟨value, .inr ?_⟩
        have delivered := frame.source.taskSuccess_noticeAncestor_bufferBefore generated
          canonical (valid.eachMatches (List.mem_append_right _ List.mem_cons_self))
          available known ancestor taskOwners owns stored
          covered.2.2.2.2.2.2.1 found lookup present currentSelected noticed
          retired.uncancelled
        rw [List.take_take] at delivered
        exact List.take_subset_take_left _ (Nat.min_le_left _ _) delivered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
