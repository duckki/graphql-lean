import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayValueConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationMonotonicity

/-! Healthy owner retirement forces publication on the common source-replay ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Owner conservation composes without source or registration assumptions
-----------------------------------------------------------------------------------------

/-- Replay preserves each buffered live owner unless its data publishes or it is cancelled.
Witness: compose the stored-owner certificates on consecutive slices of the same ledger.
Actual handler cancellation histories grow, so endpoint health protects earlier owners.
-/
theorem State.ReplayClosuresCovered.conservesOwners {queue : State}
    {available : List (Occurrence × Nat)} {events published}
    (covered : queue.ReplayClosuresCovered events published available)
    : queue.StoredOwnersConserved
        (published.take
          ((queue.rawEventReplay events available).2.flatMap
            WorkQueueEvent.objectValues).length)
        (queue.replayGraphEvents events available) := by
  induction events generalizing queue published with
  | nil => exact .refl queue
  | cons event rest ih =>
      have conserved := covered.2.2.2.2.1.append (ih covered.tail)
        (State.replayGraphEvents_cancelledGroups_subset _ rest available)
      simpa only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
        List.take_add, State.replayGraphEvents, List.foldl_cons] using conserved

/-- A buffered contributor cannot retire silently while leaving its value unpublished.
Witness: replay conservation on its actual object-count prefix; the retained branch would
keep the contributor's ref present. No completion notice for that ref is required.
-/
theorem State.ReplayClosuresCovered.buffered_retired_published {queue : State}
    {available : List (Occurrence × Nat)} {events published occurrence node value ref}
    (covered : queue.ReplayClosuresCovered events published available)
    (found : queue.taskNode? occurrence = some node) (stored : node.value = some value)
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    (retired
      : ref
        ∉ (queue.replayGraphEvents events available).groupNodes.map
            (fun owner => owner.group.node.ref))
    (uncancelled : ref ∉ (queue.replayGraphEvents events available).cancelledGroups)
    : (occurrence, value)
      ∈ published.take
          ((queue.rawEventReplay events available).2.flatMap
            WorkQueueEvent.objectValues).length := by
  rcases covered.conservesOwners occurrence node value found stored ref contributes
      present uncancelled with emitted | retained
  · exact emitted
  · exact False.elim (retired retained.2)

-----------------------------------------------------------------------------------------
-- A newly settled value inherits the same guarantee from its prepared task map
-----------------------------------------------------------------------------------------

/-- A processed success conserves its prepared owners through all later source inputs.
Witness: compose the first handler's prepared-owner certificate with ordinary replay
conservation, retaining the common ledger and its exact total object-output bound.
-/
theorem State.ReplayClosuresCovered.success_conservesOwners {queue : State}
    {available : List (Occurrence × Nat)} {occurrence result rest published node}
    (covered
      : queue.ReplayClosuresCovered (.taskSuccess occurrence result :: rest) published
          available)
    (found : (queue.cacheTaskFailures available).taskNode? occurrence = some node)
    : (((queue.cacheTaskFailures available).putTaskNode
          { node with value := some result.value }).maybeIntegrateWork
        result.work (some occurrence)).1.StoredOwnersConserved
        (published.take
          ((queue.rawEventReplay (.taskSuccess occurrence result :: rest)
              available).2.flatMap
            WorkQueueEvent.objectValues).length)
        (queue.replayGraphEvents (.taskSuccess occurrence result :: rest) available) := by
  have conserved := (covered.2.2.2.2.2.1 node found).append
    covered.tail.conservesOwners
    (by
      change List.Subset
        (queue.dispatchGraphEvent (.taskSuccess occurrence result) available).1.cancelledGroups _
      exact State.replayGraphEvents_cancelledGroups_subset _ rest available)
  simpa only [State.rawEventReplay_cons, List.flatMap_append, List.length_append,
    List.take_add, State.replayGraphEvents, List.foldl_cons, State.dispatchGraphEvent,
    State.enqueueGroupFailures, State.handleGraphEvent]
    using conserved

/-- An accepted success either publishes or retains its exact buffered value and live owner.
Witness: its prepared value is installed with the same task identity; owner conservation
follows that node through the remaining source inputs on the supplied ledger prefix.
-/
theorem State.ReplayClosuresCovered.success_published_or_buffered {queue : State}
    {available : List (Occurrence × Nat)} {occurrence result rest published node ref}
    (covered
      : queue.ReplayClosuresCovered (.taskSuccess occurrence result :: rest) published
          available)
    (found : (queue.cacheTaskFailures available).taskNode? occurrence = some node)
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    (uncancelled
      : ref
        ∉ (queue.replayGraphEvents
            (.taskSuccess occurrence result :: rest) available).cancelledGroups)
    : (occurrence, result.value)
        ∈ published.take
            ((queue.rawEventReplay (.taskSuccess occurrence result :: rest)
                available).2.flatMap
              WorkQueueEvent.objectValues).length
      ∨ ∃ buffered,
          (queue.replayGraphEvents (.taskSuccess occurrence result :: rest)
              available).taskNode?
              occurrence
            = some buffered
          ∧ buffered.value = some result.value
          ∧ ref ∈ buffered.task.groups.map Execution.DeliveryNode.ref
          ∧ ref
            ∈ (queue.replayGraphEvents
                (.taskSuccess occurrence result :: rest) available).groupNodes.map
                (fun owner => owner.group.node.ref) := by
  obtain ⟨buffered, installed, sameTask, stored⟩ := State.taskSuccess_prepared_value found result
  have preparedPresent := State.maybeIntegrateWork_includesRefs
    ((queue.cacheTaskFailures available).putTaskNode { node with value := some result.value })
    result.work (some occurrence) ref
      (by simpa only [State.putTaskNode, State.cacheTaskFailures_groupNodes] using present)
  have bufferedContributes := sameTask.symm ▸ contributes
  rcases covered.success_conservesOwners found occurrence buffered result.value
      installed stored ref bufferedContributes preparedPresent uncancelled with emitted | retained
  · exact Or.inl emitted
  · exact Or.inr ⟨buffered, retained.1, stored, bufferedContributes, retained.2⟩

/-- A settled success is published by the retirement of any initially live healthy owner.
Witness: exact prepared storage and preserved owner registration supply replay's owner
conservation theorem. Healthy disappearance excludes retention, even without a notice.
-/
theorem State.ReplayClosuresCovered.success_retired_published {queue : State}
    {available : List (Occurrence × Nat)} {occurrence result rest published node ref}
    (covered
      : queue.ReplayClosuresCovered (.taskSuccess occurrence result :: rest) published
          available)
    (found : (queue.cacheTaskFailures available).taskNode? occurrence = some node)
    (contributes : ref ∈ node.task.groups.map Execution.DeliveryNode.ref)
    (present : ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref))
    (retired
      : ref
        ∉ (queue.replayGraphEvents
            (.taskSuccess occurrence result :: rest) available).groupNodes.map
            (fun owner => owner.group.node.ref))
    (uncancelled
      : ref
        ∉ (queue.replayGraphEvents
            (.taskSuccess occurrence result :: rest) available).cancelledGroups)
    : (occurrence, result.value)
      ∈ published.take
          ((queue.rawEventReplay (.taskSuccess occurrence result :: rest)
              available).2.flatMap
            WorkQueueEvent.objectValues).length := by
  exact Or.resolve_right
    (covered.success_published_or_buffered found contributes present uncancelled)
    (fun ⟨_, _, _, _, live⟩ => retired live)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
