import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Item integration and all source handlers preserve protected buffered stream release. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Item preparation retains old buffered nodes and their live contributors
-----------------------------------------------------------------------------------------

/-- Stream-item handling releases or retains every protected buffered child stream.
Witness: root integration, empty-shell pruning, and activation retain old stored nodes and
their contributors. The shared drain then supplies complete release-or-retain conservation.
-/
theorem State.streamItems_bufferedStreamsConserved {queue : State} {work settled}
    (accounted : queue.PendingAccounting work settled) (links : queue.StoredTaskLinks)
    (inventory : queue.ChildStreamInventory) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    : queue.BufferedStreamsConserved (queue.streamItems stream items).2
        (queue.streamItems stream items).1 := by
  let invariant (current : State) :=
    current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
    ∧ current.StartedTasksRegistered ∧ current.StoredTaskLinks ∧ current.ChildStreamInventory
    ∧ (∀ occurrence node, queue.taskNode? occurrence = some node
      → current.taskNode? occurrence = some node)
    ∧ ∀ occurrence node value,
        queue.taskNode? occurrence = some node → node.value = some value
        → ∀ ref ∈ node.task.groups.map Execution.DeliveryNode.ref,
          ref ∈ queue.groupNodes.map (fun owner => owner.group.node.ref)
          → ref ∈ current.groupNodes.map (fun owner => owner.group.node.ref)
  have initial : invariant queue :=
    ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.started,
      links, inventory, fun _ _ found => found, fun _ _ _ _ _ _ _ present => present⟩
  have prepared : invariant (queue.preparedStreamItems items) := by
    apply State.preparedStreamItems_preserves invariant initial items
    intro current item member prior
    obtain ⟨refs, live, registered, started, linked, children, retained, owners⟩ := prior
    have nextRegistry := current.integrateStreamItem_registration live registered matching member
    have integratedLinks := linked.maybeIntegrateWork refs registered started item.work
    refine ⟨((refs.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
      nextRegistry.1, nextRegistry.2.1,
      ((started.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _,
      (integratedLinks.pruneEmptyGroups _).startNewWork _,
      ((children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _, ?_, ?_⟩
    · intro occurrence node found
      apply State.startNewWork_lookup_existing
      change ((current.maybeIntegrateWork item.work).1.pruneEmptyGroups _).1.taskNodes.find? _ = _
      rw [State.pruneEmptyGroups_taskNodes]
      exact State.maybeIntegrateWork_lookup_other (retained occurrence node found) item.work
    · intro occurrence node value found stored ref contributes present
      have integratedLookup := State.maybeIntegrateWork_lookup_other
        (retained occurrence node found) item.work
      have kept := State.pruneEmptyGroups_bufferedOwner_present integratedLinks
        (State.taskNode?_some integratedLookup).1 (by simp [stored]) contributes
        (current.maybeIntegrateWork_includesRefs item.work none ref
          (owners occurrence node value found stored ref contributes present))
        (current.maybeIntegrateWork item.work).2.newGroups
      dsimp only [State.integrateStreamItem]
      rwa [(State.startNewWork_groupCore _ _).1]
  obtain ⟨_, _, _, _, linked, children, retained, owners⟩ := prepared
  rw [queue.streamItems_eq]
  split
  · exact .refl queue
  · intro occurrence node value child found stored attached owner contributes live uncancelled
    have result := State.drainReadyGroups_bufferedStreamsConserved linked children
      occurrence node value child (retained occurrence node found) stored attached owner
      contributes (owners occurrence node value found stored owner contributes live) uncancelled
    exact result.imp_left (List.mem_append_right _)

-----------------------------------------------------------------------------------------
-- One event-level interface uses only internal accounting and source provenance
-----------------------------------------------------------------------------------------

/-- Every fresh matching source handler conserves protected buffered streams.
Witness: success, failure, and item handlers use their concrete conservation theorems;
stream closure modifies neither stored object nodes nor contributing group records.
-/
theorem State.handleGraphEvent_bufferedStreamsConserved {queue : State}
    {work settled before} (accounted : queue.PendingAccounting work settled)
    (links : queue.StoredTaskLinks) (inventory : queue.ChildStreamInventory)
    (sources : queue.StoredValuesSatisfy (ObjectValueFrom before))
    (included : settled.Subset (before.flatMap (fun event => event.identities.1)))
    (event : GraphEvent) (matching : event.MatchesWork work) (fresh : event.Fresh before)
    : queue.BufferedStreamsConserved (queue.handleGraphEvent event).2
        (queue.handleGraphEvent event).1 := by
  cases event with
  | taskSuccess occurrence result =>
      exact State.taskSuccess_bufferedStreamsConserved
        accounted links inventory sources included occurrence result fresh
  | taskFailure occurrence errors =>
      exact State.taskFailure_bufferedStreamsConserved sources occurrence errors fresh
  | streamItems stream items =>
      exact State.streamItems_bufferedStreamsConserved accounted links inventory _ _ matching
  | streamSuccess stream =>
      dsimp only [State.handleGraphEvent, State.streamSuccess]
      split <;> intro occurrence node value child found stored attached owner contributes live _ <;>
        exact .inr ⟨found, live⟩
  | streamFailure stream errors =>
      dsimp only [State.handleGraphEvent, State.streamFailure]
      split <;> intro occurrence node value child found stored attached owner contributes live _ <;>
        exact .inr ⟨found, live⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
