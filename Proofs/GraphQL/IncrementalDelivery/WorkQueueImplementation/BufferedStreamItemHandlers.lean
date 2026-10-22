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
    (available : List (Occurrence × Nat) := [])
    (clean
      : queue.StoredValuesSatisfy
          (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available) := by
        intro node member value stored errors impossible; cases impossible)
    : queue.BufferedStreamsConserved (queue.streamItems stream items available).2.1
        (queue.streamItems stream items available).1 := by
  let invariant (current : State) :=
    current.GroupRefsUnique ∧ current.LiveGroupsRegistered ∧ current.TaskGroupsRegistered
    ∧ current.StartedTasksRegistered ∧ current.StoredTaskLinks ∧ current.ChildStreamInventory
    ∧ current.StoredValuesSatisfy
        (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available)
    ∧ queue.StoredOwnersConserved [] current
    ∧ current.RegistrationFrame work
  have initial : invariant queue :=
    ⟨accounted.refs, accounted.liveGroups, accounted.taskGroups, accounted.started,
      links, inventory, clean, .refl queue, accounted.registration⟩
  have prepared : invariant (queue.preparedStreamItems items available) := by
    apply State.preparedStreamItems_preserves invariant initial items available
    intro current item member prior
    obtain ⟨refs, live, registered, started, linked, children, cleanValues, owners, frame⟩ := prior
    let integrated := current.maybeIntegrateWork item.work
    let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
    let released : NewWork := { integrated.2 with newGroups := pruned.2 }
    have nextRegistry := current.integrateStreamItem_registration live registered matching member
      frame available
    have integratedLinks := linked.maybeIntegrateWork refs registered started item.work
    have prunedClean := (cleanValues.maybeIntegrateWork item.work).pruneEmptyGroups
      integrated.2.newGroups
    have integratedOwners := current.maybeIntegrateWork_storedOwnersConserved item.work
    have prunedOwners := State.pruneEmptyGroups_storedOwnersConserved integratedLinks
      integrated.2.newGroups
    have first : current.StoredOwnersConserved [] pruned.1 := by
      simpa only [List.nil_append]
        using integratedOwners.append prunedOwners (by
          rw [State.pruneEmptyGroups_cancelledGroups]; exact List.Subset.refl _)
    have activated := pruned.1.startNewWork_storedOwnersConserved released available prunedClean
    have itemOwners : current.StoredOwnersConserved []
        (current.integrateStreamItem item available) := by
      simpa only [State.integrateStreamItem, integrated, pruned, released,
        List.nil_append]
        using first.append activated
          (State.startNewWork_cancelledGroups_subset pruned.1 released available)
    have retains : current.cancelledGroups.Subset
        (current.integrateStreamItem item available).cancelledGroups := by
      have middle : current.cancelledGroups.Subset pruned.1.cancelledGroups := by
        dsimp only [pruned, integrated]
        rw [State.pruneEmptyGroups_cancelledGroups, State.maybeIntegrateWork_cancelledGroups]
        exact current.addGroups_cancelledGroups_subset item.work.groups
      exact middle.trans (State.startNewWork_cancelledGroups_subset pruned.1 released available)
    refine ⟨
      ((refs.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _
        available,
      nextRegistry.1,
      nextRegistry.2.1,
      ((started.maybeIntegrateWork item.work none).pruneEmptyGroups _).startNewWork _
        available,
      (integratedLinks.pruneEmptyGroups _).startNewWork _ available,
      ((children.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _
        available,
      prunedClean.startNewWork _ available,
      ?_,
      (frame.integrateStreamItem matching member available).1
    ⟩
    simpa only [List.nil_append] using owners.append itemOwners retains
  obtain ⟨_, _, _, _, linked, children, cleanValues, owners, _⟩ := prepared
  rw [queue.streamItems_eq stream items available]
  split
  · exact .refl queue
  · let folded := items.foldl (fun acc item => streamItemStep acc item available)
      (queue, [], [], [], [])
    exact (State.BufferedStreamsConserved.of_emptyOwners owners
      [.streamValues stream folded.2.2.2.1 folded.2.1 folded.2.2.1]).append
      (State.drainReadyGroups_bufferedStreamsConserved linked children available cleanValues)
      (State.drainReadyGroups_go_cancelledGroups_subset _ _ available)

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
    (available : List (Occurrence × Nat) := [])
    (clean
      : queue.StoredValuesSatisfy
          (fun occurrence _ => ∀ errors, (occurrence, errors) ∉ available) := by
        intro node member value stored errors impossible; cases impossible)
    (own
      : ∀ occurrence result,
          event = .taskSuccess occurrence result
          → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence result same errors impossible; cases impossible)
    : queue.BufferedStreamsConserved (queue.handleGraphEvent event available).2.1
        (queue.handleGraphEvent event available).1 := by
  have cacheOwners : queue.StoredOwnersConserved [] (queue.cacheTaskFailures available) := by
    intro occurrence node value found stored ref contributes live uncancelled
    have safe := clean node (State.taskNode?_some found).1 value stored
    rw [(State.taskNode?_some found).2] at safe
    exact .inr ⟨State.cacheTaskFailures_lookup_existing found available safe,
      by rwa [State.cacheTaskFailures_groupNodes]⟩
  have cached := accounted.cacheTaskFailures available
  have cachedLinks := links.cacheTaskFailures available
  have cachedInventory := inventory.cacheTaskFailures available
  have cachedSources := sources.cacheTaskFailures available
  have cleanValues := clean.cacheTaskFailures available
  have after : (queue.cacheTaskFailures available).BufferedStreamsConserved
      (queue.handleGraphEvent event available).2.1 (queue.handleGraphEvent event available).1 := by
    cases event with
    | taskSuccess occurrence result =>
        exact State.taskSuccess_bufferedStreamsConserved cached cachedLinks cachedInventory
          cachedSources included occurrence result fresh available cleanValues (own _ _ rfl)
    | taskFailure occurrence errors =>
        exact State.taskFailure_bufferedStreamsConserved cachedSources occurrence errors fresh
    | streamItems stream items =>
        exact State.streamItems_bufferedStreamsConserved cached cachedLinks cachedInventory
          _ _ matching available cleanValues
    | streamSuccess stream =>
        dsimp only [State.handleGraphEvent, State.streamSuccess]
        split <;> intro occurrence node value child found stored attached owner
          contributes live _ <;>
          exact .inr ⟨found, live⟩
    | streamFailure stream errors =>
        dsimp only [State.handleGraphEvent, State.streamFailure]
        split <;> intro occurrence node value child found stored attached owner
          contributes live _ <;>
          exact .inr ⟨found, live⟩
    | groupFailure failure =>
        dsimp only [State.handleGraphEvent, State.groupFailure]
        split
        · exact .refl _
        · split <;> intro occurrence node value child found stored attached owner
            contributes live _ <;> exact .inr ⟨found, live⟩
  have cancelled : (queue.cacheTaskFailures available).cancelledGroups.Subset
      (queue.handleGraphEvent event available).1.cancelledGroups := by
    rw [State.cacheTaskFailures_cancelledGroups]
    exact queue.handleGraphEvent_cancelledGroups_subset event available
  simpa only [List.nil_append]
    using (State.BufferedStreamsConserved.of_emptyOwners cacheOwners []).append after
      cancelled

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
