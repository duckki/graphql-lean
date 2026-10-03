import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementHandlers

/-! Every actual normalized stream announcement is globally unique. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Initialization and the actual raw-event/batch boundaries
-----------------------------------------------------------------------------------------

/-- Initialization supplies the inventory for exactly the initial stream notices.
Witness: empty history and links, fresh root registration, pruning, and activation.
-/
theorem createWorkQueue_streamAnnouncementInventory (work : Work)
    : (State.initialize work).StreamAnnouncementInventory
        ((State.initialize work).initialStreams.map Execution.DeliveryNode.ref) := by
  have empty : ({} : State).StreamAnnouncementInventory [] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro ref impossible; cases impossible
    · intro node impossible; cases impossible
    · intro node impossible; cases impossible
  let integrated := ({} : State).maybeIntegrateWork work
  let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
  have ready := ((empty.maybeIntegrateWork work).pruneEmptyGroups
    integrated.2.newGroups).startNewWork { integrated.2 with newGroups := pruned.2 }
  exact ⟨ready.unique, ready.registered, ready.stored, ready.unreleased⟩

/-- Raw replay consumes announced refs in the exact handler-output order.
Witness: each handler updates the inventory before the next source event; source matching
preserves structural producer identity without any output-admission assumption.
-/
theorem State.StreamAnnouncementInventory.rawEventReplay
    {queue : State} {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (events : List GraphEvent) (sources : ∀ event ∈ events, event.MatchesWork work)
    : (queue.rawEventReplay events).1.StreamAnnouncementInventory
        (announced ++ (queue.rawEventReplay events).2.flatMap rawStreamNoticeRefs) := by
  induction events generalizing queue announced with
  | nil => simpa only [State.rawEventReplay, List.foldl_nil,
      List.flatMap_nil, List.append_nil] using inventory
  | cons event rest ih =>
      have source := sources event List.mem_cons_self
      have next := inventory.handleGraphEvent matching generated source
      have later := ih next (matching.handleGraphEvent source)
        (fun next member => sources next (List.mem_cons_of_mem _ member))
      rw [State.rawEventReplay_cons]
      simpa only [List.flatMap_append, List.append_assoc] using later

/-- Batch handling retains the inventory across empty and terminating outputs.
Witness: raw replay, plus a terminal flag and notice-free terminal control. Later batches
on a terminated queue emit nothing and cannot reannounce an old ref.
-/
theorem State.StreamAnnouncementInventory.handleGraphEvents
    {queue : State} {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (events : List GraphEvent) (sources : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.StreamAnnouncementInventory
        (announced
          ++ (queue.handleGraphEvents events).2.flatMap rawStreamNoticeRefs) := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · simpa only [List.flatMap_nil, List.append_nil] using inventory
  · have replayed := inventory.rawEventReplay matching generated events sources
    dsimp only
    split
    · simp only [List.flatMap_append, List.flatMap_singleton, rawStreamNoticeRefs,
        List.append_nil]
      exact ⟨replayed.unique, replayed.registered, replayed.stored, replayed.unreleased⟩
    · exact replayed

-----------------------------------------------------------------------------------------
-- Owner remapping retains stream refs and their exact order
-----------------------------------------------------------------------------------------

/-- A normalized batch extends the same inventory by its exact observable stream notices.
Witness: normalization leaves stream refs/order unchanged and does not alter queue state.
-/
theorem normalizedStep_streamAnnouncementInventory {work : Execution.Work}
    {announced : NodeRefs} (generated : ExecutedWork work) (acc : NormalizedAcc)
    (batch : List GraphEvent)
    (inventory
      : acc.1.StreamAnnouncementInventory
          (announced ++ acc.2.2.flatten.flatMap streamNoticeRefs))
    (matching : acc.1.ChildStreamsMatchWork work)
    (sources : ∀ event ∈ batch, event.MatchesWork work)
    : (normalizedStep acc batch).1.StreamAnnouncementInventory
        (announced
          ++ (normalizedStep acc batch).2.2.flatten.flatMap streamNoticeRefs) := by
  rw [normalizedStep_queue, normalizedStep_flatten, List.flatMap_append,
    IncrementalPublisher.normalizeBatch_streamNotices, ← List.append_assoc]
  exact inventory.handleGraphEvents matching generated batch sources

/-- Generated matching input yields one fresh stream-announcement history for all batches.
Witness: initialization and the actual normalized fold, retaining both inventory and child
producer provenance. Source freshness, start checks, and abstract admission are not needed.
-/
theorem createWorkQueue_runNormalized_streamAnnouncementInventory {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (sources : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.runNormalized batches).1.StreamAnnouncementInventory
        (queue.initialStreams.map Execution.DeliveryNode.ref
          ++ (queue.runNormalized batches).2.flatten.flatMap streamNoticeRefs) := by
  let initial := State.initialize (Work.fromExecution work)
  let announced := initial.initialStreams.map Execution.DeliveryNode.ref
  have loop (remaining : List (List GraphEvent)) (acc : NormalizedAcc)
      (inventory : acc.1.StreamAnnouncementInventory
        (announced ++ acc.2.2.flatten.flatMap streamNoticeRefs))
      (matching : acc.1.ChildStreamsMatchWork work)
      (sources : ∀ event ∈ remaining.flatten, event.MatchesWork work)
      : (remaining.foldl normalizedStep acc).1.StreamAnnouncementInventory
          (announced ++ (remaining.foldl normalizedStep acc).2.2.flatten.flatMap
            streamNoticeRefs) := by
    induction remaining generalizing acc with
    | nil => exact inventory
    | cons batch rest ih =>
        have source := fun event member => sources event (List.mem_append_left _ member)
        have next := normalizedStep_streamAnnouncementInventory generated acc batch
          inventory matching source
        apply ih _ next
        · rw [normalizedStep_queue]
          exact matching.handleGraphEvents batch source
        · intro event member
          exact sources event (List.mem_append_right _ member)
  exact loop batches
    (initial, { active := initial.initialGroups ++ initial.initialStreams }, [])
    (by
      simpa only [List.flatten_nil, List.flatMap_nil, List.append_nil]
        using createWorkQueue_streamAnnouncementInventory (Work.fromExecution work))
    (createWorkQueue_childStreamsMatchWork _ _) sources

/-- Initial and all later stream-notice refs are globally distinct in actual valid replay.
Witness: project uniqueness from the derived normalized inventory, without assuming any
abstract scheduler admission, matching of output events, or failure-cut certificate.
-/
theorem createWorkQueue_runNormalized_streamNoticeRefs_nodup {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    : let queue := State.initialize (Work.fromExecution work)
      (queue.initialStreams.map Execution.DeliveryNode.ref
        ++ (queue.runNormalized batches).2.flatten.flatMap streamNoticeRefs).Nodup :=
  (createWorkQueue_runNormalized_streamAnnouncementInventory generated batches
    (fun _ member => valid.event_matches member)).unique

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
