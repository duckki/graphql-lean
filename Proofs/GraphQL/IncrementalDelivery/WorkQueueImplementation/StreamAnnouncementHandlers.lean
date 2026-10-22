import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementRelease

/-! Actual source handlers preserve globally fresh stream announcements. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List β) (current : α) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

-----------------------------------------------------------------------------------------
-- Task-produced streams are announced only by consuming their stored links
-----------------------------------------------------------------------------------------

/-- Integrating task-produced work retains all new stream refs as unannounced links.
Witness: the generic integration inventory and the empty immediate task-stream frontier.
-/
theorem State.StreamAnnouncementInventory.integrateTask {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (work : Work) (occurrence : Occurrence)
    : (queue.maybeIntegrateWork work (some occurrence)).1.StreamAnnouncementInventory
        announced := by
  have silent : (queue.maybeIntegrateWork work (some occurrence)).2.newStreams = [] := by
    change ((work.tasks.foldl State.addTask (queue.addGroups work.groups).1).addStreams
      work.streams (some occurrence)).2 = []
    simp only [State.addStreams]
    split <;> rfl
  simpa only [silent, List.map_nil, List.append_nil]
    using inventory.maybeIntegrateWork work (some occurrence)

/-- One shared-owner step consumes only unannounced stream refs and preserves provenance.
Witness: cache updates preserve links; a successful flush consumes its selected producers
before the next contributor is processed.
-/
theorem successGroupStep_streamAnnouncementInventory {work : Execution.Work}
    {announced : NodeRefs} (generated : ExecutedWork work)
    (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
    (inventory
      : acc.1.StreamAnnouncementInventory
          (announced ++ acc.2.1.flatMap rawStreamNoticeRefs))
    (matching : acc.1.ChildStreamsMatchWork work)
    : (successGroupStep acc group).1.StreamAnnouncementInventory
        (announced ++ (successGroupStep acc group).2.1.flatMap rawStreamNoticeRefs)
      ∧ (successGroupStep acc group).1.ChildStreamsMatchWork work := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨inventory, matching⟩
  · rename_i node found
    split
    · let updated := { node with pending := node.pending - 1 }
      have flushed := (inventory.putGroupNode updated).finishGroupSuccess
        (matching.putGroupNode updated) generated updated
      refine ⟨?_, (matching.putGroupNode _).finishGroupSuccess _⟩
      simpa only [List.flatMap_append, ← State.finishGroupSuccess_streamNotices,
        List.append_assoc] using flushed
    · exact ⟨inventory.putGroupNode _, matching.putGroupNode _⟩

/-- Task success preserves announcement uniqueness through all owners and the final drain.
Witness: fresh attachment followed by sequential consumption of stored links; matched child
work preserves structural producer identity across preparation and every release.
-/
theorem State.StreamAnnouncementInventory.taskSuccess {queue : State}
    {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    {occurrence result}
    (source : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.StreamAnnouncementInventory
        (announced
          ++ (queue.taskSuccess occurrence result available).2.1.flatMap
              rawStreamNoticeRefs) := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simpa only [State.taskSuccess, found, List.flatMap_nil, List.append_nil]
        using inventory
  | some node =>
      have member := (State.taskNode?_some found).1
      have installed := inventory.storeValue member result.value
      have integrated := installed.integrateTask result.work occurrence
      have provenance := (matching.putTaskNode { node with value := some result.value }
        (matching node member)).maybeIntegrateWork result.work (some occurrence) (by
          intro other same stream supplied
          cases same
          exact source.childStream_producer supplied)
      have loop (groups : List Execution.DeliveryNode)
          (acc : State × List WorkQueueEvent × NewWork)
          (prior : acc.1.StreamAnnouncementInventory
            (announced ++ acc.2.1.flatMap rawStreamNoticeRefs))
          (links : acc.1.ChildStreamsMatchWork work)
          : (groups.foldl successGroupStep acc).1.StreamAnnouncementInventory
              (announced ++ (groups.foldl successGroupStep acc).2.1.flatMap rawStreamNoticeRefs)
            ∧ (groups.foldl successGroupStep acc).1.ChildStreamsMatchWork work := by
        induction groups generalizing acc with
        | nil => exact ⟨prior, links⟩
        | cons group rest ih =>
            have next :=
              successGroupStep_streamAnnouncementInventory generated acc group prior links
            exact ih _ next.1 next.2
      have folded := loop node.task.groups (_, [], {})
        (by simpa only [List.flatMap_nil, List.append_nil] using integrated) provenance
      rw [queue.taskSuccess_eq occurrence result node found available]
      let withValue := queue.putTaskNode { node with value := some result.value }
      let prepared := (withValue.maybeIntegrateWork result.work (some occurrence)).1
      let released := node.task.groups.foldl successGroupStep (prepared, [], {})
      have drained := (folded.1.startNewWork released.2.2 available).drainReadyGroups
        (folded.2.startNewWork released.2.2 available) generated available
      simpa only [List.flatMap_append, List.append_assoc] using drained

-----------------------------------------------------------------------------------------
-- Item-produced roots are announced immediately, then the shared drain runs
-----------------------------------------------------------------------------------------

/-- Every item fold preserves inventory for all stream notices accumulated so far.
Witness: each root integration announces fresh refs before subsequent items register work;
pruning and activation preserve both link freshness and structural provenance.
-/
theorem streamItemFold_streamAnnouncementInventory {work : Execution.Work}
    {announced : NodeRefs} (items : List StreamItem)
    (acc
      : State
        × List Execution.DeliveryNode
        × List Execution.DeliveryNode
        × List StreamItemValue
        × List GroupFailureEvent)
    (inventory
      : acc.1.StreamAnnouncementInventory
          (announced ++ acc.2.2.1.map Execution.DeliveryNode.ref))
    (matching : acc.1.ChildStreamsMatchWork work)
    (available : List (Occurrence × Nat) := [])
    : (items.foldl (fun current item => streamItemStep current item available)
        acc).1.StreamAnnouncementInventory
        (announced
          ++ (items.foldl (fun current item => streamItemStep current item available)
                acc).2.2.1.map
              Execution.DeliveryNode.ref)
      ∧ (items.foldl (fun current item => streamItemStep current item available)
          acc).1.ChildStreamsMatchWork
          work := by
  induction items generalizing acc with
  | nil => exact ⟨inventory, matching⟩
  | cons item rest ih =>
      apply ih
      · let integrated := acc.1.maybeIntegrateWork item.work
        let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
        have next := ((inventory.maybeIntegrateWork item.work).pruneEmptyGroups
          integrated.2.newGroups).startNewWork { integrated.2 with newGroups := pruned.2 } available
        simpa only [streamItemStep, List.map_append, List.append_assoc] using next
      · exact ((matching.integrateRoots item.work).pruneEmptyGroups _).startNewWork _ available

/-- Stream-item processing preserves globally fresh notices in its carrier and drain.
Witness: the complete item fold consumes fresh roots; the following drain consumes only
remaining stored links, so its notices cannot repeat the leading item's notices.
-/
theorem State.StreamAnnouncementInventory.streamItems
    {queue : State} {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (stream : Execution.DeliveryNode) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.StreamAnnouncementInventory
        (announced
          ++ (queue.streamItems stream items available).2.1.flatMap
              rawStreamNoticeRefs) := by
  rw [queue.streamItems_eq stream items available]
  split
  · simpa only [List.flatMap_nil, List.append_nil] using inventory
  · have prepared := streamItemFold_streamAnnouncementInventory items (queue, [], [], [], [])
        (by simpa only [List.map_nil, List.append_nil] using inventory) matching available
    have drained := prepared.1.drainReadyGroups prepared.2 generated available
    simpa only [List.flatMap_cons, rawStreamNoticeRefs, List.append_assoc] using drained

/-- Every matching graph event extends the inventory by exactly its raw stream notices.
Witness: task and item handlers preserve consumption; closure-only inputs change no links.
-/
theorem State.StreamAnnouncementInventory.handleGraphEvent
    {queue : State} {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    {event : GraphEvent} (source : event.MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.StreamAnnouncementInventory
        (announced
          ++ (queue.handleGraphEvent event available).2.1.flatMap
              rawStreamNoticeRefs) := by
  have cached := inventory.cacheTaskFailures available
  have links := matching.cacheTaskFailures available
  cases event with
  | taskSuccess => exact cached.taskSuccess links generated source available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items =>
      exact cached.streamItems links generated stream items available
  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simpa only [List.flatMap_nil, List.append_nil] using cached
      · split <;> simp only [List.flatMap_nil, List.flatMap_singleton,
          rawStreamNoticeRefs, List.append_nil] <;>
          exact ⟨cached.unique, cached.registered, cached.stored, cached.unreleased⟩
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp only [List.flatMap_nil, List.flatMap_singleton, rawStreamNoticeRefs,
        List.append_nil] <;>
        exact ⟨cached.unique, cached.registered, cached.stored, cached.unreleased⟩
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp only [List.flatMap_nil, List.flatMap_singleton, rawStreamNoticeRefs,
        List.append_nil] <;>
        exact ⟨cached.unique, cached.registered, cached.stored, cached.unreleased⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
