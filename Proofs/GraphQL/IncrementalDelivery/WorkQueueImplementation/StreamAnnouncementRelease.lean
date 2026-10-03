import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeRegistry

/-! Cleanup, activation, and draining preserve the consumable stream-notice inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

private theorem fold_preserves {α β : Type} (property : α → Prop) (step : α → β → α)
    (preserved : ∀ current item, property current → property (step current item))
    (items : List β) (current : α) (prior : property current)
    : property (items.foldl step current) := by
  induction items generalizing current with
  | nil => exact prior
  | cons item rest ih => exact ih _ (preserved current item prior)

-----------------------------------------------------------------------------------------
-- Silent cleanup and activation
-----------------------------------------------------------------------------------------

/-- Updating a group cache preserves announcement inventory definitionally.
Witness: no task link or stream-registry field changes.
-/
theorem State.StreamAnnouncementInventory.putGroupNode {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (group : GroupNode)
    : (queue.putGroupNode group).StreamAnnouncementInventory announced :=
  ⟨inventory.unique, inventory.registered, inventory.stored, inventory.unreleased⟩

/-- Installing a settled value preserves its original task links.
Witness: the replacement and all surviving nodes retain their old child lists.
-/
theorem State.StreamAnnouncementInventory.storeValue {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    {node : TaskNode} (member : node ∈ queue.taskNodes) (value : ExecutionGroupValue)
    : (queue.putTaskNode { node with value := some value }).StreamAnnouncementInventory
        announced := by
  apply inventory.of_frame
  · exact List.Subset.refl _
  intro next included
  obtain ⟨old, stored, same⟩ := List.mem_map.mp included
  split at same
  · subst next; exact .inr ⟨node, member, rfl⟩
  · subst next; exact .inr ⟨old, stored, rfl⟩

/-- Deleting a task preserves all remaining unannounced links.
Witness: task-map inclusion with unchanged registration.
-/
theorem State.StreamAnnouncementInventory.removeTask {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (occurrence : Occurrence)
    : (queue.removeTask occurrence).StreamAnnouncementInventory announced :=
  inventory.of_frame (List.Subset.refl _)
    (fun node member => .inr ⟨node, (State.removeTask_node member).1, rfl⟩)

/-- Failure cleanup cannot introduce a previously announced stored link.
Witness: the surviving-node filter and unchanged descriptor registry.
-/
theorem State.StreamAnnouncementInventory.removeGroup {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (ref : NodeRef)
    : (queue.removeGroup ref).StreamAnnouncementInventory announced :=
  inventory.of_frame (List.Subset.refl _)
    (fun node member => .inr ⟨node, (List.mem_filter.mp member).1, rfl⟩)

/-- Empty-group pruning does not affect stream announcements or stored child lists.
Witness: both relevant exact field projections.
-/
theorem State.StreamAnnouncementInventory.pruneEmptyGroups {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.StreamAnnouncementInventory announced := by
  apply inventory.of_frame
  · rw [State.pruneEmptyGroups_streams]; exact List.Subset.refl _
  · intro node member
    rw [State.pruneEmptyGroups_taskNodes] at member
    exact .inr ⟨node, member, rfl⟩

/-- Task starts retain existing links or create an empty child list.
Witness: inspect the two lookup guards; streams remain unchanged.
-/
theorem State.StreamAnnouncementInventory.startTask {queue : State} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced) (occurrence : Occurrence)
    : (queue.startTask occurrence).StreamAnnouncementInventory announced := by
  unfold State.startTask
  split
  · exact inventory
  · split
    · exact inventory
    · apply inventory.of_frame
      · exact List.Subset.refl _
      · intro node member
        rcases List.mem_append.mp member with old | new
        · exact .inr ⟨node, old, rfl⟩
        · exact .inl (List.mem_singleton.mp new ▸ rfl)

/-- Starting a group preserves unannounced child links while starting its tasks.
Witness: task-start preservation through the actual membership fold.
-/
theorem State.StreamAnnouncementInventory.startGroup {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (ref : NodeRef)
    : (queue.startGroup ref).StreamAnnouncementInventory announced := by
  unfold State.startGroup
  split
  · exact inventory
  · split
    · exact inventory
    · exact fold_preserves (fun current => current.StreamAnnouncementInventory announced)
        State.startTask (fun _ occurrence prior => prior.startTask occurrence) _ _ inventory

/-- New-work activation retains the complete announcement inventory.
Witness: group starts preserve task links; stream starts change only active roots.
-/
theorem State.StreamAnnouncementInventory.startNewWork {queue : State}
    {announced : NodeRefs} (inventory : queue.StreamAnnouncementInventory announced)
    (work : NewWork)
    : (queue.startNewWork work).StreamAnnouncementInventory announced := by
  have groups := fold_preserves (fun current => current.StreamAnnouncementInventory announced)
    State.startGroup (fun _ ref prior => prior.startGroup ref)
    (work.newGroups.map Execution.DeliveryNode.ref)
    { queue with rootGroups := queue.rootGroups ++ work.newGroups.map Execution.DeliveryNode.ref }
    ⟨inventory.unique, inventory.registered, inventory.stored, inventory.unreleased⟩
  apply fold_preserves (fun current => current.StreamAnnouncementInventory announced)
    State.startStream _ _ _ groups
  intro current ref prior
  unfold State.startStream
  split <;> exact ⟨prior.unique, prior.registered, prior.stored, prior.unreleased⟩

-----------------------------------------------------------------------------------------
-- Every internal drain release consumes fresh refs before the next release
-----------------------------------------------------------------------------------------

/-- A bounded drain extends the announcement inventory by exactly its emitted stream refs.
Witness: successful flushes consume links before recursion; failed flushes emit no stream
notice and only remove links. Structural matching survives both paths and activation.
-/
theorem State.StreamAnnouncementInventory.drainReadyGroups_go {queue : State}
    {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    (fuel : Nat)
    : (State.drainReadyGroups.go fuel queue).1.StreamAnnouncementInventory
        (announced
          ++ (State.drainReadyGroups.go fuel queue).2.flatMap rawStreamNoticeRefs) := by
  induction fuel generalizing queue announced with
  | zero =>
      simpa only [State.drainReadyGroups.go, List.flatMap_nil, List.append_nil]
        using inventory
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · simpa only [List.flatMap_nil, List.append_nil] using inventory
      · rename_i node selected
        cases cached : node.failure with
        | none =>
            dsimp only
            have next := (inventory.finishGroupSuccess matching generated node).startNewWork
              (queue.finishGroupSuccess node).2.2
            have result := ih next ((matching.finishGroupSuccess node).startNewWork _)
            simpa only [List.flatMap_append, ← State.finishGroupSuccess_streamNotices,
              List.append_assoc] using result
        | some errors =>
            have result := ih (inventory.removeGroup node.group.node.ref)
              (matching.removeGroup node.group.node.ref)
            simpa only [State.finishGroupFailure, List.flatMap_append,
              List.flatMap_singleton, rawStreamNoticeRefs, List.nil_append] using result

/-- Actual ready draining emits fresh stream notices, even across multiple inner releases.
Witness: specialize the bounded inventory induction to the implementation's live-node fuel.
-/
theorem State.StreamAnnouncementInventory.drainReadyGroups
    {queue : State} {work : Execution.Work} {announced : NodeRefs}
    (inventory : queue.StreamAnnouncementInventory announced)
    (matching : queue.ChildStreamsMatchWork work) (generated : ExecutedWork work)
    : queue.drainReadyGroups.1.StreamAnnouncementInventory
        (announced ++ queue.drainReadyGroups.2.flatMap rawStreamNoticeRefs) :=
  inventory.drainReadyGroups_go matching generated _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
