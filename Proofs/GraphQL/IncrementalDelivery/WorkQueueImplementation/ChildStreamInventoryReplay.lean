import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamProvenance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation

/-! Distinct registered child-stream links survive every executable replay step. -/

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
-- Cleanup and group release retain certified links
-----------------------------------------------------------------------------------------

/-- Group cache replacement changes neither task links nor stream descriptors.
Witness: both relevant state projections are definitionally unchanged.
-/
theorem State.ChildStreamInventory.putGroupNode {queue : State}
    (inventory : queue.ChildStreamInventory) (group : GroupNode)
    : (queue.putGroupNode group).ChildStreamInventory :=
  inventory

/-- Task deletion retains only existing, certified child lists.
Witness: task-map inclusion and an unchanged stream registry.
-/
theorem State.ChildStreamInventory.removeTask {queue : State}
    (inventory : queue.ChildStreamInventory) (occurrence : Occurrence)
    : (queue.removeTask occurrence).ChildStreamInventory :=
  fun node member => inventory node (State.removeTask_node member).1

/-- Failed-group cleanup retains only existing child lists.
Witness: the final task-node filter and unchanged stream registry.
-/
theorem State.ChildStreamInventory.removeGroup {queue : State}
    (inventory : queue.ChildStreamInventory) (ref : NodeRef)
    : (queue.removeGroup ref).ChildStreamInventory :=
  fun node member => inventory node (List.mem_filter.mp member).1

/-- Successful flushing removes task nodes without changing surviving links.
Witness: the flush selection's residual inclusion and permanent stream descriptors.
-/
theorem State.ChildStreamInventory.finishGroupSuccess {queue : State}
    (inventory : queue.ChildStreamInventory) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.ChildStreamInventory := by
  obtain ⟨_, _, _, _, retained, _⟩ := queue.finishGroupSuccess_publications group
  intro node member
  rw [State.finishGroupSuccess_streams]
  exact inventory node (retained member)

/-- Rejection retention preserves the task's registered child-stream links. -/
theorem State.ChildStreamInventory.taskFailure {queue : State}
    (inventory : queue.ChildStreamInventory) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ChildStreamInventory := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using inventory
  | some task =>
      have links := inventory task (List.mem_of_find?_eq_some found)
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves State.ChildStreamInventory
        (fun _ ref prior => prior.removeGroup ref) _ _ _
        (inventory.putTaskNode _ links.1 links.2)

/-- Recursive draining preserves the child-link inventory.
Witness: cleanup and activation preserve it at every bounded drain step.
-/
theorem State.ChildStreamInventory.drainReadyGroups {queue : State}
    (inventory : queue.ChildStreamInventory)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.ChildStreamInventory := by
  apply State.drainReadyGroups_preserves State.ChildStreamInventory
    (available := available) (valid := inventory)
  · intro current node prior _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _ available

-----------------------------------------------------------------------------------------
-- Settlements and batched replay preserve the same inventory
-----------------------------------------------------------------------------------------

/-- Task success attaches fresh stream refs before releasing settled contributors.
Witness: value replacement preserves links; integration, flushing, and draining preserve
their uniqueness and permanent registration.
-/
theorem State.ChildStreamInventory.taskSuccess {queue : State}
    (inventory : queue.ChildStreamInventory) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.ChildStreamInventory := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using inventory
  | some node =>
      have links := inventory node (State.taskNode?_some found).1
      have installed := inventory.putTaskNode { node with value := some result.value }
        links.1 links.2
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      have step (acc : State × List WorkQueueEvent × NewWork) (group : Execution.DeliveryNode)
          (prior : acc.1.ChildStreamInventory)
          : (successGroupStep acc group).1.ChildStreamInventory := by
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · exact (prior.putGroupNode _).finishGroupSuccess _
          · exact prior
      have processed := fold_preserves (fun acc => acc.1.ChildStreamInventory)
        successGroupStep step node.task.groups (_, [], {}) integrated
      rw [queue.taskSuccess_eq occurrence result node found available]
      exact (processed.startNewWork _ available).drainReadyGroups available

/-- Item integration and its trailing drain preserve distinct registered links.
Witness: parentless integration, pruning, and activation preserve the invariant per item.
-/
theorem State.ChildStreamInventory.streamItems {queue : State}
    (inventory : queue.ChildStreamInventory) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.ChildStreamInventory := by
  have folded := fold_preserves (fun acc => acc.1.ChildStreamInventory)
    (fun acc item => streamItemStep acc item available)
    (fun acc item prior =>
      ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available)
    items (queue, [], [], [], []) inventory
  rw [queue.streamItems_eq stream items available]
  split
  · exact inventory
  · exact folded.drainReadyGroups available

/-- Every graph-event handler preserves the child-link inventory, even on raw inputs.
Witness: settlement preservation; stream closure only changes root and completion fields.
-/
theorem State.ChildStreamInventory.handleGraphEvent {queue : State}
    (inventory : queue.ChildStreamInventory) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.ChildStreamInventory := by
  have cached := inventory.cacheTaskFailures available
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess occurrence result available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items => exact cached.streamItems stream items available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact cached
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact cached

  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · exact cached
      · split <;> exact cached

/-- Raw event replay preserves distinct registered child links.
Witness: induction over the exact handler fold, with no source assumptions.
-/
theorem State.ChildStreamInventory.rawEventReplay {queue : State}
    (inventory : queue.ChildStreamInventory) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.rawEventReplay events available).1.ChildStreamInventory := by
  induction events generalizing queue with
  | nil => exact inventory
  | cons event rest ih =>
      rw [State.rawEventReplay_cons _ _ _ available]
      exact ih (inventory.handleGraphEvent event available)

/-- A batched handler retains the inventory across its terminal-flag update.
Witness: raw replay preservation; an already terminated queue is unchanged.
-/
theorem State.ChildStreamInventory.handleGraphEvents {queue : State}
    (inventory : queue.ChildStreamInventory) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.ChildStreamInventory := by
  rw [State.handleGraphEvents_eq_rawEventReplay]
  split
  · exact inventory
  · dsimp only
    split <;> exact inventory.rawEventReplay events (GraphEvent.availableFailures events)

/-- Arbitrary normalized replay from initialization has a certified child-link inventory.
Witness: the empty initial task map and per-batch preservation; normalization changes no
queue fields. This derived invariant requires no host-source or scheduler premise.
-/
theorem createWorkQueue_runNormalized_childStreamInventory (work : Work)
    (batches : List (List GraphEvent))
    : ((State.initialize work).runNormalized batches).1.ChildStreamInventory := by
  apply fold_preserves (fun acc : NormalizedAcc => acc.1.ChildStreamInventory)
    normalizedStep _ _ _ (createWorkQueue_childStreamInventory work)
  intro acc batch prior
  rw [normalizedStep_queue]
  exact prior.handleGraphEvents batch

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
