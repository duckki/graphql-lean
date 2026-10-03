import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamInventory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamProvenance

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

/-- Recursive draining preserves the child-link inventory.
Witness: cleanup and activation preserve it at every bounded drain step.
-/
theorem State.ChildStreamInventory.drainReadyGroups {queue : State}
    (inventory : queue.ChildStreamInventory)
    : queue.drainReadyGroups.1.ChildStreamInventory := by
  apply State.drainReadyGroups_preserves State.ChildStreamInventory (valid := inventory)
  · intro current node prior _ _ _ _
    exact (prior.finishGroupSuccess node).startNewWork _
  · intro current node errors prior _ _ _
    exact prior.removeGroup _

-----------------------------------------------------------------------------------------
-- Settlements and batched replay preserve the same inventory
-----------------------------------------------------------------------------------------

/-- Task success attaches fresh stream refs before releasing settled contributors.
Witness: value replacement preserves links; integration, flushing, and draining preserve
their uniqueness and permanent registration.
-/
theorem State.ChildStreamInventory.taskSuccess {queue : State}
    (inventory : queue.ChildStreamInventory) (occurrence : Occurrence)
    (result : TaskResult)
    : (queue.taskSuccess occurrence result).1.ChildStreamInventory := by
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
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · exact inventory.removeTask occurrence
      · exact (processed.startNewWork _).drainReadyGroups

/-- Failure retains certified links on surviving tasks.
Witness: task deletion, group cleanup, and cache-only updates preserve the invariant.
-/
theorem State.ChildStreamInventory.taskFailure {queue : State}
    (inventory : queue.ChildStreamInventory) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.ChildStreamInventory := by
  unfold State.taskFailure
  split
  · exact inventory
  · split
    · exact inventory.removeTask occurrence
    apply fold_preserves (fun acc : State × List WorkQueueEvent => acc.1.ChildStreamInventory)
    · intro acc group prior
      obtain ⟨current, events⟩ := acc
      dsimp only
      split
      · exact prior
      · split
        · exact prior.removeGroup _
        · exact prior
    · exact inventory.removeTask occurrence

/-- Item integration and its trailing drain preserve distinct registered links.
Witness: parentless integration, pruning, and activation preserve the invariant per item.
-/
theorem State.ChildStreamInventory.streamItems {queue : State}
    (inventory : queue.ChildStreamInventory) (stream : Execution.DeliveryNode)
    (items : List StreamItem)
    : (queue.streamItems stream items).1.ChildStreamInventory := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have folded := fold_preserves (fun acc => acc.1.ChildStreamInventory) step
    (fun acc item prior => ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _)
    items (queue, [], [], []) inventory
  unfold State.streamItems
  split
  · exact inventory
  · exact folded.drainReadyGroups

/-- Every graph-event handler preserves the child-link inventory, even on raw inputs.
Witness: settlement preservation; stream closure only changes root and completion fields.
-/
theorem State.ChildStreamInventory.handleGraphEvent {queue : State}
    (inventory : queue.ChildStreamInventory) (event : GraphEvent)
    : (queue.handleGraphEvent event).1.ChildStreamInventory := by
  cases event with
  | taskSuccess occurrence result => exact inventory.taskSuccess occurrence result
  | taskFailure occurrence errors => exact inventory.taskFailure occurrence errors
  | streamItems stream items => exact inventory.streamItems stream items
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact inventory
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact inventory

/-- Raw event replay preserves distinct registered child links.
Witness: induction over the exact handler fold, with no source assumptions.
-/
theorem State.ChildStreamInventory.rawEventReplay {queue : State}
    (inventory : queue.ChildStreamInventory) (events : List GraphEvent)
    : (queue.rawEventReplay events).1.ChildStreamInventory := by
  induction events generalizing queue with
  | nil => exact inventory
  | cons event rest ih =>
      rw [State.rawEventReplay_cons]
      exact ih (inventory.handleGraphEvent event)

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
    split <;> exact inventory.rawEventReplay events

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
