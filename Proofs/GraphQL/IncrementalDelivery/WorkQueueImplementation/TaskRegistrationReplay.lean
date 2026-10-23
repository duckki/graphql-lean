import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationCoverage

/-! Permanent task registration survives handlers, draining, and actual source replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream batches integrate exactly their supplied item chunks
-----------------------------------------------------------------------------------------

/-- A started stream batch registers every structural child of each supplied item.
Witness: exact item matching and the full batch registry equation, including other items
in the same handler and its final recursive drain.
-/
theorem State.streamItems_child_registered {queue : State}
    {work stream items} (active : queue.rootStreams.contains stream.ref = true)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (selected : item ∈ items) {address owners payload}
    (known : TaskAt work (.executionGroup address) owners (some item.occurrence) payload)
    (available : List (Occurrence × Nat) := [])
    : ∃ task ∈ (queue.streamItems stream items available).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨task, member, occurrence, groups⟩ := matching.streamItemChildren_complete selected known
  rw [queue.streamItems_tasks stream items active available]
  exact ⟨task, List.mem_append_right _ (List.mem_flatMap.mpr ⟨item, selected, member⟩),
    occurrence, groups⟩

-----------------------------------------------------------------------------------------
-- Cleanup removes live nodes, never their permanent task descriptors
-----------------------------------------------------------------------------------------

/-- Registration at an observed source prefix persists through its actual continuation.
Witness: decompose the replay fold at that prefix and reuse registry persistence.
-/
theorem State.replayGraphEvents_tasks_prefix (queue : State)
    {before events : List GraphEvent} (earlier : before.IsPrefix events)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents before available).tasks.Subset
        (queue.replayGraphEvents events available).tasks := by
  obtain ⟨after, rfl⟩ := earlier
  simpa only [State.replayGraphEvents, List.foldl_append]
    using (queue.replayGraphEvents before available).replayGraphEvents_tasks_subset after
      available

/-- Whole host batches retain every earlier permanent task registration. -/
theorem State.handleGraphEvents_tasks_subset (queue : State) (events : List GraphEvent)
    : queue.tasks.Subset (queue.handleGraphEvents events).1.tasks := by
  cases running : queue.terminated with
  | true =>
      simp only [State.handleGraphEvents, running, ↓reduceIte]
      exact List.Subset.refl _
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact queue.replayGraphEvents_tasks_subset events (GraphEvent.availableFailures events)

/-- Registry persistence composes through the actual batch state fold. -/
theorem State.replayBatches_tasks_subset (queue : State)
    (batches : List (List GraphEvent))
    : queue.tasks.Subset (queue.replayBatches batches).tasks := by
  induction batches generalizing queue with
  | nil => exact List.Subset.refl _
  | cons batch rest ih => exact (queue.handleGraphEvents_tasks_subset batch).trans (ih _)

/-- Normalization preserves the same append-only permanent registry as actual batch replay. -/
theorem State.runNormalized_tasks_subset (queue : State)
    (batches : List (List GraphEvent))
    : queue.tasks.Subset (queue.runNormalized batches).1.tasks := by
  rw [State.runNormalized_replayBatches]
  exact queue.replayBatches_tasks_subset batches

-----------------------------------------------------------------------------------------
-- Structural root and producer coverage at any later source prefix
-----------------------------------------------------------------------------------------

/-- Every producer-free structural task stays registered throughout arbitrary replay.
Witness: initial inverse lowering followed by permanent-registry persistence. Missing
live nodes therefore cannot be confused with root tasks that were never registered.
-/
theorem TaskAt.executionGroup_replay_registered {work address owners payload}
    (known : TaskAt work (.executionGroup address) owners none payload)
    (events : List GraphEvent)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨task, member, occurrence, groups⟩ := TaskAt.executionGroup_initial_registered known
  exact ⟨task, (State.replayGraphEvents_tasks_subset _ events) member, occurrence, groups⟩

/-- Every child of an integrated object producer remains registered in later replay.
Witness: use the real pre-handler task lookup, then retain its exact
source-matched chunk through the rest of the source prefix. Absent-task settlements are excluded.
-/
theorem TaskAt.executionGroup_registered_after_object
    {work address owners producer payload before result events node}
    (known : TaskAt work (.executionGroup address) owners (some producer) payload)
    (matching : (GraphEvent.taskSuccess producer result).MatchesWork work)
    (earlier : (before ++ [.taskSuccess producer result]).IsPrefix events)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          producer
        = some node)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨task, member, occurrence, groups⟩ :=
    State.taskSuccess_child_registered found matching known
  have introduced : task ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
      (before ++ [.taskSuccess producer result])).tasks := by
    rwa [State.replayGraphEvents_append]
  exact ⟨
    task,
    State.replayGraphEvents_tasks_prefix _ earlier [] introduced,
    occurrence,
    groups
  ⟩

/-- Every child of a supplied active-stream item remains registered in later replay.
Witness: the actual stream handler integrates the selected item's chunk even when other
items share its batch; registry persistence carries that descriptor beyond the handler.
-/
theorem TaskAt.executionGroup_registered_after_item
    {work address owners payload before stream items events} {item : StreamItem}
    (known : TaskAt work (.executionGroup address) owners (some item.occurrence) payload)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (selected : item ∈ items)
    (earlier : (before ++ [.streamItems stream items]).IsPrefix events)
    (active
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).rootStreams.contains
          stream.ref
        = true)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.ref = owners := by
  obtain ⟨task, member, occurrence, groups⟩ :=
    State.streamItems_child_registered active matching selected known
  have introduced : task ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
      (before ++ [.streamItems stream items])).tasks := by
    rwa [State.replayGraphEvents_append]
  exact ⟨
    task,
    State.replayGraphEvents_tasks_prefix _ earlier [] introduced,
    occurrence,
    groups
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
