import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRegistrationCoverage

/-! Permanent task registration survives handlers, draining, and actual source replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (StreamItemValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Stream batches integrate exactly their supplied item chunks
-----------------------------------------------------------------------------------------

/-- An active stream appends every supplied item's immediate tasks in item order.
Witness: each integration appends its chunk; pruning, activation, and final draining
preserve the permanent registry. The equation does not assert output admission.
-/
theorem State.streamItems_tasks (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (active : queue.rootStreams.contains stream.key = true)
    : (queue.streamItems stream items).1.tasks
      = queue.tasks ++ items.flatMap (fun item => item.work.tasks) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue) (item : StreamItem) :=
    let (current, groups, streams, values) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    (pruned.startNewWork { newWork with newGroups := nonempty },
      groups ++ nonempty, streams ++ newWork.newStreams, values ++ [item.value])
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue)
      : (more.foldl step acc).1.tasks
        = acc.1.tasks ++ more.flatMap (fun item => item.work.tasks) := by
    induction more generalizing acc with
    | nil => simp
    | cons item rest ih =>
        rw [List.foldl_cons, ih]
        have current : (step acc item).1.tasks = acc.1.tasks ++ item.work.tasks :=
          State.integrateStreamItem_tasks acc.1 item
        rw [current]
        simp only [List.flatMap_cons, List.append_assoc]
  simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [State.drainReadyGroups_tasks]
  exact loop items (queue, [], [], [])

/-- A started stream batch registers every structural child of each supplied item.
Witness: exact item matching and the full batch registry equation, including other items
in the same handler and its final recursive drain.
-/
theorem State.streamItems_child_registered {queue : State}
    {work stream items} (active : queue.rootStreams.contains stream.key = true)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (selected : item ∈ items) {address owners payload}
    (known : TaskAt work (.executionGroup address) owners (some item.occurrence) payload)
    : ∃ task ∈ (queue.streamItems stream items).1.tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨task, member, occurrence, groups⟩ := matching.streamItemChildren_complete selected known
  rw [queue.streamItems_tasks stream items active]
  exact ⟨task, List.mem_append_right _ (List.mem_flatMap.mpr ⟨item, selected, member⟩),
    occurrence, groups⟩

-----------------------------------------------------------------------------------------
-- Cleanup removes live nodes, never their permanent task descriptors
-----------------------------------------------------------------------------------------

/-- Every source handler retains all earlier registered task descriptors.
Witness: success and stream-item handlers append exact chunks; ignored settlements,
failure cleanup, and stream controls leave the registry unchanged.
-/
theorem State.handleGraphEvent_tasks_subset (queue : State) (event : GraphEvent)
    : queue.tasks.Subset (queue.handleGraphEvent event).1.tasks := by
  cases event with
  | taskSuccess occurrence result =>
      cases found : queue.taskNode? occurrence with
      | none =>
          simp only [State.handleGraphEvent, State.taskSuccess, found]; exact fun _ h => h
      | some node =>
          cases healthy : queue.taskHasHealthyOwner node.task with
          | false =>
              rw [State.handleGraphEvent, State.taskSuccess_of_noHealthyOwner found healthy]
              exact fun _ h => h
          | true =>
              rw [State.handleGraphEvent, State.taskSuccess_tasks found healthy]
              exact List.subset_append_left _ _
  | taskFailure occurrence errors =>
      rw [State.handleGraphEvent, State.taskFailure_tasks]
      exact fun _ h => h
  | streamItems stream items =>
      cases active : queue.rootStreams.contains stream.key with
      | false =>
          simp only [State.handleGraphEvent, State.streamItems, active, Bool.not_false,
            ↓reduceIte]
          exact fun _ h => h
      | true =>
          rw [State.handleGraphEvent, queue.streamItems_tasks stream items active]
          exact List.subset_append_left _ _
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> exact fun _ h => h
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> exact fun _ h => h

/-- Arbitrary sequential replay retains every previously registered task.
Witness: list induction over the append-only registry of actual handlers; no source law
or generated-work invariant is needed for this structural persistence fact.
-/
theorem State.replayGraphEvents_tasks_subset (queue : State) (events : List GraphEvent)
    : queue.tasks.Subset (queue.replayGraphEvents events).tasks := by
  induction events generalizing queue with
  | nil => exact List.Subset.refl _
  | cons event rest ih => exact (queue.handleGraphEvent_tasks_subset event).trans (ih _)

/-- Registration at an observed source prefix persists through its actual continuation.
Witness: decompose the replay fold at that prefix and reuse registry persistence.
-/
theorem State.replayGraphEvents_tasks_prefix (queue : State)
    {before events : List GraphEvent} (earlier : before.IsPrefix events)
    : (queue.replayGraphEvents before).tasks.Subset
        (queue.replayGraphEvents events).tasks := by
  obtain ⟨after, rfl⟩ := earlier
  simpa only [State.replayGraphEvents, List.foldl_append]
    using (queue.replayGraphEvents before).replayGraphEvents_tasks_subset after

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
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨task, member, occurrence, groups⟩ := TaskAt.executionGroup_initial_registered known
  exact ⟨task, (State.replayGraphEvents_tasks_subset _ events) member, occurrence, groups⟩

/-- Every child of an integrated object producer remains registered in later replay.
Witness: use the real pre-handler lookup and healthy-owner guard, then retain its exact
source-matched chunk through the rest of the source prefix. Ignored successes are excluded.
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
    (eligible
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents
          before).taskHasHealthyOwner
          node.task
        = true)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨task, member, occurrence, groups⟩ :=
    State.taskSuccess_child_registered found eligible matching known
  have introduced : task ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
      (before ++ [.taskSuccess producer result])).tasks := by
    rwa [State.replayGraphEvents_append]
  exact ⟨
    task,
    State.replayGraphEvents_tasks_prefix _ earlier introduced,
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
          stream.key
        = true)
    : ∃ task ∈
        ((State.initialize (Work.fromExecution work)).replayGraphEvents events).tasks,
        task.occurrence = .executionGroup address
        ∧ task.groups.map Execution.DeliveryNode.key = owners := by
  obtain ⟨task, member, occurrence, groups⟩ :=
    State.streamItems_child_registered active matching selected known
  have introduced : task ∈ ((State.initialize (Work.fromExecution work)).replayGraphEvents
      (before ++ [.streamItems stream items])).tasks := by
    rwa [State.replayGraphEvents_append]
  exact ⟨
    task,
    State.replayGraphEvents_tasks_prefix _ earlier introduced,
    occurrence,
    groups
  ⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
