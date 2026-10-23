import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverageCore
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingDebt

/-! Permanent task catalogue equations independent of ownership and source admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Recursive release preserves the permanent task registry.
Witness: each successful flush, activation, and cached-failure removal leaves it unchanged.
-/
theorem State.drainReadyGroups_tasks (queue : State)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.tasks = queue.tasks := by
  apply State.drainReadyGroups_preserves (fun current => current.tasks = queue.tasks)
    (available := available) (valid := rfl)
  intro current node prior _ _ _
  rw [State.startNewWork_tasks, State.finishGroupSuccess_tasks, prior]

/-- A contributor step changes pending/live bookkeeping but not registered tasks.
Witness: ref-preserving updates and the successful-cleanup registry equation. -/
theorem successGroupStep_tasks (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode)
    : (successGroupStep acc group).1.tasks = acc.1.tasks := by
  obtain ⟨current, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · rfl
  · split
    · exact State.finishGroupSuccess_tasks _ _
    · rfl

/-- An eligible successful task appends exactly the supplied child tasks.
Witness: task presence selects integration; release preserves the appended registry.
-/
theorem State.taskSuccess_tasks {queue : State} {occurrence result node}
    (found : queue.taskNode? occurrence = some node)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.tasks
      = queue.tasks ++ result.work.tasks := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      : (groups.foldl successGroupStep acc).1.tasks = acc.1.tasks := by
    induction groups generalizing acc with
    | nil => rfl
    | cons group rest ih =>
        rw [List.foldl_cons, ih, successGroupStep_tasks]
  rw [queue.taskSuccess_eq occurrence result node found available]
  rw [State.drainReadyGroups_tasks _ available, State.startNewWork_tasks, loop,
    State.maybeIntegrateWork_tasks_append]
  rfl

/-- Task failure retains permanent registrations even when removing live descendants.
Witness: every owner-handler branch leaves the task registry unchanged. -/
theorem State.taskFailure_tasks (queue : State) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.tasks = queue.tasks := by
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskFailure, found]
  | some task =>
      rw [queue.taskFailure_eq occurrence errors task found]
      exact failureGroupFold_preserves (fun next => next.tasks = queue.tasks)
        (fun _ _ prior => prior) errors task.task.groups _ rfl

/-- One stream-item integration appends exactly its immediate child tasks.
Witness: pruning and activation preserve the integration append equation. -/
theorem State.integrateStreamItem_tasks (queue : State) (item : StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).tasks
      = queue.tasks ++ item.work.tasks := by
  unfold State.integrateStreamItem
  rw [State.startNewWork_tasks, State.pruneEmptyGroups_tasks,
    State.maybeIntegrateWork_tasks_append]

/-- Initialization registers exactly the immediate input tasks.
Witness: empty-queue integration, followed by registry-preserving pruning and activation. -/
theorem createWorkQueue_tasks (work : Work)
    : (State.initialize work).tasks = work.tasks := by
  unfold State.initialize
  dsimp only [State.enqueueGroupFailures]
  rw [State.startNewWork_tasks, State.pruneEmptyGroups_tasks,
    State.maybeIntegrateWork_tasks_append]
  rfl

/-- An active stream appends every supplied item's immediate tasks in item order.
Witness: each integration appends its chunk; pruning, activation, and final draining
preserve the permanent registry. The equation does not assert output admission.
-/
theorem State.streamItems_tasks (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (active : queue.rootStreams.contains stream.ref = true)
    (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.tasks
      = queue.tasks ++ items.flatMap (fun item => item.work.tasks) := by
  let step (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      (item : StreamItem) :=
    let (current, groups, streams, values, failures) := acc
    let (integrated, newWork) := current.maybeIntegrateWork item.work
    let (pruned, nonempty) := integrated.pruneEmptyGroups newWork.newGroups
    let (started, queued) :=
      pruned.startNewWork { newWork with newGroups := nonempty } available
    (started, groups ++ nonempty, streams ++ newWork.newStreams,
      values ++ [item.value], failures ++ queued)
  have loop (more : List StreamItem) (acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent)
      : (more.foldl step acc).1.tasks
        = acc.1.tasks ++ more.flatMap (fun item => item.work.tasks) := by
    induction more generalizing acc with
    | nil => simp
    | cons item rest ih =>
        rw [List.foldl_cons, ih]
        have current : (step acc item).1.tasks = acc.1.tasks ++ item.work.tasks :=
          State.integrateStreamItem_tasks acc.1 item available
        rw [current]
        simp only [List.flatMap_cons, List.append_assoc]
  simp only [State.streamItems, active, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [State.drainReadyGroups_tasks _ available]
  exact loop items (queue, [], [], [], [])

/-- Every source handler retains all earlier registered task descriptors.
Witness: success and stream-item handlers append exact chunks; ignored settlements,
failure cleanup, and stream controls leave the registry unchanged.
-/
theorem State.handleGraphEvent_tasks_subset (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : queue.tasks.Subset (queue.handleGraphEvent event available).1.tasks := by
  let current := queue.cacheTaskFailures available
  have same : current.tasks = queue.tasks := queue.cacheTaskFailures_tasks available
  rw [← same]
  cases event with
  | taskSuccess occurrence result =>
      change current.tasks.Subset (current.taskSuccess occurrence result available).1.tasks
      cases found : current.taskNode? occurrence with
      | none =>
          simp only [State.taskSuccess, found]
          exact fun _ member => member
      | some node =>
          rw [State.taskSuccess_tasks found available]
          exact List.subset_append_left _ _
  | groupFailure failure =>
      change current.tasks.Subset (current.groupFailure failure).1.tasks
      unfold State.groupFailure
      split
      · exact fun _ member => member
      · split <;> exact fun _ member => member
  | taskFailure occurrence errors =>
      change current.tasks.Subset (current.taskFailure occurrence errors).1.tasks
      rw [State.taskFailure_tasks]
      exact List.Subset.refl _
  | streamItems stream items =>
      change current.tasks.Subset (current.streamItems stream items available).1.tasks
      cases active : current.rootStreams.contains stream.ref with
      | false =>
          simp only [State.streamItems, active, Bool.not_false, ↓reduceIte]
          exact fun _ member => member
      | true =>
          rw [current.streamItems_tasks stream items active available]
          exact List.subset_append_left _ _
  | streamSuccess stream =>
      change current.tasks.Subset (current.streamSuccess stream).1.tasks
      unfold State.streamSuccess
      split <;> exact List.Subset.refl _
  | streamFailure stream errors =>
      change current.tasks.Subset (current.streamFailure stream errors).1.tasks
      unfold State.streamFailure
      split <;> exact List.Subset.refl _

/-- Arbitrary sequential replay retains every previously registered task.
Witness: list induction over the append-only registry of actual handlers; no source law
or generated-work invariant is needed for this structural persistence fact.
-/
theorem State.replayGraphEvents_tasks_subset (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : queue.tasks.Subset (queue.replayGraphEvents events available).tasks := by
  induction events generalizing queue with
  | nil => exact List.Subset.refl _
  | cons event rest ih =>
      have next : queue.tasks.Subset (queue.dispatchGraphEvent event available).1.tasks :=
        queue.handleGraphEvent_tasks_subset event available
      exact next.trans (ih (queue.dispatchGraphEvent event available).1)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
