import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RetiredTaskNodes

/-! Retirement persists through source-valid continuations, even when the source still
contains a previously enqueued notification. No source membership or output law is assumed.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics (Occurrence NodeRefs)

/-- Replacement of an existing group's task list preserves global retirement. -/
theorem State.RetiredTask.putExistingGroupNode {queue occurrence node}
    (retired : State.RetiredTask queue occurrence) (member : node ∈ queue.groupNodes)
    (updated : GroupNode) (same : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).RetiredTask occurrence :=
  ⟨
    retired.missing,
    retired.unlinked.putGroupNode updated (same ▸ retired.unlinked node member)
  ⟩

/-- Publication flushing only removes task nodes and memberships. -/
theorem State.RetiredTask.flushGroupTasks {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (tasks : List Occurrence)
    (values : List Execution.ExecutionGroupValue) (streams : NodeRefs)
    : (tasks.foldl flushGroupTask (queue, values, streams)).1.RetiredTask occurrence := by
  induction tasks generalizing queue values streams with
  | nil => exact retired
  | cons task rest ih =>
      simp only [List.foldl_cons, flushGroupTask]
      split
      · exact ih retired _ _
      · exact ih (retired.removeTask task) _ _

/-- Successful group completion and empty-shell pruning preserve task retirement. -/
theorem State.RetiredTask.finishGroupSuccess {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.RetiredTask occurrence := by
  have flushed := retired.flushGroupTasks group.tasks [] []
  let values := group.tasks.foldl flushGroupTask (queue, [], [])
  let current : State := { values.1 with
    groupNodes := values.1.groupNodes.filter
      (fun node => node.group.node.ref != group.group.node.ref)
    rootGroups := values.1.rootGroups.filter (· != group.group.node.ref) }
  have filtered : current.RetiredTask occurrence :=
    ⟨flushed.missing, fun node member => flushed.unlinked node (List.mem_filter.mp member).1⟩
  exact filtered.pruneEmptyGroups _

/-- Released groups cannot start a computation whose memberships are all absent. -/
theorem State.RetiredTask.startNewWork {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (released : NewWork)
    (available : List (Occurrence × Nat))
    : (queue.startNewWork released available).1.RetiredTask occurrence := by
  let step (acc : State × List GroupFailureEvent) (ref : Nat) :=
    let next := acc.1.startGroup ref available
    (next.1, acc.2 ++ next.2)
  have groups (refs : NodeRefs) (acc : State × List GroupFailureEvent)
      (prior : acc.1.RetiredTask occurrence)
      : (refs.foldl step acc).1.RetiredTask occurrence := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih => exact ih _ (prior.startGroup ref available)
  have streams (refs : NodeRefs) (current : State)
      (prior : current.RetiredTask occurrence)
      : (refs.foldl State.startStream current).RetiredTask occurrence := by
    induction refs generalizing current with
    | nil => exact prior
    | cons ref rest ih =>
        apply ih
        unfold State.startStream
        split
        · exact prior
        · exact ⟨prior.missing, prior.unlinked⟩
  exact streams _ _ (groups _ _ ⟨retired.missing, retired.unlinked⟩)

/-- Ready draining preserves retirement through successful release and failed child startup. -/
theorem State.RetiredTask.drainReadyGroups_go {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (fuel : Nat)
    (available : List (Occurrence × Nat))
    : (State.drainReadyGroups.go available fuel queue).1.RetiredTask occurrence := by
  induction fuel generalizing queue with
  | zero => exact retired
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · exact retired
      · rename_i node selected
        exact ih ((retired.finishGroupSuccess node).startNewWork _ available)

/-- The owner-success pass retains global retirement before newly released work starts. -/
theorem State.RetiredTask.successGroupFold {queue occurrence}
    (retired : State.RetiredTask queue occurrence)
    (groups : List Execution.DeliveryNode) (events : List Execution.WorkQueueEvent)
    (released : NewWork)
    : (groups.foldl successGroupStep (queue, events, released)).1.RetiredTask
        occurrence := by
  induction groups generalizing queue events released with
  | nil => exact retired
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih retired _ _
      · rename_i node found
        have updated := retired.putExistingGroupNode (List.mem_of_find?_eq_some found)
          {node with pending := node.pending - 1} rfl
        split
        · exact ih (updated.finishGroupSuccess _) _ _
        · exact ih updated _ _

/-- A task success can install only its fresh child occurrences. -/
theorem State.RetiredTask.taskSuccess {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (source : Occurrence)
    (result : TaskResult)
    (fresh : ∀ task ∈ result.work.tasks, occurrence ≠ task.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.taskSuccess source result available).1.RetiredTask occurrence := by
  cases found : queue.taskNode? source with
  | none => simpa only [State.taskSuccess, found] using retired
  | some node =>
      rw [queue.taskSuccess_eq source result node found available]
      have prepared := (retired.putTaskNode {node with value := some result.value})
        |>.maybeIntegrateWork result.work fresh (some source)
      exact ((prepared.successGroupFold node.task.groups [] {}).startNewWork _ available)
        |>.drainReadyGroups_go _ available

/-- Consuming any rejection cannot recreate a retired task. -/
theorem State.RetiredTask.taskFailure {queue occurrence}
    (retired : State.RetiredTask queue occurrence) (source : Occurrence) (errors : Nat)
    : (queue.taskFailure source errors).1.RetiredTask occurrence := by
  cases found : queue.taskNode? source with
  | none => simpa only [State.taskFailure, found] using retired
  | some node =>
      rw [queue.taskFailure_eq source errors node found]
      apply failureGroupFold_preserves (fun current => current.RetiredTask occurrence)
        (fun _ ref prior => prior.removeGroup ref)
      exact retired.putTaskNode {node with rejection := some errors}

/-- Receipt preparation installs only fresh occurrences before cached startup. -/
theorem State.RetiredTask.streamItems {queue occurrence stream items}
    (retired : State.RetiredTask queue occurrence)
    (fresh : ∀ item ∈ items, ∀ task ∈ item.work.tasks, occurrence ≠ task.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.streamItems stream items available).1.RetiredTask occurrence := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact retired
  · apply State.RetiredTask.drainReadyGroups_go (available := available)
    apply State.preparedStreamItems_preserves (fun q => q.RetiredTask occurrence)
      retired items available
    intro current item member prior
    exact ((prior.maybeIntegrateWork item.work (fresh item member)).pruneEmptyGroups _)
      |>.startNewWork _ available

/-- A handler cannot resurrect a retired occurrence when its supplied child work is fresh. -/
theorem State.RetiredTask.handleGraphEvent {queue occurrence event}
    (retired : State.RetiredTask queue occurrence)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.handleGraphEvent event available).1.RetiredTask occurrence := by
  have cached := retired.cacheTaskFailures available
  cases event with
  | taskSuccess source result => exact cached.taskSuccess source result fresh available
  | taskFailure source errors => exact cached.taskFailure source errors
  | streamItems stream items =>
      exact cached.streamItems
        (fun item member task listed => fresh task (List.mem_flatMap.mpr ⟨item, member, listed⟩))
        available
  | streamSuccess stream =>
      change ((queue.cacheTaskFailures available).streamSuccess stream).1.RetiredTask occurrence
      unfold State.streamSuccess
      split
      · exact ⟨cached.missing, cached.unlinked⟩
      · exact cached
  | streamFailure stream errors =>
      change ((queue.cacheTaskFailures available).streamFailure stream errors).1.RetiredTask
        occurrence
      unfold State.streamFailure
      split
      · exact ⟨cached.missing, cached.unlinked⟩
      · exact cached

  | groupFailure notice =>
      change ((queue.cacheTaskFailures available).groupFailure notice).1.RetiredTask occurrence
      unfold State.groupFailure
      split
      · exact cached
      · split
        · exact ⟨cached.missing, cached.unlinked⟩
        · exact cached

/-- Realizing enqueue effects cannot resurrect a retired task. -/
theorem State.RetiredTask.dispatchGraphEvent {queue occurrence event}
    (retired : State.RetiredTask queue occurrence)
    (fresh : ∀ child ∈ event.childTasks, occurrence ≠ child.occurrence)
    (available : List (Occurrence × Nat))
    : (queue.dispatchGraphEvent event available).1.RetiredTask occurrence := by
  have next := retired.handleGraphEvent fresh available
  exact ⟨next.missing, next.unlinked⟩

/-- Source freshness and producer provenance exclude reusing a registered retired occurrence.
The continuation may include its old buffered notification and needs no membership premise.
-/
theorem State.RetiredTask.replayGraphEvents {queue work occurrence before}
    (retired : State.RetiredTask queue occurrence)
    (registered : occurrence ∈ queue.tasks.map Task.occurrence)
    (ready : TaskProducersSucceeded work queue.tasks before)
    (ordered : ProducerOrder work (queue.tasks.map Task.occurrence))
    (events : List GraphEvent) (valid : ValidGraphEvents work (before ++ events))
    (available : List (Occurrence × Nat))
    : (queue.replayGraphEvents events available).RetiredTask occurrence := by
  induction events generalizing queue before with
  | nil => exact retired
  | cons event rest ih =>
      have earlier : (before ++ [event]).IsPrefix (before ++ event :: rest) := ⟨rest, by simp⟩
      obtain ⟨priorValid, matching, fresh⟩ := validGraphEvents_last (valid.prefix earlier)
      have next := retired.dispatchGraphEvent (by
        intro child member same
        exact matching.childTask_not_registered ready fresh member (same ▸ registered)) available
      have source := State.dispatchGraphEvent_producerOrder ready ordered
        priorValid matching fresh available
      apply ih next _ source.1 source.2
        (by simpa only [List.append_assoc, List.singleton_append] using valid)
      obtain ⟨task, member, same⟩ := List.mem_map.mp registered
      exact List.mem_map.mpr
        ⟨task, queue.handleGraphEvent_tasks_subset event available member, same⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
