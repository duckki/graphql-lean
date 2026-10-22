import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverageCore
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay

/-! Live group records remain registered independently of task-contributor coverage. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open WorkQueueSemantics (NodeRefs Occurrence)

/-- Installing arbitrary work registers every new live group before adding its tasks. -/
theorem State.LiveGroupsRegistered.maybeIntegrateWork {queue : State}
    (live : queue.LiveGroupsRegistered) (work : Work)
    (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.LiveGroupsRegistered := by
  have tasks (more : List Task) (current : State) (known : current.LiveGroupsRegistered)
      : (more.foldl State.addTask current).LiveGroupsRegistered := by
    induction more generalizing current with
    | nil => exact known
    | cons task rest ih => exact ih _ (known.addTask task)
  have installed := tasks work.tasks _ (queue.addGroups_registration live work.groups).1
  change ((work.tasks.foldl State.addTask (queue.addGroups work.groups).1).addStreams
    work.streams producer).1.LiveGroupsRegistered
  unfold State.addStreams
  split
  · exact installed
  · dsimp only
    split <;> exact installed

/-- Pruning only removes live shells and preserves their permanent registration. -/
theorem State.LiveGroupsRegistered.pruneEmptyGroups {queue : State}
    (live : queue.LiveGroupsRegistered) (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.LiveGroupsRegistered := by
  have loop (fuel : Nat) (current : State) (remaining kept : List Execution.DeliveryNode)
      (known : current.LiveGroupsRegistered)
      : (State.pruneEmptyGroups.go fuel current remaining kept).1.LiveGroupsRegistered := by
    induction fuel generalizing current remaining kept with
    | zero => exact known
    | succ fuel ih =>
        cases remaining with
        | nil => exact known
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _ known
            · split
              · exact ih _ _ _ (fun node member => known node (List.mem_filter.mp member).1)
              · exact ih _ _ _ known
  exact loop _ _ _ _ live

/-- Exposing available rejections changes no live group or registry entry. -/
theorem State.LiveGroupsRegistered.cacheTaskFailures {queue : State}
    (live : queue.LiveGroupsRegistered) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).LiveGroupsRegistered := by
  intro node member
  rw [State.cacheTaskFailures_registeredGroups]
  rw [State.cacheTaskFailures_groupNodes] at member
  exact live node member

/-- Startup can remove failed shells but cannot install an unregistered group record. -/
theorem State.LiveGroupsRegistered.startNewWork {queue : State}
    (live : queue.LiveGroupsRegistered) (work : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork work available).1.LiveGroupsRegistered := by
  intro node member
  rw [State.startNewWork_registeredGroups]
  exact live node ((queue.startNewWork_groupNodes_sublist work available).subset member)

/-- Removing a computation preserves the registration refs of its surviving owners. -/
theorem State.LiveGroupsRegistered.removeTask {queue : State}
    (live : queue.LiveGroupsRegistered) (occurrence : Occurrence)
    : (queue.removeTask occurrence).LiveGroupsRegistered := by
  intro node member
  obtain ⟨prior, listed, rfl⟩ := List.mem_map.mp member
  exact live prior listed

/-- Success removes computations and group shells; remaining records stay registered. -/
theorem State.LiveGroupsRegistered.finishGroupSuccess {queue : State}
    (live : queue.LiveGroupsRegistered) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.LiveGroupsRegistered := by
  let step (acc : State × List ExecutionGroupValue × NodeRefs) (occurrence : Occurrence) :=
    match acc.1.taskNode? occurrence with
    | none => acc
    | some node =>
        (acc.1.removeTask occurrence,
          match node.value with
          | none => acc.2.1
          | some value => acc.2.1 ++ [value],
          acc.2.2 ++ node.childStreams)
  have loop (more : List Occurrence) (acc : State × List ExecutionGroupValue × NodeRefs)
      (known : acc.1.LiveGroupsRegistered)
      : (more.foldl step acc).1.LiveGroupsRegistered := by
    induction more generalizing acc with
    | nil => exact known
    | cons occurrence rest ih =>
        apply ih
        unfold step
        split
        · exact known
        · exact known.removeTask occurrence
  let flushed := group.tasks.foldl step (queue, [], [])
  have retained := loop group.tasks (queue, [], []) live
  exact (show ({
                flushed.1 with
                  groupNodes :=
                    flushed.1.groupNodes.filter
                      (fun node => node.group.node.ref != group.group.node.ref)
                  rootGroups := flushed.1.rootGroups.filter (· != group.group.node.ref)
              }).LiveGroupsRegistered from fun node member =>
          retained node (List.mem_filter.mp member).1).pruneEmptyGroups
    _

/-- Failed subtree removal only filters registered group records. -/
theorem State.LiveGroupsRegistered.removeGroup {queue : State}
    (live : queue.LiveGroupsRegistered) (ref : NodeRef)
    : (queue.removeGroup ref).LiveGroupsRegistered :=
  fun node member => live node (List.mem_filter.mp member).1

/-- Rejecting a computation can only update or remove already registered groups. -/
theorem State.LiveGroupsRegistered.taskFailure {queue : State}
    (live : queue.LiveGroupsRegistered) (occurrence : Occurrence) (errors : Nat)
    : (queue.taskFailure occurrence errors).1.LiveGroupsRegistered := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using live
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves State.LiveGroupsRegistered
        (fun _ ref prior => prior.removeGroup ref) _ _ _ live

/-- Successful draining preserves registration through each flush and activation. -/
theorem State.LiveGroupsRegistered.drainReadyGroups {queue : State}
    (live : queue.LiveGroupsRegistered) (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.LiveGroupsRegistered :=
  State.drainReadyGroups_preserves State.LiveGroupsRegistered
    (fun _ node prior _ _ _ => (prior.finishGroupSuccess node).startNewWork _ available)
    live

/-- Successful task settlement integrates arbitrary child work before registered-owner release. -/
theorem State.LiveGroupsRegistered.taskSuccess {queue : State}
    (live : queue.LiveGroupsRegistered) (occurrence : Occurrence) (result : TaskResult)
    (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.LiveGroupsRegistered := by
  have loop (groups : List Execution.DeliveryNode)
      (acc : State × List WorkQueueEvent × NewWork) (known : acc.1.LiveGroupsRegistered)
      : (groups.foldl successGroupStep acc).1.LiveGroupsRegistered := by
    induction groups generalizing acc with
    | nil => exact known
    | cons group rest ih =>
        simp only [List.foldl_cons, successGroupStep]
        split
        · exact ih _ known
        · rename_i node found
          have changed := known.putGroupNode {node with pending := node.pending - 1}
            (known node (List.mem_of_find?_eq_some found))
          split
          · exact ih _ (changed.finishGroupSuccess _)
          · exact ih _ changed
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using live
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      have stored : (queue.putTaskNode {node with value := some result.value}).LiveGroupsRegistered := live
      have integrated := stored.maybeIntegrateWork result.work (some occurrence)
      exact ((loop node.task.groups (_, [], {}) integrated).startNewWork _ available)
        |>.drainReadyGroups available

/-- Each stream-item integration registers new records before activation. -/
theorem State.LiveGroupsRegistered.integrateStreamItem {queue : State}
    (live : queue.LiveGroupsRegistered) (item : StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.integrateStreamItem item available).LiveGroupsRegistered :=
  ((live.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available

/-- Item batches and their final ready drain preserve registration. -/
theorem State.LiveGroupsRegistered.streamItems {queue : State}
    (live : queue.LiveGroupsRegistered) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.LiveGroupsRegistered := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact live
  · exact (State.preparedStreamItems_preserves State.LiveGroupsRegistered live items available
      (fun _ item _ prior => prior.integrateStreamItem item available)).drainReadyGroups available

/-- Every handler keeps live group records registered, without a source-work premise. -/
theorem State.LiveGroupsRegistered.handleGraphEvent {queue : State}
    (live : queue.LiveGroupsRegistered) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.LiveGroupsRegistered := by
  have cached := live.cacheTaskFailures available
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
  | groupFailure notice =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · exact cached
      · split <;> exact cached

/-- Enqueue effects preserve the same unconditional live-registration invariant. -/
theorem State.LiveGroupsRegistered.dispatchGraphEvent {queue : State}
    (live : queue.LiveGroupsRegistered) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.dispatchGraphEvent event available).1.LiveGroupsRegistered :=
  live.handleGraphEvent event available

/-- Actual FIFO replay preserves registration independently of host event validity. -/
theorem State.LiveGroupsRegistered.replayGraphEvents {queue : State}
    (live : queue.LiveGroupsRegistered) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.replayGraphEvents events available).LiveGroupsRegistered := by
  induction events generalizing queue with
  | nil => exact live
  | cons event rest ih => exact ih (live.dispatchGraphEvent event available)

/-- Batch termination and FIFO execution keep every live group registered. -/
theorem State.LiveGroupsRegistered.handleGraphEvents {queue : State}
    (live : queue.LiveGroupsRegistered) (events : List GraphEvent)
    : (queue.handleGraphEvents events).1.LiveGroupsRegistered := by
  cases running : queue.terminated with
  | true => simpa only [State.handleGraphEvents, running, ↓reduceIte] using live
  | false =>
      obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
      rw [same]
      exact live.replayGraphEvents events (GraphEvent.availableFailures events)

/-- Every initial live record is registered, for arbitrary finite internal work. -/
theorem createWorkQueue_liveGroupsRegistered (work : Work)
    : (State.initialize work).LiveGroupsRegistered := by
  have empty : ({} : State).LiveGroupsRegistered := by intro node member; cases member
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
