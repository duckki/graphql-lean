import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CancellationRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.LiveRegistration
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPreparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InputReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DrainClosureBoundaries

/-! Permanent cancellation retirement through matching handlers and actual batch replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open WorkQueueSemantics

private structure CancellationFrame (queue : State) : Prop where
  retired : queue.CancellationsRetired
  live : queue.LiveGroupsRegistered

private theorem CancellationFrame.cacheTaskFailures {queue : State}
    (frame : CancellationFrame queue) (available : List (Occurrence × Nat))
    : CancellationFrame (queue.cacheTaskFailures available) := by
  exact ⟨frame.retired.cacheTaskFailures _, frame.live.cacheTaskFailures available⟩

private theorem CancellationFrame.removeGroup {queue : State}
    (frame : CancellationFrame queue) (ref : Nat)
    : CancellationFrame (queue.removeGroup ref) :=
  ⟨
    frame.retired.removeGroup frame.live _,
    fun node member => frame.live node (List.mem_filter.mp member).1
  ⟩

private theorem CancellationFrame.maybeIntegrateWork {queue : State}
    (frame : CancellationFrame queue) (incoming : Work)
    (producer : Option Occurrence := none)
    : CancellationFrame (queue.maybeIntegrateWork incoming producer).1 :=
  ⟨frame.retired.maybeIntegrateWork _ _, frame.live.maybeIntegrateWork incoming producer⟩

private theorem CancellationFrame.pruneEmptyGroups {queue : State}
    (frame : CancellationFrame queue) (groups : List Execution.DeliveryNode)
    : CancellationFrame (queue.pruneEmptyGroups groups).1 :=
  ⟨frame.retired.pruneEmptyGroups _, frame.live.pruneEmptyGroups groups⟩

private theorem CancellationFrame.startNewWork {queue : State}
    (frame : CancellationFrame queue) (released : NewWork)
    (available : List (Occurrence × Nat))
    : CancellationFrame (queue.startNewWork released available).1 :=
  ⟨
    frame.retired.startNewWork frame.live _ available,
    frame.live.startNewWork released available
  ⟩

private theorem CancellationFrame.finishGroupSuccess {queue : State}
    (frame : CancellationFrame queue) (group : GroupNode)
    : CancellationFrame (queue.finishGroupSuccess group).1 :=
  ⟨frame.retired.finishGroupSuccess _, frame.live.finishGroupSuccess group⟩

private theorem CancellationFrame.drainReadyGroups {queue : State}
    (frame : CancellationFrame queue) (available : List (Occurrence × Nat))
    : CancellationFrame (queue.drainReadyGroups available).1 :=
  State.drainReadyGroups_preserves CancellationFrame
    (fun _ group prior _ _ _ => (prior.finishGroupSuccess group).startNewWork _ available)
    frame

private theorem CancellationFrame.taskFailure {queue : State}
    (frame : CancellationFrame queue) (occurrence : Occurrence) (errors : Nat)
    : CancellationFrame (queue.taskFailure occurrence errors).1 := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskFailure, found] using frame
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves CancellationFrame
        (fun _ ref prior => prior.removeGroup ref) _ _ _
        ⟨frame.retired.putTaskNode _, frame.live⟩

private theorem CancellationFrame.successFold {queue : State}
    (frame : CancellationFrame queue) (groups : List Execution.DeliveryNode)
    (events : List WorkQueueEvent) (released : NewWork)
    : CancellationFrame (groups.foldl successGroupStep (queue, events, released)).1 := by
  induction groups generalizing queue events released with
  | nil => exact frame
  | cons group rest ih =>
      simp only [List.foldl_cons, successGroupStep]
      split
      · exact ih frame _ _
      · rename_i node found
        let updated := { node with pending := node.pending - 1 }
        have changed : CancellationFrame (queue.putGroupNode updated) :=
          ⟨frame.retired.putGroupNode _, frame.live.putGroupNode _
            (frame.live node (List.mem_of_find?_eq_some found))⟩
        split
        · exact ih (changed.finishGroupSuccess updated) _ _
        · exact ih changed _ _

private theorem CancellationFrame.taskSuccess {queue : State} {work occurrence result}
    (frame : CancellationFrame queue)
    (_matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (available : List (Occurrence × Nat))
    : CancellationFrame (queue.taskSuccess occurrence result available).1 := by
  cases found : queue.taskNode? occurrence with
  | none => simpa only [State.taskSuccess, found] using frame
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      have stored : CancellationFrame
          (queue.putTaskNode { node with value := some result.value }) :=
        ⟨frame.retired.putTaskNode _, frame.live⟩
      have prepared := stored.maybeIntegrateWork result.work
        (some occurrence)
      exact ((prepared.successFold node.task.groups [] {}).startNewWork _ available)
        |>.drainReadyGroups available

private theorem CancellationFrame.integrateStreamItem {queue : State} {work stream items}
    (frame : CancellationFrame queue)
    (_matching : (GraphEvent.streamItems stream items).MatchesWork work)
    {item : StreamItem} (_member : item ∈ items) (available : List (Occurrence × Nat))
    : CancellationFrame (queue.integrateStreamItem item available) := by
  have prepared := frame.maybeIntegrateWork item.work
  exact (prepared.pruneEmptyGroups _).startNewWork _ available

private theorem CancellationFrame.preparedStreamItems {queue : State} {work stream items}
    (frame : CancellationFrame queue)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : CancellationFrame (queue.preparedStreamItems items available) :=
  State.preparedStreamItems_preserves CancellationFrame frame items available
    (fun _ _ member prior => prior.integrateStreamItem matching member available)

/-- A registered retired ref cannot reappear during item integration and activation. -/
theorem State.RetiredGroup.preparedStreamItems {queue : State} {ref}
    (retired : queue.RetiredGroup ref) (items : List StreamItem)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).RetiredGroup ref := by
  apply State.preparedStreamItems_preserves (fun current => current.RetiredGroup ref)
    retired items available
  intro current item member prior
  exact ((prior.maybeIntegrateWork item.work).pruneEmptyGroups _).startNewWork _ available

/-- No successful drain carrier can use a ref already retired at drain entry. -/
theorem State.RetiredGroup.drainReadyGroups_go_noSuccess {queue : State} {ref}
    (retired : queue.RetiredGroup ref) (fuel : Nat) (available : List (Occurrence × Nat))
    {index : Nat} {group groups streams}
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (WorkQueueEvent.groupSuccess group groups streams))
    : group.ref ≠ ref := by
  intro sameRef
  obtain ⟨steps, node, before, bounded, found, active, zero, same, output, exactPrefix⟩ :=
    State.drainReadyGroups_go_success_boundary fuel queue available selected
  have beforeRetired := State.drainReadyGroups_go_preserves
    (fun current => current.RetiredGroup ref)
    (fun _ group prior _ _ _ => (prior.finishGroupSuccess group).startNewWork _ available)
    retired steps
  have nodeRef : node.group.node.ref = ref :=
    (congrArg Execution.DeliveryNode.ref same).trans sameRef
  rw [nodeRef] at found
  rw [beforeRetired.lookup_none] at found
  cases found

/-- A cancellation present at drain entry excludes every later successful carrier. -/
theorem State.CancellationsRetired.drainReadyGroups_go_carrier_uncancelled {queue : State}
    (prior : queue.CancellationsRetired) (fuel : Nat)
    (available : List (Occurrence × Nat)) {index : Nat} {group groups streams}
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (WorkQueueEvent.groupSuccess group groups streams))
    : group.ref ∉ queue.cancelledGroups := by
  intro cancelled
  exact (prior _ cancelled).drainReadyGroups_go_noSuccess fuel available selected rfl

/-- The complete ready drain retains retirement for every cancellation marker. -/
theorem State.CancellationsRetired.drainReadyGroups {queue : State}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered) (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.CancellationsRetired :=
  (show CancellationFrame queue from ⟨prior, live⟩).drainReadyGroups available |>.retired

/-- Each actual item-preparation boundary retains permanent cancellation retirement. -/
theorem State.CancellationsRetired.preparedStreamItems {queue : State} {work stream items}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat) := [])
    : (queue.preparedStreamItems items available).CancellationsRetired :=
  (show CancellationFrame queue from ⟨prior, live⟩).preparedStreamItems matching available
  |>.retired

private theorem CancellationFrame.streamItems {queue : State} {work stream items}
    (frame : CancellationFrame queue)
    (matching : (GraphEvent.streamItems stream items).MatchesWork work)
    (available : List (Occurrence × Nat))
    : CancellationFrame (queue.streamItems stream items available).1 := by
  rw [queue.streamItems_eq stream items available]
  split
  · exact frame
  · exact (frame.preparedStreamItems matching available).drainReadyGroups available

private theorem CancellationFrame.handleGraphEvent {queue : State} {work}
    (frame : CancellationFrame queue) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    : CancellationFrame (queue.handleGraphEvent event available).1 := by
  have cached := frame.cacheTaskFailures available
  simp only [State.handleGraphEvent]
  cases event with
  | taskSuccess occurrence result => exact cached.taskSuccess matching available
  | taskFailure occurrence errors => exact cached.taskFailure occurrence errors
  | streamItems stream items => exact cached.streamItems matching available
  | streamSuccess stream =>
      simp only [State.streamSuccess]
      split <;> exact ⟨cached.retired, cached.live⟩
  | streamFailure stream errors =>
      simp only [State.streamFailure]
      split <;> exact ⟨cached.retired, cached.live⟩

  | groupFailure notice =>
      simp only [State.groupFailure]
      split
      · exact cached
      · split <;> exact ⟨cached.retired, cached.live⟩

private theorem CancellationFrame.dispatchGraphEvent {queue : State} {work}
    (frame : CancellationFrame queue) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat))
    : CancellationFrame (queue.dispatchGraphEvent event available).1 := by
  have next := frame.handleGraphEvent event matching available
  exact ⟨next.retired, next.live⟩

/-- A matching cache-aware host transition keeps every cancellation ref retired. -/
theorem State.CancellationsRetired.handleGraphEvent {queue : State} {work}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered) (event : GraphEvent)
    (matching : event.MatchesWork work) (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.CancellationsRetired :=
  (show CancellationFrame queue from ⟨prior, live⟩).handleGraphEvent event matching
    available
  |>.retired

private theorem CancellationFrame.replayGraphEvents {queue : State} {work}
    (frame : CancellationFrame queue) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    (available : List (Occurrence × Nat))
    : CancellationFrame (queue.replayGraphEvents events available) := by
  induction events generalizing queue with
  | nil => exact frame
  | cons event rest ih =>
      exact ih (frame.dispatchGraphEvent event (matching event List.mem_cons_self) available)
        (fun next member => matching next (List.mem_cons_of_mem _ member))

private theorem CancellationFrame.handleGraphEvents {queue : State} {work}
    (frame : CancellationFrame queue) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : CancellationFrame (queue.handleGraphEvents events).1 := by
  by_cases ended : queue.terminated = true
  · simpa only [State.handleGraphEvents, ended, ite_true] using frame
  · have running : queue.terminated = false := Bool.eq_false_iff.mpr ended
    obtain ⟨terminal, same⟩ := queue.handleGraphEvents_stateCore events running
    have replayed := frame.replayGraphEvents events matching (GraphEvent.availableFailures events)
    rw [same]
    exact ⟨replayed.retired, replayed.live⟩

/-- Matched host batches preserve permanent retirement of every cancellation ref.
Witness: the existing structural frame follows the actual snapshot-aware handlers and
then the control-only batch termination update.
-/
theorem State.CancellationsRetired.handleGraphEvents {queue : State} {work}
    (prior : queue.CancellationsRetired) (live : queue.LiveGroupsRegistered)
    (_tasks : queue.TaskGroupsRegistered) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.handleGraphEvents events).1.CancellationsRetired :=
  (show CancellationFrame queue from ⟨prior, live⟩).handleGraphEvents events matching
  |>.retired

/-- Actual matched normalized batches keep all cancellation refs permanently retired.
Only structural registration and removal are used; accepted starts, failure licensing and
output admission are independent obligations.
-/
theorem createWorkQueue_runNormalized_cancellationsRetired {work : Execution.Work}
    (batches : List (List GraphEvent))
    (matching : ∀ event ∈ batches.flatten, event.MatchesWork work)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.CancellationsRetired := by
  have initial : CancellationFrame (State.initialize (Work.fromExecution work)) :=
    ⟨createWorkQueue_cancellationsRetired _, createWorkQueue_liveGroupsRegistered _⟩
  have loop (more : List (List GraphEvent)) (included : more.Subset batches)
      (current : State) (frame : CancellationFrame current)
      : CancellationFrame
          (more.foldl (fun next batch => (next.handleGraphEvents batch).1) current) := by
    induction more generalizing current with
    | nil => exact frame
    | cons batch rest ih =>
        exact ih (fun _ member => included (List.mem_cons_of_mem _ member)) _
          (frame.handleGraphEvents batch (fun _ member =>
            matching _ (List.mem_flatten.mpr ⟨batch, included List.mem_cons_self, member⟩)))
  rw [State.runNormalized_stateFold]
  exact (loop batches (List.Subset.refl _) _ initial).retired

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
