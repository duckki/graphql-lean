import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceOutputBlocks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReadyDrain
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TerminationFrames

/-! Only the batch wrapper terminates the queue or emits its terminal marker. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (
  ExecutionGroupValue StreamItemValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Individual settlements and recursive release cannot terminate the queue
-----------------------------------------------------------------------------------------

/-- Successful group release leaves termination to the enclosing batch.
Witness: flushing removes task memberships and pruning only removes group shells.
-/
theorem State.finishGroupSuccess_terminated (queue : State) (group : GroupNode)
    : (queue.finishGroupSuccess group).1.terminated = queue.terminated := by
  have preserved : ∀ acc occurrence,
      (flushGroupTask acc occurrence).1.terminated = acc.1.terminated := by
    intro acc occurrence
    unfold flushGroupTask
    split <;> rfl
  have same := fold_projection (fun acc : State × List ExecutionGroupValue × NodeRefs =>
    acc.1.terminated) flushGroupTask preserved group.tasks (queue, [], [])
  unfold State.finishGroupSuccess
  rw [State.pruneEmptyGroups_terminated]
  exact same

/-- Task rejection replay preserves the termination flag through owner removal. -/
theorem State.taskFailure_terminated (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : (queue.taskFailure occurrence errors).1.terminated = queue.terminated := by
  cases found : queue.taskNode? occurrence with
  | none => simp only [State.taskFailure, found]
  | some node =>
      rw [queue.taskFailure_eq occurrence errors node found]
      exact failureGroupFold_preserves (fun current => current.terminated = queue.terminated)
        (fun _ _ same => same) _ _ _ rfl

/-- Recursive release preserves the flag, including cached-failure removal.
Witness: the drain induction composes flag-preserving closure and activation steps.
-/
theorem State.drainReadyGroups_terminated (queue : State)
    (available : List (Occurrence × Nat) := [])
    : (queue.drainReadyGroups available).1.terminated = queue.terminated := by
  apply State.drainReadyGroups_preserves (fun current => current.terminated = queue.terminated)
    (available := available)
  · intro current node same _ _ _
    rw [State.startNewWork_terminated _ _ available, State.finishGroupSuccess_terminated]
    exact same
  · rfl

/-- Task success cannot terminate mid-batch, even when it drains every active group.
Witness: the owner fold and final drain preserve the flag; ignored outcomes only remove
task bookkeeping.
-/
theorem State.taskSuccess_terminated (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : (queue.taskSuccess occurrence result available).1.terminated
      = queue.terminated := by
  have preserved : ∀ acc group,
      (successGroupStep acc group).1.terminated = acc.1.terminated := by
    intro acc group
    obtain ⟨current, events, released⟩ := acc
    dsimp only [successGroupStep]
    split
    · rfl
    · split
      · exact State.finishGroupSuccess_terminated _ _
      · rfl
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      dsimp only
      rw [State.drainReadyGroups_terminated _ available,
        State.startNewWork_terminated _ _ available,
        fold_projection (fun acc : State × List WorkQueueEvent × NewWork =>
          acc.1.terminated) successGroupStep preserved]
      exact State.maybeIntegrateWork_terminated _ _ (some occurrence)

/-- Stream item integration and child release retain the termination flag.
Witness: each item registers/prunes/activates work before the flag-preserving drain.
-/
theorem State.streamItems_terminated (queue : State) (stream : Execution.DeliveryNode)
    (items : List StreamItem) (available : List (Occurrence × Nat) := [])
    : (queue.streamItems stream items available).1.terminated = queue.terminated := by
  have preserved (acc : State × List Execution.DeliveryNode × List Execution.DeliveryNode
      × List StreamItemValue × List GroupFailureEvent) (item : StreamItem)
      : (streamItemStep acc item available).1.terminated = acc.1.terminated := by
    simp only [streamItemStep]
    rw [State.startNewWork_terminated _ _ available, State.pruneEmptyGroups_terminated,
      State.maybeIntegrateWork_terminated]
  rw [queue.streamItems_eq stream items available]
  split
  · rfl
  · dsimp only
    rw [State.drainReadyGroups_terminated _ available]
    exact fold_projection (fun acc : State × List Execution.DeliveryNode
      × List Execution.DeliveryNode × List StreamItemValue × List GroupFailureEvent =>
        acc.1.terminated) (fun acc item => streamItemStep acc item available) preserved _ _

/-- Every individual source handler preserves the termination flag without host premises.
Witness: the task/item proofs and direct stream-closure state updates.
-/
theorem State.handleGraphEvent_terminated (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.handleGraphEvent event available).1.terminated = queue.terminated := by
  have cached := queue.cacheTaskFailures_terminated available
  cases event with
  | taskSuccess occurrence result =>
      exact ((queue.cacheTaskFailures available).taskSuccess_terminated occurrence result
        available).trans cached
  | taskFailure occurrence errors =>
      exact ((queue.cacheTaskFailures available).taskFailure_terminated occurrence errors).trans
        cached
  | streamItems stream items =>
      exact ((queue.cacheTaskFailures available).streamItems_terminated stream items
        available).trans cached
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

/-- Eventwise replay cannot terminate between supplied batch boundaries.
Witness: induction through the actual handler sequence, preserving the incoming flag.
-/
theorem State.rawEventReplay_terminated (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : (queue.rawEventReplay events available).1.terminated = queue.terminated := by
  induction events generalizing queue with
  | nil => rfl
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available]
      exact (ih _).trans (queue.handleGraphEvent_terminated event available)

-----------------------------------------------------------------------------------------
-- Handlers and publisher normalization cannot invent a terminal marker
-----------------------------------------------------------------------------------------

/-- A group flush emits optional values and one group completion, never termination.
Witness: the exact selected-publication output equation.
-/
theorem State.finishGroupSuccess_noTermination (queue : State) (group : GroupNode)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.finishGroupSuccess group).2.1 := by
  obtain ⟨selected, _, _, events, _, _⟩ := queue.finishGroupSuccess_publications group
  rw [events]
  split <;> simp

/-- Failure settlement emits only group failures, so it cannot emit termination. -/
theorem State.taskFailure_noTermination (queue : State) (occurrence : Occurrence)
    (errors : Nat)
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.taskFailure occurrence errors).2 := by
  intro emitted
  obtain ⟨group, impossible⟩ := queue.taskFailure_event_failure occurrence errors _ emitted
  cases impossible

/-- Recursive release emits only group values and closures.
Witness: induction on its budget, combining each closure with the remaining drain.
-/
theorem State.drainReadyGroups_noTermination (queue : State)
    (available : List (Occurrence × Nat) := [])
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.drainReadyGroups available).2.1 := by
  have loop (fuel : Nat) (current : State)
      : Execution.WorkQueueEvent.workQueueTermination
          ∉ (State.drainReadyGroups.go available fuel current).2.1 := by
    induction fuel generalizing current with
    | zero => simp [State.drainReadyGroups.go]
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · simp
        · rename_i node selected
          simpa only [List.mem_append, not_or]
            using And.intro (current.finishGroupSuccess_noTermination node) (ih _)
  exact loop _ queue

/-- Successful task settlement cannot emit a terminal marker during owner release.
Witness: each flush and the final drain exclude termination; ignored tasks emit nothing.
-/
theorem State.taskSuccess_noTermination (queue : State) (occurrence : Occurrence)
    (result : TaskResult) (available : List (Occurrence × Nat) := [])
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.taskSuccess occurrence result available).2.1 := by
  have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
      (prior : Execution.WorkQueueEvent.workQueueTermination ∉ acc.2.1)
      : Execution.WorkQueueEvent.workQueueTermination
          ∉ (groups.foldl successGroupStep acc).2.1 := by
    induction groups generalizing acc with
    | nil => exact prior
    | cons group rest ih =>
        apply ih
        obtain ⟨current, events, released⟩ := acc
        dsimp only [successGroupStep]
        split
        · exact prior
        · split
          · simpa only [List.mem_append, not_or]
              using And.intro prior (State.finishGroupSuccess_noTermination _ _)
          · exact prior
  cases found : queue.taskNode? occurrence with
  | none => simp [State.taskSuccess, found]
  | some node =>
      rw [queue.taskSuccess_eq occurrence result node found available]
      simpa only [List.mem_append, not_or]
        using And.intro (loop _ (_, [], {}) (by simp))
          (State.drainReadyGroups_noTermination _ available)

/-- No source-handler output contains queue termination, regardless of event validity.
Witness: task proofs, a stream-value carrier followed by group draining, and stream
closures.
-/
theorem State.handleGraphEvent_noTermination (queue : State) (event : GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.handleGraphEvent event available).2.1 := by
  cases event with
  | taskSuccess occurrence result =>
      exact (queue.cacheTaskFailures available).taskSuccess_noTermination occurrence result
        available
  | taskFailure occurrence errors =>
      exact (queue.cacheTaskFailures available).taskFailure_noTermination occurrence errors
  | streamItems stream items =>
      simp only [State.handleGraphEvent, State.streamItems]
      split
      · simp
      · simp only [List.mem_cons, reduceCtorEq, false_or]
        exact State.drainReadyGroups_noTermination _ available
  | streamSuccess stream =>
      simp only [State.handleGraphEvent, State.streamSuccess]
      split <;> simp
  | streamFailure stream errors =>
      simp only [State.handleGraphEvent, State.streamFailure]
      split <;> simp

  | groupFailure failure =>
      simp only [State.handleGraphEvent, State.groupFailure]
      split
      · simp
      · split <;> simp

/-- Eventwise replay has no terminal marker until the batch wrapper runs.
Witness: concatenate the handler-level exclusions along the actual replay.
-/
theorem State.rawEventReplay_noTermination (queue : State) (events : List GraphEvent)
    (available : List (Occurrence × Nat) := [])
    : Execution.WorkQueueEvent.workQueueTermination
      ∉ (queue.rawEventReplay events available).2 := by
  induction events generalizing queue with
  | nil => simp [State.rawEventReplay]
  | cons event rest ih =>
      rw [State.rawEventReplay_cons queue event rest available]
      simpa only [State.dispatchGraphEvent, List.mem_append, not_or]
        using And.intro (queue.handleGraphEvent_noTermination event available) (ih _)

/-- Publisher normalization contains termination exactly when its input does.
Witness: constructor inspection; owner remapping changes only value events.
-/
theorem IncrementalPublisher.handleWorkQueueEvent_termination_mem
    (publisher : IncrementalPublisher) (event : WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination
        ∈ (publisher.handleWorkQueueEvent event).2
      ↔ event = .workQueueTermination := by
  cases event <;> simp [IncrementalPublisher.handleWorkQueueEvent]

/-- Whole-batch normalization preserves and reflects terminal-marker membership.
Witness: the eventwise normalization equation and the single-event equivalence.
-/
theorem IncrementalPublisher.normalizeBatch_termination_mem
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination ∈ (publisher.normalizeBatch events).2
      ↔ Execution.WorkQueueEvent.workQueueTermination ∈ events := by
  induction events generalizing publisher with
  | nil => simp [IncrementalPublisher.normalizeBatch]
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons]
      simp only [List.mem_append, IncrementalPublisher.handleWorkQueueEvent_termination_mem,
        ih, List.mem_cons, eq_comm]

/-- Splitting value payloads into atoms preserves and reflects termination.
Witness: value atoms cannot be terminal, while each control constructor is unchanged.
-/
theorem publicationAtoms_termination_mem (event : Execution.WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination ∈ publicationAtoms event
      ↔ event = .workQueueTermination := by
  cases event with
  | streamValues stream values groups streams =>
      have absent : Execution.WorkQueueEvent.workQueueTermination ∉
          streamPublicationAtoms stream groups streams values := by
        induction values using streamPublicationAtoms.induct with
        | case1 => simp [streamPublicationAtoms]
        | case2 => simp [streamPublicationAtoms]
        | case3 value next rest ih => simpa [streamPublicationAtoms] using ih
      simpa only [publicationAtoms, reduceCtorEq, iff_false] using absent
  | _ => simp [publicationAtoms]

/-- Atom expansion of a complete event list introduces no new terminal marker.
Witness: list membership in the flat map and the single-event equivalence.
-/
theorem publicationAtoms_list_termination_mem (events : List Execution.WorkQueueEvent)
    : Execution.WorkQueueEvent.workQueueTermination ∈ events.flatMap publicationAtoms
      ↔ Execution.WorkQueueEvent.workQueueTermination ∈ events := by
  simp only [List.mem_flatMap, publicationAtoms_termination_mem]
  simp

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
