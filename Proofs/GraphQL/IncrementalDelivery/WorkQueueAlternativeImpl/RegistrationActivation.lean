import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationProjection

/-! Root-source ownership installation commutes with the reference's task starts. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

-----------------------------------------------------------------------------------------
-- Source activation and computation activation touch independent fields
-----------------------------------------------------------------------------------------

/-- Installing a root source does not affect task lookup or the task-start decision.
Witness: source activation updates only rootStreams; task activation only taskNodes.
-/
theorem startTask_startStream (queue : ReferenceWorkQueue.State)
    (occurrence : WorkQueueSemantics.Occurrence) (key : Nat)
    : (queue.startStream key).startTask occurrence
      = (queue.startTask occurrence).startStream key := by
  have nodes : (queue.startStream key).taskNode? occurrence = queue.taskNode? occurrence := by
    unfold ReferenceWorkQueue.State.startStream
    split <;> rfl
  have tasks : (queue.startStream key).task? occurrence = queue.task? occurrence := by
    unfold ReferenceWorkQueue.State.startStream
    split <;> rfl
  unfold ReferenceWorkQueue.State.startTask
  rw [nodes, tasks]
  split
  · rfl
  · split
    · rfl
    · unfold ReferenceWorkQueue.State.startStream
      dsimp only [ReferenceWorkQueue.State.stream?]
      by_cases gate : ((queue.streams.find? (fun stream => stream.node.ref == key)).isNone
        || queue.rootStreams.contains key) = true
      · simp only [gate, ↓reduceIte]
      · simp only [gate, Bool.false_eq_true, ↓reduceIte]

private theorem startTasks_startStream (queue : ReferenceWorkQueue.State)
    (occurrences : List WorkQueueSemantics.Occurrence) (key : Nat)
    : occurrences.foldl ReferenceWorkQueue.State.startTask (queue.startStream key)
      = (occurrences.foldl ReferenceWorkQueue.State.startTask queue).startStream key := by
  induction occurrences generalizing queue with
  | nil => rfl
  | cons occurrence rest ih =>
      rw [List.foldl_cons, List.foldl_cons, startTask_startStream, ih]

/-- Root-source installation commutes with activation of all tasks of a released group.
Witness: group lookup/failure gating is unchanged, then commute each task start.
-/
theorem startGroup_startStream (queue : ReferenceWorkQueue.State) (group key : Nat)
    : (queue.startStream key).startGroup group
      = (queue.startGroup group).startStream key := by
  have lookup : (queue.startStream key).groupNode? group = queue.groupNode? group := by
    unfold ReferenceWorkQueue.State.startStream
    split <;> rfl
  unfold ReferenceWorkQueue.State.startGroup
  rw [lookup]
  cases found : queue.groupNode? group with
  | none => rfl
  | some node =>
      simp only
      split
      · rfl
      · exact startTasks_startStream queue node.tasks key

private theorem startGroups_startStream (queue : ReferenceWorkQueue.State)
    (groups : List Nat) (key : Nat)
    : groups.foldl ReferenceWorkQueue.State.startGroup (queue.startStream key)
      = (groups.foldl ReferenceWorkQueue.State.startGroup queue).startStream key := by
  induction groups generalizing queue with
  | nil => rfl
  | cons group rest ih =>
      rw [List.foldl_cons, List.foldl_cons, startGroup_startStream, ih]

/-- Source-first and group-first release activation have exactly the same final kernel.
Witness: commute the source fold through the group fold, preserving both list orders.
-/
theorem startGroups_startStreams (queue : ReferenceWorkQueue.State)
    (groups : List Nat) (streams : List Execution.DeliveryNode)
    : groups.foldl ReferenceWorkQueue.State.startGroup
        (streams.foldl (fun current stream => current.startStream stream.ref) queue)
      = streams.foldl (fun current stream => current.startStream stream.ref)
          (groups.foldl ReferenceWorkQueue.State.startGroup queue) := by
  induction streams generalizing queue with
  | nil => rfl
  | cons stream rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih, startGroups_startStream]

/-- Without an active-task projection, new activation projects to shared release activation.
Witness: disposal affects only host observations; source-first/group-first activation
commutes. Neither rejection count nor disposal targets are assumed empty.
-/
theorem State.startNewWork_queue_of_no_active (state : State)
    (newWork : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget) (running : state.stopped = false)
    (inactive : integrated.activeTasks = [])
    : (state.startNewWork newWork integrated targets).1.queue
      = state.queue.startNewWork newWork := by
  simp only [State.startNewWork, running, Bool.false_eq_true, ↓reduceIte, inactive,
    List.foldl_nil, ReferenceWorkQueue.State.startNewWork]
  simpa only [List.foldl_map] using startGroups_startStreams
    { state.queue with rootGroups := state.queue.rootGroups
        ++ newWork.newGroups.map Execution.DeliveryNode.ref }
    (newWork.newGroups.map Execution.DeliveryNode.ref) newWork.newStreams

/-- Activation preserves the interruption guard. -/
theorem State.startNewWork_stopped (state : State) (newWork : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    : (state.startNewWork newWork integrated targets).1.stopped = state.stopped := by
  unfold State.startNewWork
  split <;> rfl

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
