import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitializationSpecialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActivation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupFrames

/-! Registration, cache exposure and startup leave termination to actual batch handling. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration and activation preserve the termination flag
-----------------------------------------------------------------------------------------

/-- Group registration and parent linking leave the termination flag unchanged.
Witness: recursive installation modifies only group bookkeeping.
-/
theorem State.addGroups_terminated (queue : State) (groups : List Group)
    : (queue.addGroups groups).1.terminated = queue.terminated := by
  apply State.addGroups_projection State.terminated _ queue groups
  intro current group
  unfold State.addGroup
  split
  · rfl
  · split
    · rfl
    · split
      · split <;> rfl
      · rfl

/-- Task registration never terminates the queue.
Witness: contributor updates and optional start bookkeeping preserve the flag.
-/
theorem State.addTask_terminated (queue : State) (task : Task)
    : (queue.addTask task).terminated = queue.terminated := by
  let step (current : State) (group : Execution.DeliveryNode) :=
    match current.groupNode? group.ref with
    | none => current
    | some node =>
        if node.tasks.contains task.occurrence then current
        else current.putGroupNode { node with
          tasks := node.tasks ++ [task.occurrence], pending := node.pending + 1 }
  have preserved : ∀ current group, (step current group).terminated = current.terminated := by
    intro current group
    unfold step
    split
    · rfl
    · split <;> rfl
  let current := task.groups.foldl step { queue with tasks := queue.tasks ++ [task] }
  have same : current.terminated = queue.terminated :=
    fold_projection State.terminated step preserved _ _
  change (if _ then { current with taskNodes := current.taskNodes ++ [({ task } : TaskNode)] }
    else current).terminated = _
  split <;> exact same

/-- Child integration preserves the termination flag regardless of its work shape.
Witness: group/task registration and stream attachment modify separate state fields.
-/
theorem State.maybeIntegrateWork_terminated (queue : State) (work : Work)
    (parent : Option Occurrence := none)
    : (queue.maybeIntegrateWork work parent).1.terminated = queue.terminated := by
  have streams (current : State) (entries : List Stream) (producer : Option Occurrence)
      : (current.addStreams entries producer).1.terminated = current.terminated := by
    unfold State.addStreams
    split
    · rfl
    · dsimp only
      split <;> rfl
  unfold State.maybeIntegrateWork
  rw [streams, fold_projection State.terminated State.addTask State.addTask_terminated,
    State.addGroups_terminated]

/-- Pruning empty shells does not decide queue termination.
Witness: induction over the pruning budget; every branch retains the flag.
-/
theorem State.pruneEmptyGroups_terminated (queue : State) (groups)
    : (queue.pruneEmptyGroups groups).1.terminated = queue.terminated := by
  have loop (fuel : Nat) (current : State) (more kept)
      : (State.pruneEmptyGroups.go fuel current more kept).1.terminated
        = current.terminated := by
    induction fuel generalizing current more kept with
    | zero => rfl
    | succ fuel ih =>
        cases more with
        | nil => rfl
        | cons group rest =>
            simp only [State.pruneEmptyGroups.go]
            split
            · exact ih _ _ _
            · split <;> exact ih _ _ _
  exact loop _ _ _ _

/-- Cache exposure changes only computation outcomes, preserving termination. -/
theorem State.cacheTaskFailures_terminated (queue : State)
    (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).terminated = queue.terminated := by
  have same := congrArg State.terminated (queue.cacheTaskFailures_frame available)
  exact same

/-- Group startup preserves termination even when a cached rejection removes its group. -/
theorem State.startGroup_terminated (queue : State) (ref : Nat)
    (available : List (Occurrence × Nat) := [])
    : (queue.startGroup ref available).1.terminated = queue.terminated := by
  have tasks (more : List Occurrence) (current : State)
      : (more.foldl (fun current task => current.startTask task available)
          current).terminated = current.terminated := by
    induction more generalizing current with
    | nil => rfl
    | cons task rest ih =>
        rw [List.foldl_cons, ih]
        unfold State.startTask
        split
        · rfl
        · split <;> rfl
  unfold State.startGroup
  dsimp only
  split
  · exact queue.cacheTaskFailures_terminated available
  · split
    · exact (tasks _ _).trans (queue.cacheTaskFailures_terminated available)
    · exact queue.cacheTaskFailures_terminated available

/-- Activating released groups and streams retains the termination flag. -/
theorem State.startNewWork_terminated (queue : State) (released : NewWork)
    (available : List (Occurrence × Nat) := [])
    : (queue.startNewWork released available).1.terminated = queue.terminated := by
  have groups (more : NodeRefs) (acc : State × List GroupFailureEvent)
      : (more.foldl (fun (current, failures) ref =>
          let (next, queued) := current.startGroup ref available
          (next, failures ++ queued)) acc).1.terminated = acc.1.terminated := by
    induction more generalizing acc with
    | nil => rfl
    | cons ref rest ih =>
        exact (ih _).trans (acc.1.startGroup_terminated ref available)
  have streams (more : NodeRefs) (current : State)
      : (more.foldl State.startStream current).terminated = current.terminated := by
    induction more generalizing current with
    | nil => rfl
    | cons ref rest ih =>
        rw [List.foldl_cons, ih]
        unfold State.startStream
        split <;> rfl
  exact (streams _ _).trans (groups _ _)

/-- Initialization leaves termination to the first actual batch boundary, even when
all roots are already empty. Witness: integration, pruning, and activation preserve false.
-/
theorem createWorkQueue_terminated (work : Work)
    : (State.initialize work).terminated = false := by
  rw [State.initialize_empty_eq_activation]
  dsimp only
  rw [State.startNewWork_terminated, State.pruneEmptyGroups_terminated,
    State.maybeIntegrateWork_terminated]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
