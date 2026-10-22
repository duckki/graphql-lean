import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejections
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskNodeKeys

/-! Unique computation keys follow the concrete fused walker and cached group startup.
These field invariants do not require source admission or resource endpoint assumptions.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)

/-- Delayed task registration changes no computation key. -/
theorem State.addTask_taskNodeKeysUnique {state : State}
    (unique : state.queue.TaskNodeKeysUnique) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.TaskNodeKeysUnique := by
  simpa only [ReferenceWorkQueue.State.TaskNodeKeysUnique, State.addTask_taskNodes]
    using unique

/-- Scope integration registers descriptors and attaches streams without duplicating keys. -/
theorem State.maybeIntegrateWork_taskNodeKeysUnique {state : State}
    (unique : state.queue.TaskNodeKeysUnique) (work : ReferenceWorkQueue.Work)
    (producer : Option Occurrence := none)
    : (state.maybeIntegrateWork work producer).1.queue.TaskNodeKeysUnique := by
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (prior : acc.1.queue.TaskNodeKeysUnique)
      : (tasks.foldl registerTaskStep acc).1.queue.TaskNodeKeysUnique := by
    induction tasks generalizing acc with
    | nil => exact prior
    | cons task rest ih =>
        apply ih
        unfold registerTaskStep
        dsimp only
        split <;> exact State.addTask_taskNodeKeysUnique prior task
  exact (loop work.tasks _ (unique.addGroups work.groups)).addStreams work.streams
    producer

/-- Inline last-owner disposal only removes computation keys. -/
theorem State.removeGroup_taskNodeKeysUnique {state : State}
    (unique : state.queue.TaskNodeKeysUnique) (ref : Nat) (targets : List CleanupTarget)
    : (state.removeGroup ref targets).1.queue.TaskNodeKeysUnique := by
  have step (acc : State × List CleanupTarget) (occurrence : Occurrence)
      (prior : acc.1.queue.TaskNodeKeysUnique)
      : (fusedRemovalTaskStep acc occurrence).1.queue.TaskNodeKeysUnique := by
    unfold fusedRemovalTaskStep
    split
    · exact prior
    · split
      · exact prior.removeTask occurrence
      · exact prior
  have tasks (more : List Occurrence) (acc : State × List CleanupTarget)
      (prior : acc.1.queue.TaskNodeKeysUnique)
      : (more.foldl fusedRemovalTaskStep acc).1.queue.TaskNodeKeysUnique := by
    induction more generalizing acc with
    | nil => exact prior
    | cons occurrence rest ih => exact ih _ (step acc occurrence prior)
  have loop (fuel : Nat) (current : State) (pending removed) (targets)
      (prior : current.queue.TaskNodeKeysUnique)
      : (State.removeGroup.walk fuel current pending removed targets).1.queue.TaskNodeKeysUnique
        := by
    induction fuel generalizing current pending removed targets with
    | zero => simpa only [State.removeGroup.walk] using prior
    | succ fuel ih =>
        induction pending generalizing current removed targets with
        | nil => simpa only [State.removeGroup.walk] using prior
        | cons ref rest tailIH =>
            cases found : current.queue.groupNode? ref with
            | none =>
                simpa only [State.removeGroup.walk, found] using tailIH _ _ _ prior
            | some group =>
                rw [State.removeGroup.walk, found]
                let erased := eraseRemovalGroup current ref
                let folded := group.tasks.foldl fusedRemovalTaskStep (erased, targets)
                exact ih folded.1 (group.childGroups ++ rest) (ref :: removed) folded.2
                  (tasks group.tasks (erased, targets) prior)
  exact loop _ state [ref] [] targets unique

/-- Cache exposure, private starts and failure removal all retain unique computation keys. -/
theorem State.startGroup_taskNodeKeysUnique {state : State}
    (unique : state.queue.TaskNodeKeysUnique) (ref : Nat) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat))
    : (state.startGroup ref targets available).1.queue.TaskNodeKeysUnique := by
  have cached := unique.cacheTaskFailures available
  have tasks (more : List Occurrence) (queue : ReferenceWorkQueue.State)
      (prior : queue.TaskNodeKeysUnique)
      : (more.foldl (fun current task => current.startTask task available)
          queue).TaskNodeKeysUnique := by
    induction more generalizing queue with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.startTask task available)
  unfold State.startGroup
  dsimp only
  split
  · exact cached
  · split
    · exact tasks _ _ cached
    · exact State.removeGroup_taskNodeKeysUnique cached _ _

/-- The complete delayed startup preserves computation-key uniqueness at each group cut. -/
theorem State.startNewWork_taskNodeKeysUnique {state : State}
    (unique : state.queue.TaskNodeKeysUnique) (more : ReferenceWorkQueue.NewWork)
    (integrated : IntegratedWork) (targets : List CleanupTarget)
    (available : List (Occurrence × Nat))
    : (state.startNewWork more integrated targets
        available).1.queue.TaskNodeKeysUnique := by
  have streams (nodes : List Execution.DeliveryNode) (queue : ReferenceWorkQueue.State)
      (prior : queue.TaskNodeKeysUnique)
      : (nodes.foldl (fun current stream => current.startStream stream.ref)
          queue).TaskNodeKeysUnique := by
    induction nodes generalizing queue with
    | nil => exact prior
    | cons stream rest ih =>
        apply ih (queue.startStream stream.ref)
        unfold ReferenceWorkQueue.State.startStream
        split <;> exact prior
  have tasks (nodes : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
      (prior : queue.TaskNodeKeysUnique)
      : (nodes.foldl (fun current task => current.startTask task.occurrence available)
          queue).TaskNodeKeysUnique := by
    induction nodes generalizing queue with
    | nil => exact prior
    | cons task rest ih => exact ih _ (prior.startTask task.occurrence available)
  have groups (refs : WorkQueueSemantics.NodeRefs)
      (acc : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent)
      (prior : acc.1.queue.TaskNodeKeysUnique)
      : (refs.foldl
          (fun (current, targets, failures) ref =>
            let (next, targets, queued) := current.startGroup ref targets available
            (next, targets, failures ++ queued)) acc).1.queue.TaskNodeKeysUnique := by
    induction refs generalizing acc with
    | nil => exact prior
    | cons ref rest ih =>
        exact ih _ (State.startGroup_taskNodeKeysUnique prior ref _ available)
  unfold State.startNewWork
  split
  · exact unique
  · exact groups _ _ (tasks _ _ (streams _ _ unique))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
