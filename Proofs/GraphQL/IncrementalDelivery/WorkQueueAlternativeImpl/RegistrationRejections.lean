import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationScopeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskRejections

/-! Registration and delayed starts preserve the origins of retained task rejections. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open WorkQueueSemantics (Occurrence)

/-- Delayed task registration changes no computation node. -/
theorem State.addTask_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property) (task : ReferenceWorkQueue.Task)
    : (state.addTask task).1.queue.TaskRejectionsSatisfy property := by
  intro node member
  rw [State.addTask_taskNodes] at member
  exact prior node member

/-- Delayed integration preserves every retained computation rejection. -/
theorem State.maybeIntegrateWork_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property)
    (work : ReferenceWorkQueue.Work) (parent : Option Occurrence := none)
    : (state.maybeIntegrateWork work parent).1.queue.TaskRejectionsSatisfy property := by
  have loop (tasks : List ReferenceWorkQueue.Task)
      (acc : State × List ReferenceWorkQueue.Task × List ReferenceWorkQueue.Task)
      (supported : acc.1.queue.TaskRejectionsSatisfy property)
      : (tasks.foldl registerTaskStep acc).1.queue.TaskRejectionsSatisfy property := by
    induction tasks generalizing acc with
    | nil => exact supported
    | cons task rest ih =>
        apply ih
        unfold registerTaskStep
        dsimp only
        split <;> exact State.addTask_taskRejections supported task
  exact (loop work.tasks _ (prior.addGroups work.groups)).addStreams work.streams parent

/-- Delayed activation starts only unrejected new nodes and keeps prior rejection facts. -/
theorem State.startNewWork_taskRejections {state : State} {property}
    (prior : state.queue.TaskRejectionsSatisfy property)
    (roots : ReferenceWorkQueue.NewWork) (integrated : IntegratedWork)
    (targets : List CleanupTarget := [])
    : (state.startNewWork roots integrated targets).1.queue.TaskRejectionsSatisfy
        property := by
  cases running : state.stopped with
  | true => simpa only [State.startNewWork, running, ↓reduceIte] using prior
  | false =>
      rw [State.startNewWork_queue _ _ _ _ running]
      have loop (tasks : List ReferenceWorkQueue.Task) (queue : ReferenceWorkQueue.State)
          (supported : queue.TaskRejectionsSatisfy property)
          : (tasks.foldl (fun current task => current.startTask task.occurrence)
              queue).TaskRejectionsSatisfy property := by
        induction tasks generalizing queue with
        | nil => exact supported
        | cons task rest ih => exact ih _ (supported.startTask task.occurrence)
      exact (loop integrated.activeTasks state.queue prior).startNewWork roots

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
