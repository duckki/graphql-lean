import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationTaskCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay

/-! The local registration bridge's invariants come from actual reference-prefix replay. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

/-- Every matching reference prefix retains structural task-catalogue provenance.
Witness: initialize from execution work and reuse reference handler preservation.
-/
theorem referencePrefix_registeredTasksMatch {work : Work}
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : ((ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
        events).RegisteredTasksMatch
        work := by
  have loop (more : List GraphEvent) (queue : ReferenceWorkQueue.State)
      (registered : queue.RegisteredTasksMatch work)
      (sources : ∀ event ∈ more, event.MatchesWork work)
      : (queue.replayGraphEvents more).RegisteredTasksMatch work := by
    induction more generalizing queue with
    | nil => exact registered
    | cons event rest ih =>
        exact ih _ (registered.handleGraphEvent event (sources event List.mem_cons_self))
          (fun next member => sources next (List.mem_cons_of_mem _ member))
  exact loop events _
    (ReferenceWorkQueue.createWorkQueue_fromSpec_registeredTasksMatch work) matching

/-- The active-task completion bridge applies to every matching generated reference prefix.
Witness: reuse reference replay's root presence and catalogue provenance. The bridge's
invariants are derived from the unchanged source/work model, not requested from the host.
The caller's task match is the structural child-task fact provided by MatchesWork.
-/
theorem referencePrefix_addTask_complete {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work) (events : List GraphEvent)
    (matching : ∀ event ∈ events, event.MatchesWork work) (task : ReferenceWorkQueue.Task)
    (known : ReferenceWorkQueue.TaskMatches work task)
    : let queue :=
        (ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work)).replayGraphEvents
          events
      let state : State := { queue }
      (if (state.addTask task).2 = .active then
          (state.addTask task).1.queue.startTask task.occurrence
        else
          (state.addTask task).1.queue)
      = queue.addTask task := by
  exact State.addTask_complete_eq_reference
    (generated.replayGraphEvents_rootsPresent events matching)
    (referencePrefix_registeredTasksMatch events matching) task known

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
