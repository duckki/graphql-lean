import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationInitialization
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedReleaseProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupFrames

/-! Initial synchronous activation projects exactly, including its deferred notices. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Both initializers retain the same kernel and the same ordered startup reports.
The concrete finite removal forest and live-task frame come from generated work;
no endpoint equality or output accounting is assumed of the host.
-/
theorem State.initializeWithStartup_projects {work : Work}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (startup : ReferenceWorkQueue.InitialStartup)
    : (State.initialize work startup).queue
      = ReferenceWorkQueue.State.initialize
          (ReferenceWorkQueue.Work.fromExecution work) startup := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  let initial : State := { queue := {} }
  let lowered := ReferenceWorkQueue.Work.fromExecution work
  let integrated := initial.maybeIntegrateWork lowered
  let pruned := integrated.1.queue.pruneEmptyGroups integrated.2.newGroups
  let ready : State := { integrated.1 with queue := pruned.1 }
  let released : ReferenceWorkQueue.NewWork :=
    { integrated.2.newWork with newGroups := pruned.2 }
  obtain ⟨same, roots, inactive⟩ := initial.maybeIntegrateWork_eq_reference_of_no_roots
    lowered rfl
  have groups := congrArg ReferenceWorkQueue.NewWork.newGroups roots
  have streams := congrArg ReferenceWorkQueue.NewWork.newStreams roots
  simp only [IntegratedWork.newWork] at groups streams
  dsimp only [initial, lowered] at same groups streams
  have readyEq : ready.queue = (ReferenceWorkQueue.initialPreparation work).1 := by
    dsimp only [ready, pruned, integrated, ReferenceWorkQueue.initialPreparation,
      initial, lowered]
    simp only [same, groups]
  have releasedEq : released = (ReferenceWorkQueue.initialPreparation work).2 := by
    dsimp only [released, pruned, integrated, ReferenceWorkQueue.initialPreparation,
      initial, lowered]
    simp only [IntegratedWork.newWork, same, groups, streams]
  have readyRunning : ready.stopped = false := initial.maybeIntegrateWork_stopped lowered
  have frame : ready.queue.TaskOwnerFrame work := by
    rw [readyEq]
    exact ReferenceWorkQueue.initialPreparation_taskOwnerFrame work
  have forest : ready.queue.RemovalForest parents := by
    rw [readyEq]
    exact generated.initialPreparation_removalForest parents canonical
  have activeEq : integrated.2.activeTasks.foldl
      (fun current task => current.startTask task.occurrence startup.failures)
      ready.queue = ready.queue := by rw [inactive]; rfl
  have projected := ready.startNewWork_projects released integrated.2 [] readyRunning
    startup.failures (activeEq ▸ frame) (activeEq ▸ forest)
  rw [activeEq, readyEq, releasedEq] at projected
  simp only [State.initialize, ReferenceWorkQueue.State.initialize]
  have updated := congrArg (fun result : ReferenceWorkQueue.State
      × List ReferenceWorkQueue.GroupFailureEvent =>
    { result.1.enqueueGroupFailures result.2 with
        initialGroups := pruned.2
        initialStreams := released.newStreams }) projected
  simpa only [Bool.false_eq_true, ↓reduceIte, ready, released, pruned, integrated,
    initial, lowered, ReferenceWorkQueue.initialPreparation, IntegratedWork.newWork, same,
    groups, streams]
    using updated

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
