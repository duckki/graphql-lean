import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailableTaskHandlerProgress

/-! Generated eventwise task-resource progress specializes the local cache-aware proof
at the actual source boundary. No additional host or resource endpoint law is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

/-- Every owned prepared task still unsettled after this input retains a concrete record
or receives an abort from the actual dispatch. Includes incoming and previously registered
tasks, even when no computation node has been created.
-/
theorem generatedPreparedTask_progress {work inputs event task}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (registered
      : task
        ∈ (registrationSnapshot
            ((State.initialize work).runNormalized inputs).1.queue event).tasks)
    (pending
      : task.occurrence
        ∉ event.recordTaskOutcome
            (ReferenceWorkQueue.GraphEvent.taskSettlements inputs.flatten))
    (owned
      : ∃ owner ∈ task.groups,
          ∃ group,
            (registrationSnapshot
              ((State.initialize work).runNormalized inputs).1.queue event).groupNode?
              owner.ref
            = some group)
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
      RecordTargetRepresented reduced.state.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.effects := by
  let before := ((State.initialize work).runNormalized inputs).1
  let queue := before.queue
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := generatedReplay_sourceFrame generated canonical valid started
  have accounted := generatedReplay_nextAccounting generated valid started
  have queueKeys : queue.TaskNodeKeysUnique := by
    obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
    change ((State.initialize work).runNormalized inputs).1.queue.TaskNodeKeysUnique
    rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
    exact (ReferenceWorkQueue.createWorkQueue_taskNodeKeysUnique
      (ReferenceWorkQueue.Work.fromExecution work)).runNormalized inputs
  have notSettled : task.occurrence ∉ ReferenceWorkQueue.GraphEvent.taskSettlements
      inputs.flatten := by
    intro member
    apply pending
    cases event with
    | taskSuccess | taskFailure => exact List.mem_cons_of_mem _ member
    | streamItems | groupFailure | streamSuccess | streamFailure => exact member
  have unrejected : queue.TaskRejectionsSatisfy
      (fun rejected _ => rejected ≠ task.occurrence) :=
    (generatedReplay_taskRejections generated valid started).mono
      (fun occurrence _ member same => notSettled (same ▸ member))
  have running := generatedReplay_beforeNextState generated valid started
  change before = { queue := queue } at running
  change let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
    RecordTargetRepresented reduced.state.queue (.task task.occurrence)
      ∨ .abortTask task.occurrence ∈ reduced.effects
  rw [running]
  have progress := sourceFrame_preparedTask_progress_available generated canonical source accounted
    queueKeys valid [] rfl unrejected (by intro occurrence errors member; cases member)
    registered pending owned
  dsimp only [GraphBatchResult.handleGraphEvent]
  rcases progress with represented | aborted
  · exact .inl (represented.withGroupFailures _)
  · exact .inr (List.mem_append_right _ aborted)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
