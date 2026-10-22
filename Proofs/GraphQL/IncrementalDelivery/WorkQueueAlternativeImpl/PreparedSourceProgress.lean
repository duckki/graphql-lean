import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.AvailablePreparedSourceProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedDispatchBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRecords

/-! Prepared source coverage at the actual normalized next-input boundary. Both accepting
handlers use their real registration/settlement/drain reductions; no reconstructed failure
targets, output-filter disposal algorithm or failure-cut construction is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (TaskNode)

/-- Exact-source classification at the original normalized generated/start boundary.
The retained record, active source and cancellation alternatives belong to the same
dispatch, including newly adopted sources in its registration phase.
-/
theorem generatedPrepared_sourceClassified {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true)
    (release : RegistrationInput event)
    {occurrence : Occurrence} {node : TaskNode} {key : Nat}
    (found
      : ReferenceWorkQueue.State.taskNode?
          (registrationSnapshot ((State.initialize work).runNormalized inputs).1.queue
            event)
          occurrence
        = some node)
    (_stored : node.value.isSome = true) (held : key ∈ node.childStreams)
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
      reduced.state.queue.taskNode? occurrence = some node
      ∨ key ∈ reduced.state.queue.rootStreams
      ∨ .cancelSource key ∈ reduced.effects := by
  obtain ⟨raw, priorStarted, _⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame :=
    (ReferenceWorkQueue.initial_uncancelledReplayFrame generated canonical).runNormalized
      (before := []) generated canonical inputs prior
      (by rwa [ReferenceWorkQueue.inputsStarted_eq_batchesStarted] at priorStarted)
  have keys := ReferenceWorkQueue.createWorkQueue_runNormalized_taskNodeKeysUnique
    (ReferenceWorkQueue.Work.fromExecution work) inputs
  have inventory := ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
    (ReferenceWorkQueue.Work.fromExecution work) inputs
  rw [ReferenceWorkQueue.State.runNormalized_replayBatches] at frame keys inventory
  rw [generatedReplay_beforeNextState generated valid started, raw]
  rw [raw] at found
  simp only [GraphBatchResult.handleGraphEvent, List.nil_append]
  cases event with
  | taskSuccess incoming result =>
      exact sourceFrame_taskSuccess_sources generated canonical frame keys inventory incoming result
        valid found held
  | streamItems stream items =>
      exact sourceFrame_streamItems_sources generated canonical frame keys inventory stream items
        matched found held
  | taskFailure | groupFailure | streamSuccess | streamFailure => cases release

/-- Every stored prepared source is represented after success/item dispatch or cancelled
by that same dispatch. All phase frames and effect boundaries are constructed from the
original generated source/start contract, not supplied as desired endpoint premises.
-/
def GeneratedPreparedSourceProgress : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ (occurrence : Occurrence) (node : TaskNode) key,
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        snapshot.taskNode? occurrence = some node
        → node.value.isSome = true
        → key ∈ node.childStreams
        → RecordTargetRepresented reduced.state.queue (.stream key)
          ∨ .cancelSource key ∈ reduced.effects

theorem GeneratedPreparedSourceProgress_holds : GeneratedPreparedSourceProgress := by
  intro work inputs event generated valid started release occurrence node key
  dsimp only
  intro found stored held
  let before := ((State.initialize work).runNormalized inputs).1
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := generatedReplay_sourceFrame generated canonical valid started
  obtain ⟨raw, _, _⟩ := generatedReplay_beforeNext generated valid started
  have keys : before.queue.TaskNodeKeysUnique := by
    change ((State.initialize work).runNormalized inputs).1.queue.TaskNodeKeysUnique
    rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
    exact ReferenceWorkQueue.createWorkQueue_runNormalized_taskNodeKeysUnique
      (ReferenceWorkQueue.Work.fromExecution work) inputs
  have inventory : before.queue.ChildStreamInventory := by
    change ((State.initialize work).runNormalized inputs).1.queue.ChildStreamInventory
    rw [raw, ← ReferenceWorkQueue.State.runNormalized_replayBatches]
    exact ReferenceWorkQueue.createWorkQueue_runNormalized_childStreamInventory
      (ReferenceWorkQueue.Work.fromExecution work) inputs
  have progress := sourceFrame_preparedSource_progress_available generated canonical source keys
    inventory valid release [] rfl (.bufferedStream found stored held)
  have running := generatedReplay_beforeNextState generated valid started
  change before = { queue := before.queue } at running
  simp only [GraphBatchResult.handleGraphEvent, List.nil_append]
  change RecordTargetRepresented (((before.handleGraphEvent event).1.queue).enqueueGroupFailures
    (before.handleGraphEvent event).2.2.2) (.stream key)
    ∨ .cancelSource key ∈ (before.handleGraphEvent event).2.2.1
  rw [running]
  rcases progress with retained | cancelled
  · apply Or.inl
    cases retained with
    | activeStream active => exact .activeStream active
    | bufferedStream found stored held => exact .bufferedStream found stored held
  · exact .inr cancelled

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
