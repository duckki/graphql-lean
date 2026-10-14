import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskSources
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedDispatchBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceRecords

/-! Prepared source coverage at the actual normalized next-input boundary. Both accepting
handlers use their real registration/settlement/drain reductions; no reconstructed failure
targets, output-filter disposal algorithm or failure-cut construction is assumed.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)
open ReferenceWorkQueue (TaskNode)

/-- Registration-bearing inputs, named independently of their source-validity evidence. -/
def RegistrationInput : GraphEvent → Prop
  | .taskSuccess _ _ | .streamItems _ _ => True
  | _ => False

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
    (stored : node.value.isSome = true) (held : key ∈ node.childStreams)
    : let before := ((State.initialize work).runNormalized inputs).1
      let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
      reduced.state.queue.taskNode? occurrence = some node
      ∨ key ∈ reduced.state.queue.rootStreams
      ∨ .cancelSource key ∈ reduced.effects := by
  obtain ⟨raw, _, accepted⟩ := generatedReplay_beforeNext generated valid started
  obtain ⟨prior, matched, _⟩ := ReferenceWorkQueue.validGraphEvents_last valid
  rw [generatedReplay_beforeNextState generated valid started, raw]
  rw [raw] at found
  simp only [GraphBatchResult.handleGraphEvent, List.nil_append]
  cases event with
  | taskSuccess incoming result =>
      exact referencePrefix_taskSuccess_sources generated inputs.flatten incoming result
        valid accepted occurrence node key found stored held
  | streamItems stream items =>
      exact referencePrefix_streamItems_sources generated inputs.flatten prior accepted
        stream items matched occurrence node key found held
  | taskFailure | streamSuccess | streamFailure => cases release

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
  rcases generatedPrepared_sourceClassified generated valid started release found stored held with
    retained | active | requested
  · exact .inl (.bufferedStream retained stored held)
  · exact .inl (.activeStream active)
  · exact .inr requested

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
