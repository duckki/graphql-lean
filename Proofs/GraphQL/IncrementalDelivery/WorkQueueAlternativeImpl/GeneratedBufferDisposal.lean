import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PreparedSourceProgress
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceCompletion

/-! Universal mixed-release source disposal without an assumed live buffer owner. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Generated owner existence removes the remaining buffer-ownership premise
-----------------------------------------------------------------------------------------

/-- Every dropped stored buffer's held source is transferred or requested by that dispatch.
Live-owner existence is derived for the actual snapshot; native acquisitions remain
independently supplied, and requesting cleanup does not assert asynchronous settlement.
-/
def GeneratedStoredReleaseDisposal : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ resources : ResourceState,
        let before := ((State.initialize work).runNormalized inputs).1
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        let snapshot := registrationSnapshot before.queue event
        let observed := resources.observeCompletionAndCleanup before event
        ResourceReplay resources observed.2 observed.1
        ∧ ∀ occurrence node key,
            snapshot.taskNode? occurrence = some node
            → node.value.isSome = true
            → key ∈ node.childStreams
            → reduced.state.queue.taskNode? occurrence = none
            → key ∈ reduced.state.queue.rootStreams
              ∨ (.cancelSource key ∈ reduced.effects
                  ∧ (resources (.stream key) = .owned .queue
                      → observed.1 (.stream key) = .cleanupRequested .queue))

/-- Actual handler source progress supplies disposal and the same completion/request
history, without reconstructing a frontier or assuming a live buffer owner.
-/
theorem GeneratedStoredReleaseDisposal_holds : GeneratedStoredReleaseDisposal := by
  intro work inputs event generated valid started release resources
  dsimp only
  let before := ((State.initialize work).runNormalized inputs).1
  refine ⟨resources.observeCompletionAndCleanup_replay before event, ?_⟩
  intro occurrence node key found stored held dropped
  rcases generatedPrepared_sourceClassified generated valid started release found stored held with
    retained | active | requested
  · rw [dropped] at retained
    contradiction
  · exact .inl active
  · refine .inr ⟨requested, ?_⟩
    intro owned
    apply resources.observeCompletionAndCleanup_requested before event (.stream key) _
      (List.mem_filterMap.mpr ⟨.cancelSource key, requested, rfl⟩) owned
    cases event with
    | taskSuccess | streamItems => intro same; cases same
    | taskFailure | groupFailure | streamSuccess | streamFailure => cases release

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
