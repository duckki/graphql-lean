import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResourceHandoff
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PreparedSourceProgress

/-! Prepared held sources keep a concrete record or enter actual cleanup. This is the
handler preservation edge needed by a same-run resource bridge, not native completeness.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open GraphQL.IncrementalDelivery.WorkQueueSemantics (Occurrence)
open GraphQL.IncrementalDelivery.ReferenceWorkQueue (TaskNode)

-----------------------------------------------------------------------------------------
-- Still-owned leases cannot take the actual cleanup branch
-----------------------------------------------------------------------------------------

/-- Any still-queue-owned prepared source has a concrete endpoint record after actual
completion, handoff, and cleanup. This covers both old and newly adopted leases without
inferring acquisitions from records or assuming inventory completeness.
-/
def GeneratedDispatchSourceRepresentation : Prop :=
  ∀ work inputs event,
    ReferenceWorkQueue.ExecutedWork work
    → ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event])
    → ReferenceWorkQueue.inputsStarted work (inputs ++ [[event]]) = true
    → (match event with
        | .taskSuccess _ _ | .streamItems _ _ => True
        | _ => False)
    → ∀ (resources : ResourceState) (inventories : ProducerInventories)
        (occurrence : Occurrence) (node : TaskNode) key,
        let before := ((State.initialize work).runNormalized inputs).1
        let snapshot := registrationSnapshot before.queue event
        let reduced := ({ state := before } : GraphBatchResult).handleGraphEvent event
        snapshot.taskNode? occurrence = some node
        → node.value.isSome = true
        → key ∈ node.childStreams
        → (resources.observeDispatch inventories before event).1 (.stream key)
          = .owned .queue
        → RecordTargetRepresented reduced.state.queue (.stream key)

/-- Eliminate actual cancellation using the same observer's cleanup phase. The independent
resource inventory need not be complete for this preservation fact.
-/
theorem GeneratedDispatchSourceRepresentation_of_progress
    (progress : GeneratedPreparedSourceProgress)
    : GeneratedDispatchSourceRepresentation := by
  intro work inputs event generated valid started release resources inventories
    occurrence node key
  dsimp only
  intro found stored held owned
  rcases progress work inputs event generated valid started release occurrence node key found
      stored held with represented | requested
  · exact represented
  · obtain ⟨_, absent⟩ := ResourceState.requestQueueCleanup_still_owned _ _ (.stream key) owned
    exact False.elim (absent (List.mem_filterMap.mpr ⟨.cancelSource key, requested, rfl⟩))

/-- Universal prepared-source representation through the actual accepting dispatch. -/
theorem GeneratedDispatchSourceRepresentation_holds
    : GeneratedDispatchSourceRepresentation :=
  GeneratedDispatchSourceRepresentation_of_progress GeneratedPreparedSourceProgress_holds

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
