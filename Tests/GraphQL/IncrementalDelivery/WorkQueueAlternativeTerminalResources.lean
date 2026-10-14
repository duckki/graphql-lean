import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.TerminalResourceInvariant
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

/-! Terminal safety roots and the real generated terminal batch's requested source lease. -/

namespace AlternativeTerminalResourcesChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedDispatchTerminalNoOwned := GeneratedDispatchTerminalNoOwned_holds

example : GeneratedResourceSingletonBatchInvariant :=
  GeneratedResourceSingletonBatchInvariant_holds

-- Terminal clearing preserves a pending asynchronous request, without pretending it settled.
example
    : let observed :=
        State.observeResourceBatch SharedOwnerFailure.firstFailure.state
          SharedOwnerFailure.requested (fun _ => []) [SharedOwnerFailure.failureH]
      observed.dispatch.state.stopped = true
      ∧ observed.resources (.stream 2) = .cleanupRequested .queue := by
  constructor
  · cbv
  · cbv

-- Root absence by itself is insufficient for raw malformed buffers.
private def orphanNode : ReferenceWorkQueue.TaskNode :=
  {
    task := { occurrence := SharedOwnerFailure.heldProducer, groups := [] }
    value := some { path := [], data := [] }
    childStreams := [2]
  }

private def orphan : ReferenceWorkQueue.State := { taskNodes := [orphanNode] }

example : (orphan.rootGroups.isEmpty && orphan.rootStreams.isEmpty) = true := rfl

example : RecordTargetRepresented orphan (.stream 2) := by
  apply RecordTargetRepresented.bufferedStream (occurrence := SharedOwnerFailure.heldProducer)
    (node := orphanNode) rfl rfl
  exact List.mem_cons_self

example : ¬orphan.BufferedOwnersPresent := by
  intro owners
  obtain ⟨_, _, impossible⟩ := owners _ List.mem_cons_self rfl
  cases impossible

#print axioms recordTargetRequiresRoot
#print axioms generatedDispatch_recordRootEvidence
#print axioms GeneratedDispatchTerminalNoOwned_holds
#print axioms GeneratedResourceSingletonBatchInvariant_holds

end AlternativeTerminalResourcesChecks
