import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeSharedOwnerFailureChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : ReferenceWorkQueue.ExecutedWork SharedOwnerFailure.work :=
  SharedOwnerFailure.executed

example : SharedOwnerFailure.schedule.ValidFor SharedOwnerFailure.work :=
  SharedOwnerFailure.source_valid

example
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        SharedOwnerFailure.inputs.flatten :=
  SharedOwnerFailure.valid_events

example
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work SharedOwnerFailure.inputs
      = true :=
  SharedOwnerFailure.started

example
    : StopCoverage SharedOwnerFailure.lastFailure.state SharedOwnerFailure.requested :=
  SharedOwnerFailure.final_coverage

-- The independent wire/accounting contract still holds; it does not assert resource disposal.
example
    : (createWorkQueueForSchedule SharedOwnerFailure.work
        SharedOwnerFailure.schedule).Conforms
        SharedOwnerFailure.work :=
  createWorkQueueForScheduleConforms_holds _ _ SharedOwnerFailure.executed
    SharedOwnerFailure.nonempty SharedOwnerFailure.source_valid

example
    : (createWorkQueueForSchedule SharedOwnerFailure.work
        SharedOwnerFailure.schedule).workEventStream.finished
        ((State.initialize SharedOwnerFailure.work).runNormalized
          SharedOwnerFailure.inputs).2 := by
  refine ⟨SharedOwnerFailure.inputs, SharedOwnerFailure.admitted, rfl, ?_⟩
  change ((State.initialize SharedOwnerFailure.work).runNormalized SharedOwnerFailure.inputs).1.queue.terminated
    = true
  rw [SharedOwnerFailure.actual_replay_state]
  exact SharedOwnerFailure.terminated

#print axioms SharedOwnerFailure.generated_disposal
#print axioms SharedOwnerFailure.work_shape
#print axioms SharedOwnerFailure.source_valid
#print axioms SharedOwnerFailure.started
#print axioms SharedOwnerFailure.handoff
#print axioms SharedOwnerFailure.disposal
#print axioms SharedOwnerFailure.actual_replay_state
#print axioms createWorkQueueForScheduleConforms_holds

end AlternativeSharedOwnerFailureChecks
