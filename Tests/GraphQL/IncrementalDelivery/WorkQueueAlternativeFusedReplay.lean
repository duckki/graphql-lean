import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.QueryObservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedFailureProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedHandlerFrames

/-! Public replay witnesses use the shared generated-work and source domain.
Host/resource-effect coverage is proved separately, not assumed by these targets.
-/

namespace AlternativeFusedReplayChecks
open GraphQL.IncrementalDelivery.AlternativeWorkQueue

example : replayMatchesReference := replayMatchesReference_holds

example : createWorkQueueForScheduleMatchesReference :=
  createWorkQueueForScheduleMatchesReference_holds

example : responseReplayMatchesReference := responseReplayMatchesReference_holds
example : createWorkQueueForScheduleConforms := createWorkQueueForScheduleConforms_holds

#print axioms State.taskFailure_projection
#print axioms referencePrefix_taskSuccess_drainFrames
#print axioms referencePrefix_streamItems_drainFrames
#print axioms referencePrefix_taskSuccess
#print axioms referencePrefix_streamItems
#print axioms referencePrefix_handleGraphEvent
#print axioms replayMatchesReference_holds
#print axioms createWorkQueueForScheduleMatchesReference_holds
#print axioms responseReplayMatchesReference_holds
#print axioms createWorkQueueForScheduleConforms_holds
#print axioms ResponseStreamCursor.queryObservation

end AlternativeFusedReplayChecks
