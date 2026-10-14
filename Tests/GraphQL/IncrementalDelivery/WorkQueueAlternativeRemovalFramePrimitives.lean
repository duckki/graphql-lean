import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLinkDisposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskLinkDispositionHandlers
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerExistence

/-! Reusable removal-frame leaves, without depending on alternative replay equivalence.
GeneratedFusedRemoval and FusedHandlerFrames derive the complete generated phase frames.
-/

namespace AlternativeRemovalFramePrimitiveChecks
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

example (work : Work) : (State.initialize work).TaskLinkDisposition :=
  createWorkQueue_taskLinkDisposition work

example : GeneratedStartedTaskLinks := GeneratedStartedTaskLinks_holds

example {queue : State} {node : TaskNode} (disposition : queue.TaskLinkDisposition)
    (registered : queue.StartedTasksRegistered) (member : node ∈ queue.taskNodes)
    : queue.TaskLinkedOn node.task.occurrence
        (node.task.groups.map GraphQL.IncrementalDelivery.Execution.DeliveryNode.ref) :=
  disposition.startedLinks registered member

#print axioms createWorkQueue_taskLinkDisposition
#print axioms State.TaskLinkDisposition.startedLinks
#print axioms State.TaskLinkDisposition.maybeIntegrateWork
#print axioms State.TaskLinkDisposition.startNewWork
#print axioms State.TaskLinkDisposition.finishGroupSuccess
#print axioms State.TaskLinkDisposition.drainReadyGroups
#print axioms State.TaskLinkDisposition.handleGraphEvent
#print axioms State.TaskLinkDisposition.replayGraphEvents
#print axioms ExecutedWork.runNormalized_taskLinkDisposition
#print axioms GeneratedStartedTaskLinks_holds
#print axioms ExecutedWork.replayGraphEvents_bufferedOwnersPresent
#print axioms ExecutedWork.runNormalized_bufferedOwnersPresent

end AlternativeRemovalFramePrimitiveChecks
