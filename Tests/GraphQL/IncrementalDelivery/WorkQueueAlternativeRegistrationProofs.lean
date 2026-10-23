import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedFailureCut
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationReachability
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationScopeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationDispatch
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.QueryObservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReceiptLifecycle
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedCallbacks
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationSnapshotProjection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.BufferedOwnerExistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SourceRecordPreservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GeneratedBufferDisposal
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RegistrationRejection
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskRegistration

/-! Registration proof targets, axiom audits, and the unrestricted raw-input boundary.

The counterexample below is intentionally malformed: one task occurrence has conflicting
catalogue contributors. It refutes an old auxiliary all-raw-input claim, not the generated
public replay proposition. Structural TaskMatches provenance excludes this conflict.
-/

namespace AlternativeRegistrationProofChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue

example {work inputs event}
    (generated : ReferenceWorkQueue.ExecutedWork work)
    (valid : ReferenceWorkQueue.ValidGraphEvents work (inputs.flatten ++ [event]))
    (started : ReferenceWorkQueue.inputsStarted work inputs = true)
    : NativeRefinement.SnapshotProjection
        ((State.initialize work).runNormalized inputs).1.queue event :=
  NativeRefinement.generatedSnapshot_projection generated valid started

example : NativeRefinement.GeneratedSnapshotTaskEvidence :=
  NativeRefinement.GeneratedSnapshotTaskEvidence_holds

example : NativeRefinement.GeneratedSnapshotBufferedOwners :=
  NativeRefinement.GeneratedSnapshotBufferedOwners_holds

example : NativeRefinement.GeneratedPublicationExclusionTransfer :=
  NativeRefinement.GeneratedPublicationExclusionTransfer_holds

example : NativeRefinement.GeneratedPendingBufferLossCut :=
  NativeRefinement.GeneratedPendingBufferLossCut_holds

example : NativeRefinement.GeneratedStoredReleaseDisposal :=
  NativeRefinement.GeneratedStoredReleaseDisposal_holds

example : NativeRefinement.GeneratedRepresentedSourceProgress :=
  NativeRefinement.GeneratedRepresentedSourceProgress_holds

private def node (key : Nat) : Execution.DeliveryNode := { ref := key, path := [] }

private def task (id owner : Nat) : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [id], groups := [node owner] }

private def conflictingCatalogue : ReferenceWorkQueue.State :=
  {
    rootGroups := [1]
    registeredGroups := [1, 2]
    groupNodes :=
      [
        { group := { node := node 1 }, tasks := [.executionGroup [9]], pending := 1 },
        { group := { node := node 2 } }
      ]
    tasks := [task 9 1, task 10 2]
    taskNodes := [{ task := task 9 1 }]
  }

private def conflictingResult : GraphEvent :=
  .taskSuccess (.executionGroup [9])
    { value := { path := [], data := [] }, work := { tasks := [task 10 1] } }

private def owners (queue : ReferenceWorkQueue.State) : Option (List Nat) :=
  (queue.taskNode? (.executionGroup [10])).map
    (fun node => node.task.groups.map Execution.DeliveryNode.ref)

example
    : owners
        (({ queue := conflictingCatalogue } : State).handleGraphEvent
          conflictingResult).1.queue
      = some [2] := by decide

example
    : owners (conflictingCatalogue.handleGraphEvent conflictingResult).1 = some [1] := by
  decide

/-- Arbitrary raw kernel equality is too strong after occurrence-based delayed activation.
This checks the exact difference, not a serialized-state comparison or an unproved premise.
-/
theorem conflicting_raw_dispatch_differs
    : (({ queue := conflictingCatalogue } : State).handleGraphEvent
        conflictingResult).1.queue
      ≠ (conflictingCatalogue.handleGraphEvent conflictingResult).1 := by
  intro same
  have selected := congrArg owners same
  have alternative : owners (({ queue := conflictingCatalogue } : State).handleGraphEvent
      conflictingResult).1.queue = some [2] := by decide
  have reference : owners (conflictingCatalogue.handleGraphEvent conflictingResult).1
      = some [1] := by decide
  rw [alternative, reference] at selected
  cases selected

#check State.addTask_registrationCore
#check State.maybeIntegrateWork_registrationCore
#check State.addTask_active_iff
#check State.addTask_complete_eq_reference
#check State.initialize_fromReference
#check State.initialize_pendingAccounting
#check referencePrefix_addTask_complete
#check State.maybeIntegrateWork_complete
#check activateRegisteredTasks_lookup
#check State.maybeIntegrateWork_startTasks
#check State.startNewWork_queue
#check referencePrefix_streamItems
#check successGroupFold_activateRegisteredTasks
#check referencePrefix_taskSuccess
#check referencePrefix_handleGraphEvent
#check referencePrefix_handleGraphEvents
#check replayMatchesReference_holds
#check createWorkQueueForScheduleMatchesReference_holds
#check createWorkQueueForScheduleConforms_holds
#check responseReplayMatchesReference_holds
#check ResponseStreamCursor.queryObservation
#check createWorkQueueForScheduleMatchesReference_of_replay
#check createWorkQueueForScheduleConforms_of_replay

#print axioms State.addTask_registrationCore
#print axioms State.maybeIntegrateWork_registrationCore
#print axioms State.addTask_active_iff
#print axioms matchedTasks_eq_of_occurrence_eq
#print axioms State.addTask_complete_eq_reference
#print axioms State.initialize_fromReference
#print axioms State.addTask_pendingTracks
#print axioms State.maybeIntegrateWork_pendingTracks
#print axioms State.maybeIntegrateWork_unsettledTaskLinks
#print axioms State.initialize_pendingAccounting
#print axioms referencePrefix_addTask_complete
#print axioms registerTasks_complete
#print axioms activateRegisteredTasks_addStreams
#print axioms State.maybeIntegrateWork_complete
#print axioms activateRegisteredTasks_eq_startTasks
#print axioms State.maybeIntegrateWork_startTasks
#print axioms activateRegisteredTasks_pruneEmptyGroups
#print axioms State.startNewWork_queue
#print axioms State.integrateStreamItem_cache_projects
#print axioms referencePrefix_preparedItems_invariants
#print axioms referencePrefix_streamRegistrationFold
#print axioms referencePrefix_streamItems
#print axioms activateRegisteredTasks_finishGroupSuccess
#print axioms successGroupFold_activateRegisteredTasks
#print axioms State.taskSuccess_registrationDebt
#print axioms State.taskSuccess_projection
#print axioms referencePrefix_taskSuccess
#print axioms State.handleGraphEvent_stopped
#print axioms referencePrefix_handleGraphEvent
#print axioms referencePrefix_handleGraphEvents
#print axioms State.runNormalized_initialize
#print axioms replayMatchesReference_holds
#print axioms createWorkQueueForScheduleMatchesReference_holds
#print axioms createWorkQueueForScheduleConforms_holds
#print axioms responseReplayMatchesReference_holds
#print axioms ResponseStreamCursor.queryObservation
#print axioms graphEffects_adoptedProducers
#print axioms graphEffects_acknowledgedStreams
#print axioms NativeRefinement.ReceiptReplay.full_streamItems
#print axioms NativeRefinement.BufferedCallbacks.stale_dispatch
#print axioms NativeRefinement.BufferedCallbacks.projectBatch_alternative
#print axioms NativeRefinement.referencePrefix_snapshotProjection
#print axioms NativeRefinement.generatedSnapshot_projection
#print axioms NativeRefinement.GeneratedSnapshotTaskEvidence_holds
#print axioms NativeRefinement.GeneratedSnapshotBufferedOwners_holds
#print axioms NativeRefinement.generatedSnapshot_removalForest
#print axioms NativeRefinement.generatedReplay_dispatchProjection
#print axioms NativeRefinement.GeneratedPublicationExclusionTransfer_holds
#print axioms NativeRefinement.GeneratedPendingBufferLossCut_holds
#print axioms NativeRefinement.GeneratedStoredReleaseDisposal_holds
#print axioms NativeRefinement.GeneratedRepresentedSourceProgress_holds
#print axioms NativeRefinement.State.startNewWork_lookup_existing
#print axioms State.maybeIntegrateWork_lookup_other
#print axioms State.maybeIntegrateWork_rejected
#print axioms State.startNewWork_rejected
#print axioms State.taskSuccess_ownerless_aborted
#print axioms NativeRefinement.streamRegistrationFold_existingTask_progress
#print axioms NativeRefinement.streamRegistrationFold_ownerless_target
#print axioms NativeRefinement.GeneratedAdoptedTaskRegistrationProgress_holds
#print axioms createWorkQueueForScheduleMatchesReference_of_replay
#print axioms createWorkQueueForScheduleConforms_of_replay
#print axioms conflicting_raw_dispatch_differs

end AlternativeRegistrationProofChecks
