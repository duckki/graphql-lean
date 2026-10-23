import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupPublicationFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupRetirement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger

/-! Generated startup replay has one exact publication and closure ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Actual startup replay derives its publication ledger without new source premises.
One set of occurrence labels supports exact payloads, buffered/prepared closure coverage,
and producer-before-stream release under the ordinary publisher with retained pending controls.
-/
theorem ExecutedWork.startup_runNormalized_bufferedCoverage {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (batches : List (List GraphEvent)) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ published : List ObjectPublication,
        published.map Prod.snd
          = (initial.runNormalized batches).2.flatten.flatMap normalizedObjectValues
        ∧ (initial.runNormalized batches).1.PublicationInventory
            (ObjectValueFrom batches.flatten) published
        ∧ initial.BatchClosuresCovered batches published
        ∧ NormalizedStreamReleasePublications work published
            (initial.runNormalized batches).2.flatten
        ∧ published.map Prod.snd = initial.batchedObjectValues batches := by
  obtain ⟨published, values, inventory, covered, streams, raw⟩ :=
    State.runNormalized_startup_bufferedCoverage _ generated
    (State.initializeWithStartup_publicationInventory _ startup)
    (State.initializeWithStartup_pendingAccounting work generated.declarations startup)
    (State.initializeWithStartup_storedTaskLinks _ startup)
    (State.initializeWithStartup_childStreamsSettled _ startup)
    (State.initializeWithStartup_childStreamsMatchWork _ startup work)
    (State.initializeWithStartup_groupMembershipOrder _ startup)
    (State.initializeWithStartup_cancellationsRetired work generated startup)
    batches valid (by rwa [← inputsStartedWithStartup_eq_batchesStarted])
  exact ⟨published, values, inventory, covered, streams, raw⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
