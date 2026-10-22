import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupPublicationLedger

/-! Actual normalized replay retains one ledger for closure coverage and stream release. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Normalization retains source-handler certificates on the same occurrence labels
-----------------------------------------------------------------------------------------

/-- Generated valid started batching has one ledger for closure maps and stream releases.
Witness: process each actual batch with its joint raw certificate, preserve its labels
through owner normalization, and retain exact consecutive slices for every source handler.
State accounting is derived from creation and source laws, not assumed output admission.
-/
theorem ExecutedWork.runNormalized_bufferedCoverage {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ∃ published : List ObjectPublication,
        published.map (fun publication => publication.2)
          = ((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
              normalizedObjectValues
        ∧ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).1.PublicationInventory
            (ObjectValueFrom batches.flatten) published
        ∧ (State.initialize (Work.fromExecution work)).BatchClosuresCovered batches
            published
        ∧ NormalizedStreamReleasePublications work published
            ((State.initialize (Work.fromExecution work)).runNormalized batches).2.flatten
        ∧ published.map Prod.snd
          = (State.initialize (Work.fromExecution work)).batchedObjectValues batches := by
  let queue := State.initialize (Work.fromExecution work)
  have initial : queue.PublicationInventory (ObjectValueFrom []) [] :=
    ⟨by simp, by simp, createWorkQueue_storedValues _ _⟩
  exact queue.runNormalized_startup_bufferedCoverage generated initial
    (createWorkQueue_pendingAccounting work
      generated.declarations) (createWorkQueue_storedTaskLinks _)
    (createWorkQueue_childStreamsSettled _) (createWorkQueue_childStreamsMatchWork _ _)
    (createWorkQueue_groupMembershipOrder _) (createWorkQueue_cancellationsRetired _)
    batches valid (by rwa [← inputsStarted_eq_batchesStarted])

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
