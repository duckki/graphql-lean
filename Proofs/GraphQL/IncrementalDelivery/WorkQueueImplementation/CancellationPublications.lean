import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReplayCancellation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamFailureAccounting

/-! Rejected failures are cancelled relative to actual normalized publications. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact publication provenance discharges nonpublication for rejected failures
-----------------------------------------------------------------------------------------

/-- A rejected failed task is cancelled relative to the runner's actual output history.
Witness: exact publications have successful fixed payloads, so they cannot publish the
matched failed task. Owner replay supplies cancellation from earlier eligible failures.
No explained history, admitted output, or ordered failure-cut witness is assumed.
-/
theorem ExecutedWork.runNormalized_rejectedFailure_cancelled {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (matching : PublicationMatching)
    (exactValues
      : let atoms :=
          ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms
        ∀ index event,
          atoms[index]? = some event
          → IsValue event
          → PublicationAt work (matching index) event)
    {occurrence taskNode errors}
    (source : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (found
      : ((State.initialize (Work.fromExecution work)).runNormalized batches).1.taskNode?
          occurrence
        = some taskNode)
    (fresh : occurrence ∉ GraphEvent.taskSettlements batches.flatten)
    (rejected
      : State.taskHasHealthyOwner
          ((State.initialize (Work.fromExecution work)).runNormalized batches).1
          taskNode.task
        = false)
    : Causality.TaskCancelled work
        ((State.initialize (Work.fromExecution work)).objectFailureContributions
          batches.flatten)
        (Published matching
          (((State.initialize (Work.fromExecution work)).runNormalized
              batches).2.flatten.flatMap
            publicationAtoms)) occurrence := by
  obtain ⟨owners, producer, path, known⟩ := source
  exact generated.runNormalized_rejectedTask_cancelled valid started found fresh rejected
    (failedTask_unpublished_of_exactValues exactValues known rfl)

/-- One actual output matching also cancels every fresh rejected failed task at this boundary.
Witness: construct the normalized publication matching once, then use its exact payloads
for each rejected failure. Nonpublication is derived rather than a caller-supplied premise.
This remains snapshot cancellation; ordered-cut licensing is a separate obligation.
-/
theorem ExecutedWork.runNormalized_rejectedFailures_matching {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let outputs := (queue.runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index))
        ∧ ∀ occurrence taskNode errors,
            (GraphEvent.taskFailure occurrence errors).MatchesWork work
            → (queue.runNormalized batches).1.taskNode? occurrence = some taskNode
            → occurrence ∉ GraphEvent.taskSettlements batches.flatten
            → (queue.runNormalized batches).1.taskHasHealthyOwner taskNode.task = false
            → Causality.TaskCancelled work
                (queue.objectFailureContributions batches.flatten)
                (Published matching atoms) occurrence := by
  obtain ⟨matching, batching, publications⟩ :=
    createWorkQueue_runNormalized_publicationMatching valid started
  refine ⟨matching, batching, publications, ?_⟩
  intro occurrence taskNode errors source found fresh rejected
  exact generated.runNormalized_rejectedFailure_cancelled valid started matching
    (fun index event atEvent value => (publications index event atEvent value).1)
    source found fresh rejected

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
