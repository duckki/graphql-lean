import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors

/-! Exact source causes bridge to the scheduler's selected failure accounting. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A generated source rejection gives a positive selected cause on its singleton inventory.
The inventory records the selected task; other received rejections are not summed.
-/
theorem GroupFailureSourceCause.nodeFailureCause {work inputs ref errors}
    (cause : GroupFailureSourceCause work inputs ref errors)
    (generated : ExecutedWork work)
    : ∃ occurrence,
        NodeFailureCause work [occurrence] ref errors
        ∧ ∃ owners producer path,
            GraphEvent.taskFailure occurrence errors ∈ inputs
            ∧ TaskAt work occurrence owners producer (.object path (.error errors))
            ∧ ref ∈ owners := by
  obtain ⟨occurrence, received, owners, producer, path, known, owner⟩ := cause
  exact ⟨
    occurrence,
    ⟨
      occurrence,
      by simp,
      owners,
      producer,
      _,
      known,
      owner,
      rfl,
      generated.taskFailure_positive known rfl
    ⟩,
    owners,
    producer,
    path,
    received,
    known,
    owner
  ⟩

/-- Every actual failed group completion has a singleton positive source-cause witness.
Output provenance and execution positivity supply this local witness; failure-cut
visibility and licensing remain separate obligations.
-/
theorem createWorkQueue_runNormalized_groupFailure_nodeFailureCauseWitness
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms)
    : ∃ occurrence,
        NodeFailureCause work [occurrence] group.ref errors
        ∧ ∃ owners producer path,
            GraphEvent.taskFailure occurrence errors ∈ batches.flatten
            ∧ TaskAt work occurrence owners producer (.object path (.error errors))
            ∧ group.ref ∈ owners :=
  (createWorkQueue_runNormalized_atomicGroupFailure_source generated valid
    emitted).nodeFailureCause
    generated

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
