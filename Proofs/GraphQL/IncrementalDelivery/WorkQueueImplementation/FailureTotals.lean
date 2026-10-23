import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupFailureSource
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedTaskErrors

/-! Exact aggregate source causes bridge to the scheduler's reporting accounting. -/

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

/-- Distinct exact source causes give a positive aggregate reporting witness.
Source occurrence availability is supplied separately from causal failure-cut licensing.
-/
theorem GroupFailureSources.nodeFailureCauses {work inputs ref errors}
    (sources : GroupFailureSources work inputs ref errors) (generated : ExecutedWork work)
    (available : List Occurrence)
    (included
      : ∀ occurrence count,
          GraphEvent.taskFailure occurrence count ∈ inputs → occurrence ∈ available)
    : NodeFailureCauses work available ref errors := by
  obtain ⟨causes, nonempty, distinct, total, known⟩ := sources
  refine ⟨causes, nonempty, distinct, ?_, total.symm⟩
  intro occurrence count member
  obtain ⟨received, owners, producer, path, failed, owner⟩ := known occurrence count member
  exact ⟨included occurrence count received, owners, producer, _, failed, owner, rfl,
    generated.taskFailure_positive failed rfl⟩

/-- Every actual failed group report has positive distinct causes in the source inventory.
Output provenance and execution positivity supply this local aggregate witness;
reporting-cut visibility and causal licensing remain separate obligations.
-/
theorem createWorkQueue_runNormalized_groupFailure_nodeFailureCausesWitness
    {work : Execution.Work} (generated : ExecutedWork work)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {group errors}
    (emitted
      : Execution.WorkQueueEvent.groupFailure group errors
        ∈ ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            publicationAtoms)
    : NodeFailureCauses work (GraphEvent.failureSettlements batches.flatten) group.ref
        errors := by
  have sources := createWorkQueue_runNormalized_atomicGroupFailure_source generated valid emitted
  apply sources.nodeFailureCauses generated
  intro occurrence count member
  exact List.mem_reverse.mpr (List.mem_flatMap.mpr
    ⟨.taskFailure occurrence count, member, List.mem_cons_self⟩)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
