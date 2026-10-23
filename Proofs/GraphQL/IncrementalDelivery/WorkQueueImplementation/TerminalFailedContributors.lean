import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ContributorRootReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedFailureReports

/-! Every consumed failed contributor is cancelled and reported at actual terminal replay. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Terminal retirement and success-only accounting cancel every consumed failed contributor. -/
theorem ExecutedWork.terminal_failedContributor_cancelled
    {work inputs occurrence owners ref} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (ended
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated
        = true)
    (known : TaskHasOwners work occurrence owners) (contributes : ref ∈ owners)
    (failed : occurrence ∈ GraphEvent.failureSettlements inputs.flatten)
    : ref
      ∈ ((State.initialize (Work.fromExecution work)).runNormalized
          inputs).1.cancelledGroups := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have source := (initial_uncancelledReplayFrame generated canonical).runNormalized
    (before := []) generated canonical inputs valid
    (by rwa [inputsStarted_eq_batchesStarted] at started)
  obtain ⟨task, registered, identity⟩ := source.failures occurrence failed
  obtain ⟨_, actualPayload, actualProducer, _, descriptor⟩ :=
    (source.pending.matching task registered).1
  obtain ⟨producer, payload, structural⟩ := known
  have sameOwners := (TaskAt.unique structural (identity ▸ descriptor)).1
  have actualContributes : ref ∈ task.groups.map Execution.DeliveryNode.ref :=
    sameOwners ▸ contributes
  have retired := generated.terminal_registeredContributor_retired valid started ended
    registered actualContributes
  apply Classical.byContradiction
  intro uncancelled
  have settled := source.owners.retired_contributor_settled registered actualContributes
    uncancelled retired
  exact valid.succeeds_not_failureSettlements
    (valid.groupSettlements_succeed (identity ▸ settled)) failed

namespace ConformancePlan

/-- Every consumed failing owner has a positive report at termination, including cached startup. -/
theorem terminal_failedContributor_reported
    {work inputs occurrence owners group dependencies} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (known : TaskHasOwners work occurrence owners) (contributes : group.ref ∈ owners)
    (failed : occurrence ∈ GraphEvent.failureSettlements inputs.flatten)
    (record : GroupRecordAt work group dependencies)
    : GroupFailureReported w.events group dependencies := by
  have cancelled := generated.terminal_failedContributor_cancelled valid started ended
    known contributes failed
  have reported := generated.runNormalized_cancelledRecordsReported inputs valid started ended
    group dependencies record cancelled
  rwa [← history] at reported

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
