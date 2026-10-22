import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailureReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedErrorAccumulation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedFailureReports
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeRegistrationHistory

/-! Retired error caches yield actual positive completion reports on the common witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- A concretely retained failure on an absent final contributor covers its object task.
Witness: absence forces a permanent marker, and normalized replay supplies its positive
same-group or ancestor report on the existing publication matching and failure cuts.
This uses no terminal reporting law.
-/
theorem retainedContributor_task_reported {work inputs address owners producer payload}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (explained
      : Explains work (initialQueue work).initialGroups
          (initialQueue work).initialStreams w.events w.matching w.failures)
    (known : TaskAt work (.executionGroup address) owners producer payload)
    {group dependencies birth} (record : NodeAt work group .group dependencies birth)
    (contributes : group.ref ∈ owners)
    (retained : ((initialQueue work).runNormalized inputs).1.FailureRetained group.ref)
    (absent : ((initialQueue work).runNormalized inputs).1.groupNode? group.ref = none)
    : FailureReportedFor w.events payload.path := by
  exact cancelledContributor_task_reported generated valid started history explained known
    record contributes (retained.cancelled_of_absent
      (createWorkQueue_runNormalized_groupRefsUnique _ inputs) absent)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
