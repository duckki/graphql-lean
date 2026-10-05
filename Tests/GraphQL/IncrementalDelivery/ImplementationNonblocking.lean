import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Nonblocking
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NonblockingReadiness

/-! Finite nonblocking is an optional host-policy property,
not a consequence of validity. -/

namespace GraphQL.IncrementalDelivery.Tests.ImplementationNonblocking
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution

private def emptyStream : Execution.Work := .stream { ref := 0, path := [] } []

private def stalled : EventSource (List GraphEvent) :=
  { admissible := fun inputs => inputs = [], finished := fun _ => False }

/-- A stalled source still obeys payload, freshness, and start discipline.
Witness: it admits only the empty prefix; all event obligations are vacuous.
-/
theorem stalled_valid : stalled.ValidFor emptyStream := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro before after earlier accepted
    subst after
    exact List.eq_nil_of_prefix_nil earlier
  · intro inputs accepted
    subst inputs
    exact ⟨.nil, rfl⟩

/-- A valid stalled source need not produce a nonblocking queue, even for an empty stream.
Witness: initial input is admitted but no supplied input can close the live boundary.
The source's own `finished` predicate is not used for concrete queue termination.
-/
theorem stalled_not_nonblocking
    : ¬(createWorkQueueForSchedule emptyStream stalled).Nonblocking := by
  intro nonblocking
  obtain ⟨suffix, inputs, accepted, _, ended⟩ :=
    nonblocking [] ⟨[], rfl, rfl⟩
  change inputs = [] at accepted
  subst inputs
  contradiction

/-- The exposed queue property follows from the checked finite local-continuation lemma.
Witness: apply the general implementation theorem, not the source's finished predicate.
-/
theorem queue_nonblocking {work : Execution.Work}
    {schedule : EventSource (List GraphEvent)} (valid : schedule.ValidFor work)
    (nonblocking : schedule.NonblockingFor work)
    : (createWorkQueueForSchedule work schedule).Nonblocking :=
  createWorkQueueForSchedule_nonblocking valid nonblocking

/-- The public nonblocking proposition has its advertised implementation witness.
Witness: the proved finite-source transfer, without adding nonblocking to conformance.
-/
theorem public_nonblocking : ImplementationNonblocking := implementationNonblocking_holds

#print axioms ValidGraphEvents.length_le_budget
#print axioms admittedInputs_canFinish
#print axioms createWorkQueueForSchedule_nonblocking
#print axioms implementationNonblocking_holds
#print axioms ExecutedWork.runNormalized_rootGroupsHealthy

end GraphQL.IncrementalDelivery.Tests.ImplementationNonblocking
