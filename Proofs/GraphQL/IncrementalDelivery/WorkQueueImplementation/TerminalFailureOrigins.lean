import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureOriginReporting

/-! Actual accepted object-failure invalidations have observable terminal report origins. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every record invalidated by actual accepted host batches has a positive terminal report.
Unconditional contributor retirement accounts for each consumed failing owner. Its real
cancellation report propagates through canonical full ancestry to the selected record. -/
theorem terminal_invalidatedRecord_reported {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    (invalid
      : GroupRecordInvalidated work
          ((initialQueue work).admittedObjectFailureContributionsForBatches inputs)
          node.ref)
    : GroupFailureReported w.events node dependencies := by
  rw [State.admittedObjectFailureContributionsForBatches_eq_of_started _ inputs
    (by rwa [inputsStarted_eq_batchesStarted] at started)] at invalid
  obtain ⟨cause, owners, owner, taskKnown, failed, contributes, inChain⟩ :=
    (generated.groupRecordInvalidated_iff known).mp invalid
  obtain ⟨producer, payload, structural⟩ := taskKnown
  cases cause with
  | executionGroup address =>
      obtain ⟨group, ancestors, ownerKnown, sameRef⟩ := structural.executionGroup_owner contributes
      have report := terminal_failedContributor_reported generated valid started history ended
        ⟨producer, payload, structural⟩ (sameRef.symm ▸ contributes) failed
        (groupRecordAt_of_nodeAt ownerKnown)
      exact report.inherit_chain generated (groupRecordAt_of_nodeAt ownerKnown) known
        (sameRef.symm ▸ inChain)
  | item address ordinal =>
      obtain ⟨_, _, _, _, impossible⟩ := valid.failureSettlements_known _ failed
      obtain ⟨_, _, _, _, _, _, _, _, payloadEq⟩ := impossible
      cases payloadEq

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
