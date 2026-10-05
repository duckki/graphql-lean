import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyFailureOwners

/-! Earlier or newly accepted group-failure origins report their full defer ancestry. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A reported ref in a record's full chain reports that record as well.
Witness: equal refs have canonical equal dependency lists; strict ancestors use generated
transitivity. The record itself may be taskless or unannounced.
-/
theorem GroupFailureReported.inherit_chain {work events owner ancestors node dependencies}
    (reported : GroupFailureReported events owner ancestors)
    (generated : ExecutedWork work) (ownerKnown : GroupRecordAt work owner ancestors)
    (known : GroupRecordAt work node dependencies)
    (inChain : owner.ref ∈ node.ref :: dependencies)
    : GroupFailureReported events node dependencies := by
  rcases List.mem_cons.mp inChain with equal | above
  · obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
    have same : ancestors = dependencies := by
      rw [canonical owner ancestors ownerKnown, canonical node dependencies known, equal]
    obtain ⟨reporter, errors, positive, member, relation⟩ := reported
    exact ⟨reporter, errors, positive, member, by simpa only [equal, same] using relation⟩
  · exact reported.inherit generated known ownerKnown above

namespace ConformancePlan

/-- One accepted failure extends report coverage from earlier record invalidations.
Witness: an old cause reuses its earlier report. A new contributing cause either was
already invalidated, or was healthy and is reported by concrete terminal exhaustion.
Canonical full ancestry propagates that contributor's report to the selected record.
The earlier-report hypothesis is a proof induction step, not a source or contract premise.
-/
theorem terminal_acceptedFailure_reportsRecords
    {work inputs before after occurrence errors task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (splitInputs : inputs.flatten = before ++ .taskFailure occurrence errors :: after)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    (found
      : ((initialQueue work).replayGraphEvents before).taskNode? occurrence = some task)
    (accepted
      : ((initialQueue work).replayGraphEvents before).taskHasHealthyOwner task.task
        = true)
    (earlier
      : ∀ node dependencies,
          GroupRecordAt work node dependencies
          → GroupRecordInvalidated work
              ((initialQueue work).objectFailureContributions before) node.ref
          → GroupFailureReported w.events node dependencies)
    {node dependencies} (known : GroupRecordAt work node dependencies)
    (invalid
      : GroupRecordInvalidated work
          (occurrence :: (initialQueue work).objectFailureContributions before) node.ref)
    : GroupFailureReported w.events node dependencies := by
  obtain ⟨cause, owners, owner, taskKnown, failed, contributes, inChain⟩ :=
    (generated.groupRecordInvalidated_iff known).mp invalid
  rcases List.mem_cons.mp failed with current | past
  · subst cause
    obtain ⟨producer, payload, structural⟩ := taskKnown
    cases occurrence with
    | item address index =>
        have matched := valid.eachMatches
          (splitInputs ▸ List.mem_append_right before List.mem_cons_self)
        obtain ⟨otherOwners, otherProducer, path, failed⟩ := matched
        obtain ⟨stream, entries, enclosing, result, children, located, entry,
          sameOwners, impossible⟩ := failed
        cases impossible
    | executionGroup address =>
        obtain ⟨group, ancestors, ownerKnown, sameRef⟩ :=
          structural.executionGroup_owner contributes
        have beforeValid := valid.prefix ⟨.taskFailure (.executionGroup address) errors :: after,
          splitInputs.symm⟩
        have accepts := (initialQueue work).batchesStarted_acceptsBatch inputs
          (by rwa [← inputsStarted_eq_batchesStarted])
        have beforeStarted : (initialQueue work).acceptsBatch before = true := by
          apply State.acceptsBatch_prefix
            (after := .taskFailure (.executionGroup address) errors :: after)
          rwa [← splitInputs]
        obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
        have acceptedAt : ∀ past next, (past ++ [next]).IsPrefix before →
            ((initialQueue work).replayGraphEvents past).acceptsGraphEvent next = true := by
          intro past next prefixBefore
          obtain ⟨later, equal⟩ := prefixBefore
          apply State.acceptsBatch_atPrefix _ past next later
          simpa only [← equal, List.append_assoc, List.singleton_append] using beforeStarted
        have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical
          beforeValid acceptedAt
        have registered := ledger.pending.started task (List.mem_of_find?_eq_some found)
        obtain ⟨⟨otherAddress, otherPayload, otherProducer, identity, otherKnown⟩, _⟩ :=
          ledger.pending.matching task.task registered
        have occurrenceEq := (State.taskNode?_some found).2
        rw [occurrenceEq] at otherKnown
        have ownersEq := (structural.unique otherKnown).1
        have actualContributes : group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref :=
          ownersEq ▸ (sameRef.symm ▸ contributes)
        classical
        have reported : GroupFailureReported w.events group ancestors := by
          by_cases prior : GroupInvalidated work
              ((initialQueue work).objectFailureContributions before) group.ref
          · exact earlier group ancestors (groupRecordAt_of_nodeAt ownerKnown)
              prior.toRecordInvalidated
          · exact terminal_acceptedHealthyOwner_reported generated valid started history
              splitInputs ended (groupRecordAt_of_nodeAt ownerKnown) found accepted
              actualContributes prior
        exact reported.inherit_chain generated (groupRecordAt_of_nodeAt ownerKnown) known
          (sameRef.symm ▸ inChain)
  · exact earlier node dependencies known
      ((generated.groupRecordInvalidated_iff known).mpr
        ⟨cause, owners, owner, taskKnown, past, contributes, inChain⟩)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
