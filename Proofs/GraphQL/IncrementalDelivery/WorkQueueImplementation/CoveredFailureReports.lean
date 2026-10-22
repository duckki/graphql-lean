import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OldRootCoverage

/-! A covered contributor's retained failure must become observable at termination. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A root-covered contributor of an accepted failure receives a positive terminal report.
Witness: its exact settlement installs a cache or cancellation marker. The earlier path
excludes a final live record even if later health is lost, and report provenance follows
the same concrete replay and normalized witness. `distinct` is generated task metadata.
-/
theorem terminal_acceptedCoveredContributor_reported
    {work inputs before after occurrence errors task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (splitInputs : inputs.flatten = before ++ .taskFailure occurrence errors :: after)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {group dependencies} (record : GroupRecordAt work group dependencies)
    (found
      : ((initialQueue work).replayGraphEvents before).taskNode? occurrence = some task)
    (contributes : group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (covered
      : ∃ root ∈ ((initialQueue work).replayGraphEvents before).rootGroups,
          ((initialQueue work).replayGraphEvents before).LiveDescendant root group.ref)
    : GroupFailureReported w.events group dependencies := by
  have absent := generated.terminal_oldRootCovered_absent valid started splitInputs ended covered
  have cancelled := generated.runNormalized_failedContributor_cancelled_of_absent
    valid started splitInputs found contributes absent
  have reported := generated.runNormalized_cancelledRecordsReported inputs valid started
    group dependencies record cancelled
  rwa [← history] at reported

/-- A previously healthy live contributor of an accepted failure is reported by termination.
Witness: actual started-task registration and generated healthy-contributor coverage derive
the pre-settlement root path; the covered-failure theorem then tracks its cache to a
positive completion. Contributor uniqueness comes from execution, not an extra premise.
-/
theorem terminal_acceptedHealthyContributor_reported
    {work inputs before after occurrence errors task} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (splitInputs : inputs.flatten = before ++ .taskFailure occurrence errors :: after)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {group dependencies} (record : GroupRecordAt work group dependencies)
    (found
      : ((initialQueue work).replayGraphEvents before).taskNode? occurrence = some task)
    (contributes : group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (healthy
      : ¬GroupInvalidated work
          ((initialQueue work).objectFailureContributions before) group.ref)
    (live
      : ∃ node,
          ((initialQueue work).replayGraphEvents before).groupNode? group.ref = some node)
    : GroupFailureReported w.events group dependencies := by
  have prefixInputs : before.IsPrefix inputs.flatten :=
    ⟨.taskFailure occurrence errors :: after, splitInputs.symm⟩
  have beforeValid := valid.prefix prefixInputs
  have accepts := (initialQueue work).batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have beforeStarted : (initialQueue work).acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := .taskFailure occurrence errors :: after)
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
  have covered := generated.replayGraphEvents_healthyContributorsCovered before beforeValid
    beforeStarted task.task registered group.ref contributes healthy live
  exact terminal_acceptedCoveredContributor_reported generated valid started history
    splitInputs ended record found contributes covered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
