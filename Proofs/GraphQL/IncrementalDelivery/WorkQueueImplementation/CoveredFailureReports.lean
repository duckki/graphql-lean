import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OldRootCoverage

/-! A covered contributor's retained failure must become observable at termination. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An earlier covered group with a retained failure has a positive terminal report.
Witness: continuation preserves old root paths, so terminal root exhaustion excludes a
final live cache. Cache persistence forces a cancellation marker, and concrete replay
supplies its exact same-group or ancestor completion. No terminal law is assumed.
-/
theorem terminal_coveredFailure_reported {work inputs before after} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (splitInputs : inputs.flatten = before ++ after)
    (ended : ((initialQueue work).runNormalized inputs).1.terminated = true)
    {group dependencies} (record : GroupRecordAt work group dependencies)
    (covered
      : ∃ root ∈ ((initialQueue work).replayGraphEvents before).rootGroups,
          ((initialQueue work).replayGraphEvents before).LiveDescendant root group.ref)
    (retained : ((initialQueue work).replayGraphEvents before).FailureRetained group.ref)
    : GroupFailureReported w.events group dependencies := by
  have absent := generated.terminal_oldRootCovered_absent valid started splitInputs ended covered
  have continued := retained.rawEventReplay
    (State.GroupRefsUnique.replayGraphEvents (createWorkQueue_groupRefsUnique _) before) after
  have full : ((initialQueue work).rawEventReplay inputs.flatten).1.FailureRetained
      group.ref := by
    rw [splitInputs, State.rawEventReplay_append]
    simpa only [State.rawEventReplay_state] using continued
  rw [State.rawEventReplay_state] at full
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  have final : ((initialQueue work).runNormalized inputs).1.FailureRetained group.ref := by
    rw [same]
    exact full
  have cancelled := final.cancelled_of_absent
    (createWorkQueue_runNormalized_groupRefsUnique _ inputs) absent
  have reported := generated.runNormalized_cancelledRecordsReported inputs valid started
    group dependencies record cancelled
  rwa [← history] at reported

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
    (distinct : (task.task.groups.map Execution.DeliveryNode.ref).Nodup)
    (accepted
      : ((initialQueue work).replayGraphEvents before).taskHasHealthyOwner task.task
        = true)
    (contributes : group.ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (covered
      : ∃ root ∈ ((initialQueue work).replayGraphEvents before).rootGroups,
          ((initialQueue work).replayGraphEvents before).LiveDescendant root group.ref)
    : GroupFailureReported w.events group dependencies := by
  have absent := generated.terminal_oldRootCovered_absent valid started splitInputs ended covered
  obtain ⟨_, _, path⟩ := covered
  have retained := State.taskFailure_contributorRetained (errors := errors) found distinct accepted contributes
    path.target_present
  have continued := retained.rawEventReplay
    ((State.GroupRefsUnique.replayGraphEvents (createWorkQueue_groupRefsUnique _) before).taskFailure
      occurrence errors) after
  have full : ((initialQueue work).rawEventReplay inputs.flatten).1.FailureRetained
      group.ref := by
    rw [splitInputs, State.rawEventReplay_append]
    dsimp only
    rw [State.rawEventReplay_cons]
    simpa only [State.rawEventReplay_state, State.handleGraphEvent] using continued
  rw [State.rawEventReplay_state] at full
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  have final : ((initialQueue work).runNormalized inputs).1.FailureRetained group.ref := by
    rw [same]
    exact full
  have cancelled := final.cancelled_of_absent
    (createWorkQueue_runNormalized_groupRefsUnique _ inputs) absent
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
    (accepted
      : ((initialQueue work).replayGraphEvents before).taskHasHealthyOwner task.task
        = true)
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
  obtain ⟨⟨address, payload, producer, identity, known⟩, _⟩ :=
    ledger.pending.matching task.task registered
  have distinct : (task.task.groups.map Execution.DeliveryNode.ref).Nodup := by
    exact generated.taskOwners_nodup known
  have covered := generated.replayGraphEvents_healthyContributorsCovered before beforeValid
    beforeStarted task.task registered group.ref contributes healthy live
  exact terminal_acceptedCoveredContributor_reported generated valid started history
    splitInputs ended record found distinct accepted contributes covered

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
