import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CoveredFailureReports
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureSettlements

/-! A matched failing task cannot have a healthy contributor that already retired. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A started matched failing task's healthy contributor still has a live group record.
Witness: permanent registration makes an absent ref retired. Healthy retirement would
require a task-success source event in the earlier prefix, contradicting that task's
fixed failing payload. No output-admission or terminal premise is used.
-/
theorem ExecutedWork.matchedFailure_healthyContributor_live
    {work before occurrence errors task ref} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch before = true)
    (matching : (GraphEvent.taskFailure occurrence errors).MatchesWork work)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some task)
    (contributes : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (healthy
      : ¬GroupInvalidated work
          ((State.initialize (Work.fromExecution work)).objectFailureContributions before)
          ref)
    : ∃ node,
        ((State.initialize (Work.fromExecution work)).replayGraphEvents before).groupNode?
          ref
        = some node := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have acceptedAt : ∀ past next, (past ++ [next]).IsPrefix before →
      ((State.initialize (Work.fromExecution work)).replayGraphEvents past).acceptsGraphEvent next
        = true := by
    intro past next earlier
    obtain ⟨after, equal⟩ := earlier
    apply State.acceptsBatch_atPrefix _ past next after
    simpa only [← equal, List.append_assoc, List.singleton_append] using started
  have ledger := generated.replayGraphEvents_ownerAccounting_of_eachAccepted canonical
    valid acceptedAt
  have registered := ledger.pending.started task (List.mem_of_find?_eq_some found)
  have taskMatching := ledger.pending.matching task.task registered
  have recordHealthy := taskMatching.contributor_recordHealthy generated contributes healthy
  cases lookup
        : ((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).groupNode?
            ref with
  | some node => exact ⟨node, rfl⟩
  | none =>
      have retired := State.RetiredGroup.of_lookup_none
        (ledger.pending.taskGroups task.task registered ref contributes) lookup
      obtain ⟨result, member⟩ := generated.replayGraphEvents_retiredContributor_succeeded
        valid started registered contributes retired recordHealthy
      have succeeded := valid.eachMatches member
      obtain ⟨owners, producer, path, failed⟩ := matching
      obtain ⟨otherOwners, otherProducer, success, _, _⟩ := succeeded
      have identity := (State.taskNode?_some found).2
      rw [identity] at success
      have same := (success.unique failed).2.2
      cases same

namespace ConformancePlan

/-- A healthy contributor at an accepted failure obtains a positive report by termination.
Witness: source matching excludes prior successful retirement and hence derives live
ownership; generated root coverage, cache persistence, and terminal exhaustion then force
a report. The conclusion does not require an extra live-node or distinct-owner premise.
-/
theorem terminal_acceptedHealthyOwner_reported
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
    : GroupFailureReported w.events group dependencies := by
  have beforeValid := valid.prefix ⟨.taskFailure occurrence errors :: after, splitInputs.symm⟩
  have matched := valid.eachMatches
    (splitInputs ▸ List.mem_append_right before List.mem_cons_self)
  have accepts := (initialQueue work).batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have beforeStarted : (initialQueue work).acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := .taskFailure occurrence errors :: after)
    rwa [← splitInputs]
  exact terminal_acceptedHealthyContributor_reported generated valid started history
    splitInputs ended record found accepted contributes (healthy := healthy)
    (live :=
      generated.matchedFailure_healthyContributor_live beforeValid beforeStarted
        matched found contributes healthy)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
