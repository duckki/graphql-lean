import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CoveredFailureReports
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureSettlements

/-! Healthy retirement excludes a matching failure in the empty-snapshot eventwise domain. -/

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
    (started
      : State.eventsStarted [] (State.initialize (Work.fromExecution work)) before = true)
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
    apply State.eventsStarted_atPrefix _ past next after
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
