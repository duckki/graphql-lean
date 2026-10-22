import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActiveRejectionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HealthyCounterReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RootPresenceReplay

/-! Derived queue readiness, separate from any host nonblocking assumption. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Active roots retain exact healthy counters
-----------------------------------------------------------------------------------------

/-- Every active group is uninvalidated by the complete source failure ledger.
Witness: uncached active records have no accepted failed contributor; their ancestors
are healthy by structural retirement. The checked failure-inventory equivalence also
accounts for ignored late failures without requiring identical failure-token lists.
-/
theorem ExecutedWork.runNormalized_rootGroupsHealthy {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.RootGroupsHealthy
        work (GraphEvent.failureSettlements batches.flatten) := by
  let queue := ((State.initialize (Work.fromExecution work)).runNormalized batches).1
  let failed := (State.initialize (Work.fromExecution work)).objectFailureContributions
    batches.flatten
  obtain ⟨_, ledger⟩ := generated.runNormalized_healthyCounterLedger batches valid started
  have clear := createWorkQueue_runNormalized_noActiveCachedFailure
    generated batches valid started
  have ancestry := (generated.runNormalized_retiredHealth batches valid started).2.1
  have counts := generated.runNormalized_retainedFailures batches valid started
  intro ref active invalid
  have accepted : GroupInvalidated work failed ref :=
    (generated.runNormalized_failureInventories_groupInvalidated_iff batches valid started
      ref).mp invalid
  have present := generated.replayGraphEvents_rootsPresent batches.flatten
    (fun _ member => valid.eachMatches member)
  obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
  have rootsPresent : queue.RootGroupsPresent := by
    dsimp only [queue]
    rw [same]
    exact present
  obtain ⟨node, member, nodeRef⟩ := List.mem_map.mp (rootsPresent ref active)
  obtain ⟨dependencies, known⟩ := ledger.groups node member
  have cause := generated.groupRecordInvalidated_causes known
    (nodeRef.symm ▸ accepted.toRecordInvalidated)
  rcases cause with direct | inherited
  · obtain ⟨occurrence, owners, ⟨producer, payload, task⟩, owner, recorded⟩ := direct
    have received := ((State.initialize (Work.fromExecution work)).objectFailureContributions_sublist
      batches.flatten).subset recorded
    obtain ⟨actualOwners, actualProducer, path, errors, actual⟩ :=
      valid.failureSettlements_known occurrence received
    have sameOwners := (task.unique actual).1
    exact counts.uncached_noFailedContributor generated member
      (clear node member (nodeRef.symm ▸ active)) actual (by simp [Payload.failure])
      (sameOwners ▸ owner) recorded
  · obtain ⟨ancestor, included, failure⟩ := inherited
    exact ancestry ref active node.group.node dependencies known nodeRef
      ancestor included failure

/-- Active group pending counts exactly track the remaining source-unsettled memberships.
Witness: the independently proved root-health lemma specializes healthy counter exactness.
This excludes surplus pending debt at host boundaries, but is not yet task-start coverage.
-/
theorem ExecutedWork.runNormalized_activePendingTracks {work : Execution.Work}
    (generated : ExecutedWork work) (batches : List (List GraphEvent))
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : ((State.initialize (Work.fromExecution work)).runNormalized
        batches).1.ActivePendingTracks
        (GraphEvent.taskSettlements batches.flatten) := by
  obtain ⟨_, ledger⟩ := generated.runNormalized_healthyCounterLedger batches valid started
  have healthy := generated.runNormalized_rootGroupsHealthy batches valid started
  intro node member active
  exact ledger.healthy node member (healthy _ active)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
