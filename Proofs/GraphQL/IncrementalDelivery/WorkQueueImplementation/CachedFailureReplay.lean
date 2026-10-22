import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CachedFailurePersistence
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RetiredHealthReplay

/-! Actual source rejection cannot retire an owning ref successfully.
Generated retirement health replaces the obsolete arbitrary-state cache persistence law.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An owning ref absent after a valid source rejection has a cancellation marker.
Witness: source matching identifies its fixed owner; permanent registration survives the
continuation. The recorded rejection invalidates that ref, contradicting uncancelled
successful retirement in generated replay.
-/
theorem ExecutedWork.runNormalized_failedContributor_cancelled_of_absent
    {work inputs before after occurrence errors task ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (split : inputs.flatten = before ++ .taskFailure occurrence errors :: after)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some task)
    (owner : ref ∈ task.task.groups.map Execution.DeliveryNode.ref)
    (absent
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.groupNode?
          ref
        = none)
    : ref
      ∈ ((State.initialize (Work.fromExecution work)).runNormalized
          inputs).1.cancelledGroups := by
  let initial := State.initialize (Work.fromExecution work)
  have accepted := initial.batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have beforeStarted : initial.acceptsBatch before = true := by
    apply State.acceptsBatch_prefix (after := .taskFailure occurrence errors :: after)
    rwa [← split]
  have beforeValid := valid.prefix (show before.IsPrefix inputs.flatten from ⟨_, split.symm⟩)
  have ledger := (createWorkQueue_pendingAccounting work).replayGraphEvents_successes
    (before := []) generated before beforeValid beforeStarted
  have registered := ledger.started task (List.mem_of_find?_eq_some found)
  obtain ⟨⟨address, payload, producer, identity, known⟩, _⟩ := ledger.matching task.task registered
  have occurrenceEq := (State.taskNode?_some found).2
  rw [occurrenceEq] at known
  have failureMember : GraphEvent.taskFailure occurrence errors ∈ inputs.flatten := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have recorded : occurrence ∈ GraphEvent.failureSettlements inputs.flatten := by
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure occurrence errors, failureMember, List.mem_cons_self⟩
  have failed := (generated.runNormalized_failureInventories_groupInvalidated_iff
    inputs valid started ref).mp (GroupInvalidated.task ⟨producer, payload, known⟩ owner recorded)
  have priorRegistered : ref ∈ (initial.replayGraphEvents before).registeredGroups :=
    ledger.taskGroups task.task registered ref owner
  have continued := State.replayGraphEvents_registration ledger.liveGroups ledger.taskGroups
    (.taskFailure occurrence errors :: after) (fun event member => valid.eachMatches (by
      rw [split]
      exact List.mem_append_right _ member))
  have finalRegistered : ref ∈ ((initial.runNormalized inputs).1).registeredGroups := by
    obtain ⟨terminal, same⟩ := createWorkQueue_runNormalized_stateCore started
    rw [same]
    change ref ∈ (initial.replayGraphEvents inputs.flatten).registeredGroups
    rw [split, State.replayGraphEvents, List.foldl_append]
    exact continued.2.2 priorRegistered
  obtain ⟨group, dependencies, descriptor, sameRef⟩ :=
    TaskAt.executionGroup_owner (occurrenceEq.symm.trans identity ▸ known) owner
  have health := (generated.runNormalized_retiredHealth inputs valid started).1
  apply Classical.byContradiction
  intro uncancelled
  exact health group dependencies (groupRecordAt_of_nodeAt descriptor)
    (.of_lookup_none (sameRef.symm ▸ finalRegistered) (sameRef.symm ▸ absent))
    (sameRef.symm ▸ uncancelled) (sameRef.symm ▸ failed.toRecordInvalidated)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
