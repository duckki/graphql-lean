import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames
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
    {work inputs earlier batch later fifo after occurrence errors task ref}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (split : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ .taskFailure occurrence errors :: after)
    (found
      : (((State.initialize (Work.fromExecution work)).replayBatches
            earlier).replayGraphEvents
          fifo (GraphEvent.availableFailures batch)).taskNode?
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
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frames := generated.uncancelledFrames_atBatchEvent canonical valid started earlier batch
    later fifo (.taskFailure occurrence errors) after split batchEq
  have metadata := frames.2.2.1.tasks
  have originalRegistered := metadata.registered task (List.mem_of_find?_eq_some found)
  have original := metadata.matching task.task originalRegistered
  obtain ⟨⟨address, payload, producer, identity, known⟩, exactGroups⟩ := original
  have occurrenceEq := (State.taskNode?_some found).2
  rw [occurrenceEq] at known exactGroups
  have failureMember : GraphEvent.taskFailure occurrence errors ∈ inputs.flatten := by
    rw [split, List.flatten_append, List.flatten_cons, batchEq]
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _
      List.mem_cons_self))
  have recorded : occurrence ∈ GraphEvent.failureSettlements inputs.flatten := by
    apply List.mem_reverse.mpr
    exact List.mem_flatMap.mpr ⟨.taskFailure occurrence errors, failureMember, List.mem_cons_self⟩
  obtain ⟨actualTask, registered, sameOccurrence⟩ :=
    generated.runNormalized_failedTasksRegistered inputs valid started occurrence recorded
  have ledger := generated.runNormalized_pendingLedger inputs valid started
  have actual := ledger.matching actualTask registered
  have actualGroups := actual.2
  rw [sameOccurrence] at actualGroups
  have sameGroups : actualTask.groups = task.task.groups :=
    Option.some.inj (actualGroups.symm.trans exactGroups)
  have finalRegistered : ref ∈ ((initial.runNormalized inputs).1).registeredGroups :=
    ledger.taskGroups actualTask registered ref (sameGroups.symm ▸ owner)
  have failed := (generated.runNormalized_failureInventories_groupInvalidated_iff
    inputs valid started ref).mp (GroupInvalidated.task ⟨producer, payload, known⟩ owner recorded)
  obtain ⟨group, dependencies, descriptor, sameRef⟩ :=
    TaskAt.executionGroup_owner (occurrenceEq.symm.trans identity ▸ known) owner
  have health := (generated.runNormalized_retiredHealth inputs valid started).1
  apply Classical.byContradiction
  intro uncancelled
  exact health group dependencies (groupRecordAt_of_nodeAt descriptor)
    (.of_lookup_none (sameRef.symm ▸ finalRegistered) (sameRef.symm ▸ absent))
    (sameRef.symm ▸ uncancelled) (sameRef.symm ▸ failed.toRecordInvalidated)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
