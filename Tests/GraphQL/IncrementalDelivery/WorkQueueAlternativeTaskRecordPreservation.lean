import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.DispatchResourceInvariant
import Tests.GraphQL.IncrementalDelivery.Fixtures.RejectedTaskCleanup

open GraphQL.IncrementalDelivery.Tests

/-! Universal existing/incoming lease roots, and why completed buffers are not task leases. -/

namespace AlternativeTaskRecordPreservationChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedRepresentedUnsettledTaskProgress :=
  GeneratedRepresentedUnsettledTaskProgress_holds

example : GeneratedDispatchExistingTaskRepresentation :=
  GeneratedDispatchExistingTaskRepresentation_holds

example : GeneratedDispatchTasksPendingRepresented :=
  GeneratedDispatchTasksPendingRepresented_holds

example : GeneratedDispatchResourcesRepresented :=
  GeneratedDispatchResourcesRepresented_holds

private abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized
    [[SharedOwnerFailure.parentSuccess]]).1

private def stale : ResourceState :=
  fun target =>
    if target = .task RejectedTaskCleanup.producer then .owned .queue else .unacquired

-- A completed producer remains buffered under its other owner. That is not a pending lease.
example : RecordTargetRepresented before.queue (.task RejectedTaskCleanup.producer) := by
  cases found : before.queue.groupNode? SharedOwnerFailure.groupH.ref with
  | none =>
      have live : (before.queue.groupNode? SharedOwnerFailure.groupH.ref).isSome = true := by
        unfold before
        rw [SharedOwnerFailure.work_shape]
        cbv
      rw [found] at live
      cases live
  | some group =>
      apply RecordTargetRepresented.task found ?_
        (by
          unfold before
          rw [SharedOwnerFailure.work_shape]
          cbv)
      have allLinked : before.queue.groupNodes.all
          (fun group => group.group.node.ref != SharedOwnerFailure.groupH.ref
            || group.tasks.contains RejectedTaskCleanup.producer) = true := by
        unfold before
        rw [SharedOwnerFailure.work_shape]
        cbv
      have tested := List.all_eq_true.mp allLinked _ (List.mem_of_find?_eq_some found)
      rw [ReferenceWorkQueue.State.groupNode?_ref found] at tested
      simpa using tested

example
    : ¬TasksPendingRepresented before.queue
        (ReferenceWorkQueue.GraphEvent.taskSettlements [SharedOwnerFailure.parentSuccess])
        stale := by
  intro invariant
  have unfinished := (invariant RejectedTaskCleanup.producer (by simp [stale])).2
  apply unfinished
  simp [ReferenceWorkQueue.GraphEvent.taskSettlements, ReferenceWorkQueue.GraphEvent.groupSuccesses,
    ReferenceWorkQueue.GraphEvent.groupFailures, SharedOwnerFailure.parentSuccess,
    RejectedTaskCleanup.producer]

-- The real completion observer releases that computation rather than aborting its buffer.
example
    : (stale.observeNormalCompletion before.queue SharedOwnerFailure.parentSuccess).1
        (.task RejectedTaskCleanup.producer)
      = .released := by
  exact stale.finishQueueTarget_owned (.task RejectedTaskCleanup.producer)
    (by simp [stale])

#print axioms registrationSnapshot_unsettledTask_progress
#print axioms GeneratedRepresentedUnsettledTaskProgress_holds
#print axioms GeneratedDispatchExistingTaskRepresentation_holds
#print axioms GeneratedDispatchTasksPendingRepresented_holds
#print axioms GeneratedDispatchResourcesRepresented_holds
#print axioms generatedDispatch_resourceReplay_and_records

end AlternativeTaskRecordPreservationChecks
