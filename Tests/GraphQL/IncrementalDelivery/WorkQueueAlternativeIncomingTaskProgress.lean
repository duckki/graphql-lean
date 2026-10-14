import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IncomingTaskProgress
import Tests.GraphQL.IncrementalDelivery.Fixtures.RejectedTaskCleanup

open GraphQL.IncrementalDelivery.Tests

/-! Universal actual-handler incoming-task progress and independent resource correspondence.
The generated fixture checks both retained and rejected registration schedules.
-/

namespace AlternativeIncomingTaskProgressChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedIncomingTaskOwnerProgress := GeneratedIncomingTaskOwnerProgress_holds
example : GeneratedAdoptedTaskProgress := GeneratedAdoptedTaskProgress_holds

example : GeneratedDispatchIncomingTaskRepresentation :=
  GeneratedDispatchIncomingTaskRepresentation_holds

private theorem firstValid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        [SharedOwnerFailure.parentSuccess] :=
  SharedOwnerFailure.valid_events.prefix
    ⟨
      [
        SharedOwnerFailure.success,
        SharedOwnerFailure.failureG,
        SharedOwnerFailure.failureH
      ],
      rfl
    ⟩

private theorem firstStarted
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work
        [[SharedOwnerFailure.parentSuccess]]
      = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

private abbrev retained :=
  ({ state := State.initialize SharedOwnerFailure.work }
    : GraphBatchResult).handleGraphEvent
    SharedOwnerFailure.parentSuccess

-- The same structural child is retained if its owner has not already failed.
example
    : RecordTargetRepresented retained.state.queue (.task RejectedTaskCleanup.child) := by
  have progress := GeneratedAdoptedTaskProgress_holds SharedOwnerFailure.work [] SharedOwnerFailure.parentSuccess
    SharedOwnerFailure.executed firstValid firstStarted RejectedTaskCleanup.producer
    [1, 0, 0, 0, 1, 0] [0]
    (.object [.field "box"] (.ok ([("values", .list [])], 0)))
    (by rw [SharedOwnerFailure.work_shape]; cbv; exact List.mem_cons_self) RejectedTaskCleanup.childKnown
  rcases progress with kept | aborted
  · exact kept
  · have absent : .abortTask RejectedTaskCleanup.child ∉ retained.effects := by
      unfold retained
      rw [SharedOwnerFailure.work_shape]
      cbv
      intro member
      cases member with
      | tail _ impossible => cases impossible
    exact False.elim (absent aborted)

-- With G already failed, the universal theorem derives the actual abort branch.
example : .abortTask RejectedTaskCleanup.child ∈ RejectedTaskCleanup.reduced.effects := by
  have progress := GeneratedAdoptedTaskProgress_holds SharedOwnerFailure.work [[SharedOwnerFailure.failureG]]
    SharedOwnerFailure.parentSuccess SharedOwnerFailure.executed RejectedTaskCleanup.valid RejectedTaskCleanup.started
    RejectedTaskCleanup.producer [1, 0, 0, 0, 1, 0] [0]
    (.object [.field "box"] (.ok ([("values", .list [])], 0)))
    (by rw [RejectedTaskCleanup.labels]; exact List.mem_cons_self) RejectedTaskCleanup.childKnown
  exact progress.resolve_left RejectedTaskCleanup.unrepresented

#print axioms taskSuccess_registrationDebt
#print axioms successGroupFold_unsettledOwners
#print axioms GeneratedIncomingTaskOwnerProgress_holds
#print axioms generatedIncomingTask_unpublished
#print axioms generatedAcceptedTask_progress
#print axioms GeneratedAdoptedTaskProgress_holds
#print axioms GeneratedDispatchIncomingTaskRepresentation_holds

end AlternativeIncomingTaskProgressChecks
