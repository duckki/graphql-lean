import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.UnsettledTaskProgress
import Tests.GraphQL.IncrementalDelivery.Fixtures.RejectedTaskCleanup

open GraphQL.IncrementalDelivery.Tests

/-! All-handler unsettled-task roots and a generated existing-child failure regression.
The child has been registered by an earlier input but has not completed when G fails.
-/

namespace AlternativeUnsettledTaskProgressChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : GeneratedUnsettledTaskOwnerProgress := GeneratedUnsettledTaskOwnerProgress_holds

example : GeneratedPreparedUnsettledTaskProgress :=
  GeneratedPreparedUnsettledTaskProgress_holds

private theorem failedKnown
    : WorkQueueSemantics.TaskAt SharedOwnerFailure.work (.executionGroup [1, 1, 0]) [0]
        none (.object [] (.error 1)) := by
  refine ⟨[{ node := SharedOwnerFailure.groupG }], [], { result := .error 1, cause := some 1 }, .empty, [], ?_, rfl, rfl⟩
  rw [SharedOwnerFailure.work_shape]
  rfl

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        [SharedOwnerFailure.parentSuccess, SharedOwnerFailure.failureG] := by
  have first := SharedOwnerFailure.valid_events.prefix
    (show [SharedOwnerFailure.parentSuccess].IsPrefix SharedOwnerFailure.inputs.flatten from
      ⟨[SharedOwnerFailure.success, SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩)
  exact .append first SharedOwnerFailure.failureG_matches
    (by
      simp [ReferenceWorkQueue.GraphEvent.Fresh, ReferenceWorkQueue.GraphEvent.identities,
        SharedOwnerFailure.parentSuccess, SharedOwnerFailure.failureG])
    ⟨[0], none, _, failedKnown, by intro producer impossible; cases impossible⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work
        [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.failureG]]
      = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

private abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized
    [[SharedOwnerFailure.parentSuccess]]).1

private abbrev reduced :=
  ({ state := before } : GraphBatchResult).handleGraphEvent SharedOwnerFailure.failureG

private def child : ReferenceWorkQueue.Task :=
  { occurrence := RejectedTaskCleanup.child, groups := [SharedOwnerFailure.groupG] }

private theorem registered
    : child ∈ (registrationSnapshot before.queue SharedOwnerFailure.failureG).tasks := by
  unfold before
  rw [SharedOwnerFailure.work_shape]
  cbv
  repeat first | exact List.mem_cons_self | apply List.mem_cons_of_mem

private theorem pending
    : child.occurrence
      ∉ SharedOwnerFailure.failureG.recordTaskOutcome
          (ReferenceWorkQueue.GraphEvent.taskSettlements
            [SharedOwnerFailure.parentSuccess]) := by
  simp [child, RejectedTaskCleanup.child, SharedOwnerFailure.heldProducer, SharedOwnerFailure.failureG,
    SharedOwnerFailure.parentSuccess, ReferenceWorkQueue.GraphEvent.recordTaskOutcome,
    ReferenceWorkQueue.GraphEvent.taskSettlements, ReferenceWorkQueue.GraphEvent.groupSuccesses,
    ReferenceWorkQueue.GraphEvent.groupFailures]

private theorem owned
    : ∃ owner ∈ child.groups,
        ∃ group,
          (registrationSnapshot before.queue SharedOwnerFailure.failureG).groupNode?
            owner.ref
          = some group := by
  refine ⟨SharedOwnerFailure.groupG, List.mem_cons_self, ?_⟩
  cases found
        : (registrationSnapshot before.queue SharedOwnerFailure.failureG).groupNode?
            SharedOwnerFailure.groupG.ref with
  | some group => exact ⟨group, rfl⟩
  | none =>
      have live : ((registrationSnapshot before.queue SharedOwnerFailure.failureG).groupNode? SharedOwnerFailure.groupG.ref).isSome = true := by
        unfold before
        rw [SharedOwnerFailure.work_shape]
        cbv
      rw [found] at live
      cases live

-- Derive last-owner disposal from the universal root, not an assumed cleanup target.
example : .abortTask child.occurrence ∈ reduced.effects := by
  have progress := GeneratedPreparedUnsettledTaskProgress_holds SharedOwnerFailure.work [[SharedOwnerFailure.parentSuccess]]
    SharedOwnerFailure.failureG SharedOwnerFailure.executed valid started child registered pending owned
  rcases progress with kept | aborted
  · have absent : ¬RecordTargetRepresented reduced.state.queue (.task child.occurrence) := by
      intro represented
      cases represented with
      | task found member =>
          have excludes : reduced.state.queue.groupNodes.all
              (fun group => !group.tasks.contains child.occurrence) = true := by
            unfold reduced before
            rw [SharedOwnerFailure.work_shape]
            cbv
          have absent := List.all_eq_true.mp excludes _ (List.mem_of_find?_eq_some found)
          rw [List.contains_iff_mem.mpr member] at absent
          cases absent
    exact False.elim (absent kept)
  · exact aborted

#print axioms GeneratedUnsettledTaskOwnerProgress_holds
#print axioms handleGraphEvent_tasks_eq_snapshot
#print axioms generatedUnsettledTask_unpublished
#print axioms GeneratedPreparedUnsettledTaskProgress_holds
#print axioms generatedPreparedTask_progress

end AlternativeUnsettledTaskProgressChecks
