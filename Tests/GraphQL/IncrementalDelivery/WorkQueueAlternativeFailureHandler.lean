import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FailureHandlerPruning
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeFailureHandlerChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement
open WorkQueueSemantics (Occurrence)

example : GeneratedTaskFailureDisposal := GeneratedTaskFailureDisposal_holds

private def activePrefix : List (List GraphEvent) :=
  [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work
        (activePrefix.flatten ++ [SharedOwnerFailure.failureG]) :=
  SharedOwnerFailure.valid_events.prefix ⟨[SharedOwnerFailure.failureH], rfl⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work activePrefix = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

private abbrev before :=
  ((State.initialize SharedOwnerFailure.work).runNormalized activePrefix).1

private abbrev reduced :=
  ({ state := before } : GraphBatchResult).handleGraphEvent SharedOwnerFailure.failureG

private abbrev observed :=
  SharedOwnerFailure.leases.observeHandlerCleanup before SharedOwnerFailure.failureG

private def buffered : ReferenceWorkQueue.TaskNode :=
  {
    task :=
      {
        occurrence := SharedOwnerFailure.heldProducer,
        groups := [SharedOwnerFailure.groupG]
      },
    value :=
      some
        {
          deliveryGroups := [SharedOwnerFailure.groupG],
          path := [.field "box"],
          data := [("values", .list [])]
        },
    childStreams := [2]
  }

private theorem owned
    : ∃ owner ∈ buffered.task.groups,
        ∃ group, before.queue.groupNode? owner.ref = some group := by
  refine ⟨SharedOwnerFailure.groupG, List.mem_cons_self, ?_⟩
  have present : (before.queue.groupNode? SharedOwnerFailure.groupG.ref).isSome = true := by cbv
  cases lookup : before.queue.groupNode? SharedOwnerFailure.groupG.ref with
  | none => simp [lookup] at present
  | some group => exact ⟨group, rfl⟩

private theorem source_disposal
    : .cancelSource 2 ∈ reduced.effects
      ∧ observed.1 (.stream 2) = .cleanupRequested .queue := by
  have covered := GeneratedTaskFailureDisposal_holds _ _ _ _ SharedOwnerFailure.executed valid started
    SharedOwnerFailure.leases
  have dropped := covered.2 SharedOwnerFailure.heldProducer buffered 2 (by cbv) rfl owned
    (by decide) (by cbv)
  exact ⟨dropped.1, dropped.2 SharedOwnerFailure.source_owned⟩

example : .cancelSource 2 ∈ reduced.effects := source_disposal.1
example : observed.1 (.stream 2) = .cleanupRequested .queue := source_disposal.2

example
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer),
            .adopt SharedOwnerFailure.heldProducer [.stream 2]
          ]
          ++ observed.2) observed.1 :=
  SharedOwnerFailure.handoff.append
    (GeneratedTaskFailureDisposal_holds _ _ _ _ SharedOwnerFailure.executed valid started
      SharedOwnerFailure.leases).1

-----------------------------------------------------------------------------------------
-- One event removes both shared contributors; either root by itself would retain the task
-----------------------------------------------------------------------------------------

private def group0 : Execution.DeliveryNode := { ref := 0, path := [] }
private def group1 : Execution.DeliveryNode := { ref := 1, path := [] }
private def failed : Occurrence := .executionGroup [0]
private def producer : Occurrence := .executionGroup [1]

private def bufferTask : ReferenceWorkQueue.Task :=
  { occurrence := producer, groups := [group0, group1] }

private def node : ReferenceWorkQueue.TaskNode :=
  {
    task := bufferTask,
    value := some { deliveryGroups := [group0, group1], path := [], data := [] },
    childStreams := [7]
  }

private def shared : ReferenceWorkQueue.State :=
  {
    rootGroups := [0, 1],
    groupNodes :=
      [
        { group := ⟨group0, none⟩, tasks := [failed, producer] },
        { group := ⟨group1, none⟩, tasks := [failed, producer] }
      ],
    tasks := [{ occurrence := failed, groups := [group0, group1] }, bufferTask],
    taskNodes := [{ task := { occurrence := failed, groups := [group0, group1] } }, node]
  }

example : (({ queue := shared } : State).removeGroup 0).2 = [] := by
  cbv

example : (({ queue := shared } : State).removeGroup 1).2 = [] := by
  cbv

example
    : (shared.taskFailure failed 1).2
      = [.groupFailure group0 1, .groupFailure group1 1] := by cbv

-- The actual full-handler theorem, not separate single-root results, proves disposal.
example : .cancelSource 7 ∈ (({ queue := shared } : State).taskFailure failed 1).2.2 := by
  apply taskFailure_droppedBufferedSource (occurrence := producer) (node := node) _ failed
    1 (by decide) (by cbv) (by decide) (by cbv)

#print axioms GeneratedTaskFailureDisposal_holds
#print axioms taskFailure_droppedBufferedSource
#print axioms failureFold_outside_survives
#print axioms generatedReplay_bufferedSource

end AlternativeFailureHandlerChecks
