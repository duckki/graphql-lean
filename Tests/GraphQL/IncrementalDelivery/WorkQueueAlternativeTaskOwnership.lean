import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PruningTaskOwnership
import Tests.GraphQL.IncrementalDelivery.Fixtures.SharedOwnerFailure

open GraphQL.IncrementalDelivery.Tests

namespace AlternativeTaskOwnershipChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

-- Exact generated construction: no caller-supplied catalogue, membership, or forest law.
example : GeneratedPruningBufferedCoverage := GeneratedPruningBufferedCoverage_holds

private def activePrefix : List (List GraphEvent) :=
  [[SharedOwnerFailure.parentSuccess], [SharedOwnerFailure.success]]

private theorem valid
    : ReferenceWorkQueue.ValidGraphEvents SharedOwnerFailure.work activePrefix.flatten :=
  SharedOwnerFailure.valid_events.prefix
    ⟨[SharedOwnerFailure.failureG, SharedOwnerFailure.failureH], rfl⟩

private theorem started
    : ReferenceWorkQueue.inputsStarted SharedOwnerFailure.work activePrefix = true := by
  rw [SharedOwnerFailure.work_shape]
  cbv

private abbrev queue :=
  ((State.initialize SharedOwnerFailure.work).runNormalized activePrefix).1.queue

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

private theorem found
    : queue.taskNode? SharedOwnerFailure.heldProducer = some buffered := by
  cbv

private theorem owned
    : ∃ owner ∈ buffered.task.groups,
        ∃ group, queue.groupNode? owner.ref = some group := by
  refine ⟨SharedOwnerFailure.groupG, List.mem_cons_self, ?_⟩
  have present : (queue.groupNode? SharedOwnerFailure.groupG.ref).isSome = true := by cbv
  cases lookup : queue.groupNode? SharedOwnerFailure.groupG.ref with
  | none => simp [lookup] at present
  | some group => exact ⟨group, rfl⟩

-- The reference really drops this buffer; the universal trace proof finds its source.
private theorem dropped
    : (queue.removeGroup 0).taskNode? SharedOwnerFailure.heldProducer = none := by
  cbv

private theorem generated_target
    : .stream 2 ∈ (({ queue := queue } : State).removeGroup 0).2 := by
  obtain ⟨final, targets, trace, same, covers⟩ :=
    GeneratedPruningBufferedCoverage_holds _ _ SharedOwnerFailure.executed valid started 0
  rw [same, mem_uniqueCleanupTargets]
  exact covers _ buffered 2 found (by rfl) owned (by decide) dropped

example
    : (SharedOwnerFailure.leases.requestQueueCleanup
        ((({ queue := queue } : State).removeGroup 0).2)).1
        (.stream 2)
      = .cleanupRequested .queue :=
  SharedOwnerFailure.leases.requestQueueCleanup_owned _ _ generated_target
    SharedOwnerFailure.source_owned

-- One compatible acquisition/adoption/request history, not independent existential traces.
example
    : ResourceReplay ResourceState.empty
        ([
            .acquire (.stream 2) (.producer SharedOwnerFailure.heldProducer),
            .adopt SharedOwnerFailure.heldProducer [.stream 2]
          ]
          ++ (SharedOwnerFailure.leases.requestQueueCleanup
                ((({ queue := queue } : State).removeGroup 0).2)).2)
        (SharedOwnerFailure.leases.requestQueueCleanup
          ((({ queue := queue } : State).removeGroup 0).2)).1 :=
  SharedOwnerFailure.handoff.append
    (SharedOwnerFailure.leases.requestQueueCleanup_replay _)

-----------------------------------------------------------------------------------------
-- Raw counterexamples delimit the structural leaves; none is a generated-work bug
-----------------------------------------------------------------------------------------

private def group0 : Execution.DeliveryNode := { ref := 0, path := [] }
private def group1 : Execution.DeliveryNode := { ref := 1, path := [] }

private def task : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [0], groups := [group0] }

private def rawBuffer : ReferenceWorkQueue.TaskNode :=
  {
    task,
    value := some { deliveryGroups := [group0], path := [], data := [] },
    childStreams := [7]
  }

-- Without live ownership, an orphan does not occur in any traversed group membership.
private def orphan : ReferenceWorkQueue.State :=
  { tasks := [task], taskNodes := [rawBuffer] }

example : (orphan.removeGroup 0).taskNode? task.occurrence = none := by cbv

example : (({ queue := orphan } : State).removeGroup 0).2 = [] := by
  cbv

-- A live owner alone is insufficient if the buffered occurrence lacks its membership link.
private def unlinked : ReferenceWorkQueue.State :=
  { orphan with groupNodes := [{ group := ⟨group0, none⟩ }] }

example : (unlinked.removeGroup 0).taskNode? task.occurrence = none := by cbv

example : (({ queue := unlinked } : State).removeGroup 0).2 = [] := by cbv

example : ¬unlinked.StoredTaskLinks := by
  intro links
  have impossible := links rawBuffer List.mem_cons_self rfl
    { group := ⟨group0, none⟩ } List.mem_cons_self (List.mem_cons_self (a := 0))
  cases impossible

-- A stale catalogue co-owner can defeat the actual guard despite correct buffered links.
private def mismatched : ReferenceWorkQueue.State :=
  {
    orphan with
      tasks := [{ task with groups := [group0, group1] }],
      groupNodes :=
        [
          { group := ⟨group0, none⟩, tasks := [task.occurrence] },
          { group := ⟨group1, none⟩ }
        ]
  }

example : (mismatched.removeGroup 0).taskNode? task.occurrence = none := by cbv

example : (({ queue := mismatched } : State).removeGroup 0).2 = [] := by cbv

#print axioms GeneratedPruningBufferedCoverage_holds
#print axioms generatedReplay_taskInvariants
#print axioms canonicalTaskCatalogue
#print axioms PruningGroups.retainedHasOwner
#print axioms PruningGroups.removedBufferedSource

end AlternativeTaskOwnershipChecks
