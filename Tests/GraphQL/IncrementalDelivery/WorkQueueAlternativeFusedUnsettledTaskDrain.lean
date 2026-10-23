import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedUnsettledTaskDrain

/-! Unstarted tasks require pending/membership accounting, not a fabricated computation node. -/

namespace AlternativeFusedUnsettledDrainChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : FusedUnsettledDrainProgress := FusedUnsettledDrainProgress_holds

private def group : Execution.DeliveryNode := { ref := 0, path := [] }

private def task : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [0], groups := [group] }

private def unstarted : State :=
  {
    queue :=
      {
        rootGroups := [0]
        groupNodes :=
          [{ group := ⟨group, none⟩, tasks := [task.occurrence], pending := 1 }]
        tasks := [task]
      }
  }

-- An unfinished membership blocks success; cached rejection at startup removes its owner.
example : (unstarted.drainReadyGroups).2.1 = [] := by cbv
example : (unstarted.drainReadyGroups).2.2.1 = [] := by cbv

private def failed : State :=
  {
    unstarted with
      queue :=
        {
          unstarted.queue with
            groupNodes :=
              [{
                group := ⟨group, none⟩,
                tasks := [task.occurrence, .executionGroup [1]],
                pending := 1
              }]
            tasks := task :: [{ occurrence := .executionGroup [1], groups := [group] }]
            taskNodes :=
              [{
                task := { occurrence := .executionGroup [1], groups := [group] }
                rejection := some 1
              }]
        }
  }

example : (failed.startGroup 0).2.1 = [.task task.occurrence] := by cbv

example : (failed.startGroup 0).2.2 = [⟨group, 1⟩] := by cbv

-- Ready draining waits for notifications; startup performs cached-failure inspection.
example : (failed.drainReadyGroups).2.2.1 = [] := by cbv

#print axioms FusedUnsettledDrainProgress_holds
#print axioms drain_unsettledTask

end AlternativeFusedUnsettledDrainChecks
