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

-- An unfinished membership blocks success; failure removes it with a real abort target.
example : (unstarted.drainReadyGroups).2.1 = [] := by cbv
example : (unstarted.drainReadyGroups).2.2 = [] := by cbv

private def failed : State :=
  {
    unstarted with
      queue :=
        {
          unstarted.queue with
            groupNodes :=
              [{
                group := ⟨group, none⟩,
                tasks := [task.occurrence],
                pending := 1,
                failure := some 1
              }]
        }
  }

example : (failed.drainReadyGroups).2.2 = [.task task.occurrence] := by cbv

#print axioms FusedUnsettledDrainProgress_holds
#print axioms drain_unsettledTask

end AlternativeFusedUnsettledDrainChecks
