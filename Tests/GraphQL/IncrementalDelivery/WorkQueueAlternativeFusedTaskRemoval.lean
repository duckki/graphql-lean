import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskRemoval

/-! Last-owner disposal covers tasks with no computation node, not only buffered sources. -/

namespace AlternativeFusedTaskRemovalChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : FusedRemovalTaskProgress := FusedRemovalTaskProgress_holds

private def first : Execution.DeliveryNode := { ref := 0, path := [] }
private def second : Execution.DeliveryNode := { ref := 1, path := [] }

private def task : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [0], groups := [first, second] }

private def unstarted : State :=
  {
    queue :=
      {
        rootGroups := [0, 1]
        groupNodes :=
          [
            { group := ⟨first, none⟩, tasks := [task.occurrence] },
            { group := ⟨second, none⟩, tasks := [task.occurrence] }
          ]
        tasks := [task]
      }
  }

example : unstarted.queue.taskNode? task.occurrence = none := by cbv
example : (unstarted.removeGroup 0).2 = [] := by cbv
example : ((unstarted.removeGroup 0).1.queue.groupNode? 1).isSome = true := by cbv

example : ((unstarted.removeGroup 0).1.removeGroup 1).2 = [.task task.occurrence] := by
  cbv

example : (unstarted.removeGroup 9).2 = [] := by cbv

#print axioms FusedRemovalTaskProgress_holds
#print axioms PruningGroups.linkedOnOrAbort
#print axioms PruningGroups.linkedOwnerOrAbort

end AlternativeFusedTaskRemovalChecks
