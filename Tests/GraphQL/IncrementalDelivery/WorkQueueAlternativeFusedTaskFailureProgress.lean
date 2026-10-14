import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedTaskFailureProgress

/-! Actual failed-owner disposal covers unstarted shared tasks and excludes the settler. -/

namespace AlternativeFusedTaskFailureProgressChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

private def first : Execution.DeliveryNode := { ref := 0, path := [] }
private def second : Execution.DeliveryNode := { ref := 1, path := [] }

private def failed : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [0], groups := [first, second] }

private def waiting : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [1], groups := [first, second] }

private def shared : State :=
  {
    queue :=
      {
        rootGroups := [0, 1]
        groupNodes :=
          [
            { group := ⟨first, none⟩, tasks := [failed.occurrence, waiting.occurrence] },
            { group := ⟨second, none⟩, tasks := [failed.occurrence, waiting.occurrence] }
          ]
        tasks := [failed, waiting]
        taskNodes := [{ task := failed }]
      }
  }

example : shared.queue.taskNode? waiting.occurrence = none := by cbv

example
    : (shared.taskFailure failed.occurrence 1).2.2 = [.abortTask waiting.occurrence] := by
  cbv

example : (shared.taskFailure failed.occurrence 1).1.queue.groupNodes = [] := by cbv
example : (shared.taskFailure (.executionGroup [9]) 1).2.2 = [] := by cbv

#print axioms failureFold_unsettledTask
#print axioms State.taskFailure_unsettledTask

end AlternativeFusedTaskFailureProgressChecks
