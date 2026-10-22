import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedDrainSources

/-! Source retention/transfer/cleanup follows the real mixed drain, in either root order. -/

namespace AlternativeFusedDrainSourceChecks
open GraphQL.IncrementalDelivery
open AlternativeWorkQueue
open AlternativeWorkQueue.NativeRefinement

example : FusedDrainSourceProgress := FusedDrainSourceProgress_holds

example : GeneratedReferenceDrainSourceProgress :=
  GeneratedReferenceDrainSourceProgress_holds

private def first : Execution.DeliveryNode := { ref := 0, path := [] }
private def second : Execution.DeliveryNode := { ref := 1, path := [] }
private def source : Execution.DeliveryNode := { ref := 7, path := [] }
private def producer : WorkQueueSemantics.Occurrence := .executionGroup [0]
private def rejected : WorkQueueSemantics.Occurrence := .executionGroup [1]
private def otherRejected : WorkQueueSemantics.Occurrence := .executionGroup [2]

private def mixed : State :=
  {
    queue :=
      {
        rootGroups := [0, 1]
        groupNodes :=
          [
            { group := ⟨first, none⟩, tasks := [producer] },
            { group := ⟨second, none⟩, tasks := [producer, rejected], pending := 1 }
          ]
        tasks :=
          [
            { occurrence := producer, groups := [first, second] },
            { occurrence := rejected, groups := [second] }
          ]
        taskNodes :=
          [
            {
              task := { occurrence := producer, groups := [first, second] }
              value := some { deliveryGroups := [first, second], path := [], data := [] }
              childStreams := [7]
            },
            {
              task := { occurrence := rejected, groups := [second] }, rejection := some 1
            }
          ]
        streams := [⟨source⟩]
      }
  }

-- Success transfers the shared source; the later failed co-owner cannot cancel it.
example : (mixed.drainReadyGroups).1.queue.rootStreams = [7] := by cbv
example : (mixed.drainReadyGroups).1.queue.taskNode? producer = none := by cbv
example : (mixed.drainReadyGroups).2.2 = [] := by cbv

-- Failure first still retains the healthy co-owner, whose subsequent success transfers.
private def failureFirst : State :=
  { mixed with queue := { mixed.queue with rootGroups := [1, 0] } }

example : (failureFirst.drainReadyGroups).1.queue.rootStreams = [7] := by cbv
example : (failureFirst.drainReadyGroups).2.2 = [] := by cbv

-- With both co-owners failed, the last actual removal disposes the held source once.
private def allFailed : State :=
  {
    mixed with
      queue :=
        {
          mixed.queue with
            groupNodes :=
              [
                {
                  group := ⟨first, none⟩, tasks := [producer, otherRejected], pending := 1
                },
                { group := ⟨second, none⟩, tasks := [producer, rejected], pending := 1 }
              ]
            tasks :=
              mixed.queue.tasks ++ [{ occurrence := otherRejected, groups := [first] }]
            taskNodes :=
              mixed.queue.taskNodes
              ++ [{
                    task := { occurrence := otherRejected, groups := [first] },
                    rejection := some 1
                  }]
        }
  }

example : (allFailed.drainReadyGroups).1.queue.rootStreams = [] := by cbv
example : (allFailed.drainReadyGroups).2.2 = [.task producer, .stream 7] := by cbv

private def lease : ResourceState :=
  fun target => if target = .stream 7 then .owned .queue else .unacquired

example
    : (lease.observeReadyDrain allFailed []).1 (.stream 7)
      = .cleanupRequested .queue := by cbv

example : (lease.observeReadyDrain mixed []).1 (.stream 7) = .owned .queue := by cbv

#print axioms FusedDrainSourceProgress_holds
#print axioms GeneratedReferenceDrainSourceProgress_holds
#print axioms readyDrain_resourceSafety

end AlternativeFusedDrainSourceChecks
