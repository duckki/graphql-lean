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

-- Success transfers the shared source while its failed co-owner awaits notification.
example : (mixed.drainReadyGroups).1.queue.rootStreams = [7] := by cbv
example : (mixed.drainReadyGroups).1.queue.taskNode? producer = none := by cbv
example : (mixed.drainReadyGroups).2.2.1 = [] := by cbv

-- Root order still permits the ready co-owner to transfer the shared source.
private def failureFirst : State :=
  { mixed with queue := { mixed.queue with rootGroups := [1, 0] } }

example : (failureFirst.drainReadyGroups).1.queue.rootStreams = [7] := by cbv
example : (failureFirst.drainReadyGroups).2.2.1 = [] := by cbv

-- Cached startup of both failed co-owners disposes the last-owned held source once.
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

private def failedStartup := allFailed.startNewWork ⟨[first, second], []⟩

example : failedStartup.1.queue.rootStreams = [] := by cbv
example : failedStartup.2.1 = [.task producer, .stream 7] := by cbv
example : failedStartup.2.2 = [⟨first, 1⟩, ⟨second, 1⟩] := by cbv

example
    : (failedStartup.1.drainReadyGroups failedStartup.2.1).2.2.1
      = [.task producer, .stream 7] := by cbv

-- A successful parent releases a failed child; startup disposes its held source inline.
private def releasedFailure : State :=
  {
    queue :=
      {
        rootGroups := [0]
        groupNodes :=
          [
            { group := ⟨first, none⟩, childGroups := [1] },
            { group := ⟨second, some 0⟩, tasks := [producer, rejected], pending := 1 }
          ]
        tasks :=
          [
            { occurrence := producer, groups := [second] },
            { occurrence := rejected, groups := [second] }
          ]
        taskNodes :=
          [
            {
              task := { occurrence := producer, groups := [second] }, childStreams := [7]
            },
            {
              task := { occurrence := rejected, groups := [second] }, rejection := some 1
            }
          ]
        streams := [⟨source⟩]
      }
  }

example : releasedFailure.drainReadyGroups.1.queue.taskNode? producer = none := by cbv
example : releasedFailure.drainReadyGroups.2.2.1 = [.task producer, .stream 7] := by cbv
example : releasedFailure.drainReadyGroups.2.2.2 = [⟨second, 1⟩] := by cbv

private def lease : ResourceState :=
  fun target => if target = .stream 7 then .owned .queue else .unacquired

example
    : (lease.observeReadyDrain failedStartup.1 failedStartup.2.1).1 (.stream 7)
      = .cleanupRequested .queue := by cbv

example : (lease.observeReadyDrain mixed []).1 (.stream 7) = .owned .queue := by cbv

#print axioms FusedDrainSourceProgress_holds
#print axioms GeneratedReferenceDrainSourceProgress_holds
#print axioms readyDrain_resourceSafety

end AlternativeFusedDrainSourceChecks
