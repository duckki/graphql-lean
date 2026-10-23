import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! A ready parent releases a dormant child with a cached rejection and a held source. -/

namespace GraphQL.IncrementalDelivery.Tests.SourceDrainCleanup
open AlternativeWorkQueue

def group : Execution.DeliveryNode := { ref := 0, path := [] }
def child : Execution.DeliveryNode := { ref := 1, path := [] }
def carrier : Execution.DeliveryNode := { ref := 9, path := [] }
def source : Execution.DeliveryNode := { ref := 7, path := [] }
def producer : WorkQueueSemantics.Occurrence := .executionGroup [0]
def parentTask : WorkQueueSemantics.Occurrence := .executionGroup [1]
def failedTask : WorkQueueSemantics.Occurrence := .executionGroup [2]

def readyFailure : State :=
  {
    queue :=
      {
        rootGroups := [0]
        rootStreams := [9]
        groupNodes :=
          [
            { group := ⟨group, none⟩, tasks := [parentTask], childGroups := [1] },
            { group := ⟨child, some 0⟩, tasks := [producer, failedTask], pending := 1 }
          ]
        tasks :=
          [
            { occurrence := parentTask, groups := [group] },
            { occurrence := producer, groups := [child] },
            { occurrence := failedTask, groups := [child] }
          ]
        taskNodes :=
          [
            {
              task := { occurrence := parentTask, groups := [group] },
              value := some { deliveryGroups := [group], path := [], data := [] }
            },
            {
              task := { occurrence := producer, groups := [child] },
              value := some { deliveryGroups := [child], path := [], data := [] },
              childStreams := [7]
            },
            {
              task := { occurrence := failedTask, groups := [child] }, rejection := some 1
            }
          ]
        streams := [⟨source⟩, ⟨carrier⟩]
      }
  }

end GraphQL.IncrementalDelivery.Tests.SourceDrainCleanup
