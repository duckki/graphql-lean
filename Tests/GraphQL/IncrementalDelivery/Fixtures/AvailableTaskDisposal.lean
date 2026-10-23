import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! One newly activated group shares an available rejection and an unfinished computation.
Only the unfinished task requires an abort when cached startup removes their owner.
-/

namespace GraphQL.IncrementalDelivery.Tests.AvailableTaskDisposal
open AlternativeWorkQueue

def group : Execution.DeliveryNode := ⟨10, [], none⟩

def failed : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [0], groups := [group] }

def waiting : ReferenceWorkQueue.Task :=
  { occurrence := .executionGroup [1], groups := [group] }

def state : State :=
  {
    queue :=
      {
        rootGroups := [group.ref]
        groupNodes :=
          [{
            group := ⟨group, none⟩,
            tasks := [failed.occurrence, waiting.occurrence],
            pending := 2
          }]
        tasks := [failed, waiting]
        taskNodes := [{ task := failed }, { task := waiting }]
      }
  }

def available : List (WorkQueueSemantics.Occurrence × Nat) := [(failed.occurrence, 2)]

end GraphQL.IncrementalDelivery.Tests.AvailableTaskDisposal
