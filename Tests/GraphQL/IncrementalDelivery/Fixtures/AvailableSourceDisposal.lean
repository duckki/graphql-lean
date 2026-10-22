import GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl

/-! Raw startup fixture: two newly exposed rejections remove a buffered source's last owner.
This fixture makes no claim that an execution generated the supplied queue records.
-/

namespace GraphQL.IncrementalDelivery.Tests.AvailableSourceDisposal
open AlternativeWorkQueue

def owner : Execution.DeliveryNode := { ref := 10, path := [] }
def source : Execution.DeliveryNode := { ref := 20, path := [] }
def producer : WorkQueueSemantics.Occurrence := .executionGroup [0]
def firstFailure : WorkQueueSemantics.Occurrence := .executionGroup [1]
def secondFailure : WorkQueueSemantics.Occurrence := .executionGroup [2]

def buffered : ReferenceWorkQueue.TaskNode :=
  {
    task := { occurrence := producer, groups := [owner] }
    value := some { deliveryGroups := [owner], path := [], data := [] }
    childStreams := [source.ref]
  }

def initial : State :=
  {
    queue :=
      {
        groupNodes :=
          [{
            group := ⟨owner, none⟩,
            tasks := [producer, firstFailure, secondFailure],
            pending := 2
          }]
        tasks :=
          [
            buffered.task,
            { occurrence := firstFailure, groups := [owner] },
            { occurrence := secondFailure, groups := [owner] }
          ]
        taskNodes :=
          [
            buffered,
            { task := { occurrence := firstFailure, groups := [owner] } },
            { task := { occurrence := secondFailure, groups := [owner] } }
          ]
        streams := [⟨source⟩]
      }
  }

def available : List (WorkQueueSemantics.Occurrence × Nat) :=
  [(firstFailure, 2), (secondFailure, 3)]

def closed : State × List CleanupTarget × List ReferenceWorkQueue.GroupFailureEvent :=
  initial.startNewWork ⟨[owner], []⟩ {} [] available

end GraphQL.IncrementalDelivery.Tests.AvailableSourceDisposal
