import GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Fixtures.WorkDeclarations

open GraphQL.IncrementalDelivery.Tests (declaredTask)

/-! Finite queues for successful draining and cached-rejection notification boundaries. -/

namespace GraphQL.IncrementalDelivery.Tests.Fixtures.DrainNormalForm
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

def parent : DeliveryNode := { ref := 2, path := [] }
def child : DeliveryNode := { ref := 3, path := [] }

def failedTask : Task := { occurrence := .executionGroup [], groups := [child] }

def readyWork : Execution.Work :=
  declaredTask [⟨child, [parent]⟩] [] { result := .error 3 } .empty

def readyChain : State :=
  {
    rootGroups := [99, parent.ref]
    groupNodes :=
      [
        { group := { node := parent }, childGroups := [child.ref] },
        {
          group := { node := child, parent := some parent.ref },
          tasks := [failedTask.occurrence],
          pending := 1
        }
      ]
    tasks := [failedTask]
    taskNodes := [{ task := failedTask, rejection := some 3 }]
  }

def activeCached : State := { readyChain with rootGroups := [child.ref] }

end GraphQL.IncrementalDelivery.Tests.Fixtures.DrainNormalForm
