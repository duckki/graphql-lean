import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Buffered values with a cached failing co-task and an optional surviving owner. -/

namespace GraphQL.IncrementalDelivery.Tests.Fixtures.StoredValueStartup
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue

def failingGroup : DeliveryNode := { ref := 2, path := [] }
def survivingGroup : DeliveryNode := { ref := 3, path := [] }

def buffered : TaskNode :=
  {
    task :=
      { occurrence := .executionGroup [0], groups := [failingGroup, survivingGroup] }
    value := some { path := [], data := [] }
  }

def rejected : TaskNode :=
  {
    task := { occurrence := .executionGroup [1], groups := [failingGroup] }
    rejection := some 1
  }

def survivor : GroupNode :=
  { group := { node := survivingGroup }, tasks := [buffered.task.occurrence] }

def startup : NewWork := { newGroups := [failingGroup] }

def queue : State :=
  {
    groupNodes :=
      [
        {
          group := { node := failingGroup },
          tasks := [buffered.task.occurrence, rejected.task.occurrence],
          pending := 1
        },
        survivor
      ]
    tasks := [buffered.task, rejected.task]
    taskNodes := [buffered, rejected]
  }

def lastOwner : State := { queue with groupNodes := queue.groupNodes.take 1 }

end GraphQL.IncrementalDelivery.Tests.Fixtures.StoredValueStartup
