import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Explicit declarations for hand-built execution work in queue regressions. -/

namespace GraphQL.IncrementalDelivery.Tests
open GraphQL.IncrementalDelivery.Execution

/-- Declare each contributor and its ancestors before constructing a fixture task.
This fixture builder makes registration candidates explicit in the execution tree.
-/
@[simp]
def declaredTask (groups : List DeferredFragment) (path : ResponsePath)
    (outcome : TaskOutcome (List (Name × ResponseValue))) (children : Work)
    : Work :=
  .declareGroups
    (groups.flatMap (fun group => chain (group.node :: group.ancestors)))
    (.executionGroup groups path outcome children)
where
  chain : List DeliveryNode → List DeferredFragment
    | [] => []
    | node :: ancestors => chain ancestors ++ [⟨node, ancestors⟩]

private def parent : DeliveryNode := { ref := 0, path := [] }
private def child : DeliveryNode := { ref := 1, path := [] }

-- Contributors alone do not declare groups; fixture declarations retain ancestor order.
#guard
  (ReferenceWorkQueue.Work.fromExecution
    (.executionGroup [⟨child, [parent]⟩] [] { result := .ok ([], 0) }
      .empty)).groups.isEmpty
#guard
  (ReferenceWorkQueue.Work.fromExecution
    (declaredTask [⟨child, [parent]⟩] [] { result := .ok ([], 0) } .empty)).groups.map
    (·.node.ref)
  == [0, 1]

end GraphQL.IncrementalDelivery.Tests
