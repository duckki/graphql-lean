import Proofs.GraphQL.IncrementalDelivery.Correctness.RootPartitionFailureCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Ordinary root field order differs from the generated immediate/deferred plan order. -/

namespace GraphQL.IncrementalDelivery.Tests.RootPartitionFailureCoverage
open GraphQL.IncrementalDelivery.Execution
open Correctness
open WorkQueueSemantics

private def selections : List Selection :=
  [defer [field "b", field "fail"], field "a", defer [field "b"], field "c"]

private def collected :=
  ((collectFields schema [] "Query" (.object "Query" 0) selections).run 0).1

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1

private def ownerField (name : Name) (ref : NodeRef) : FieldDetails :=
  {
    fieldName := name,
    arguments := [],
    selectionSet := [],
    directives := [],
    deferUsage := some { ref := ref }
  }

private def partitions : List (NodeRefs × CollectedFieldsMap) :=
  [
    ([0, 1], [("b", [ownerField "b" 0, ownerField "b" 1])]),
    ([0], [("fail", [ownerField "fail" 0])])
  ]

/-- Actual root coverage includes the ordinary field order, not just partition order.
Witness: the root collection/erasure theorem and local scalar completion equations.
Two deferred owners share b, fail contributes a nullable error, and immediate fields
occur between the deferred selections in the original query.
-/
example (containers : Bool)
    : PreparedResponseCovers
        (.object
          [("b", .scalar "b"), ("fail", .null), ("a", .scalar "a"), ("c", .scalar "c")])
        { data := .object [("a", .scalar "a"), ("c", .scalar "c")], errors := 0 }
        completed.work containers := by
  have covered := executeRootSelectionSetCore_partition_coverage schema resolvers [] 30
    "Query" (.object "Query" 0) selections 0 collected 2 (by cbv)
    (by intro next; cbv)
    (by
      intro partition member next
      have actual : (buildExecutionPlan collected.collectedFieldsMap).newCollectedFieldsMaps
          = partitions := by cbv
      rw [actual] at member
      simp only [partitions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> cbv)
    containers
  change PreparedResponseCovers _ (selectionSetResultToResponse completed.result)
    completed.work containers at covered
  have ordinary : GraphQL.Execution.executeRootSelectionSet schema resolvers [] 30 "Query"
      (.object "Query" 0) (SelectionSet.eraseIncrementalDirectives selections)
      = .ok ([("b", .scalar "b"), ("fail", .null), ("a", .scalar "a"),
          ("c", .scalar "c")], 1) := by cbv
  have initial : completed.result
      = .ok ([("a", .scalar "a"), ("c", .scalar "c")], 0) := by cbv
  rw [ordinary, initial] at covered
  exact covered

end GraphQL.IncrementalDelivery.Tests.RootPartitionFailureCoverage
