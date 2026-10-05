import Proofs.GraphQL.IncrementalDelivery.Correctness.DeferredFailureCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Failure-aware coverage of actual plans with overlapping deferred field selections. -/

namespace GraphQL.IncrementalDelivery.Tests.DeferredFailureCoverage
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics
open Correctness

private def selected (last : Name) : List Selection :=
  [field "a", defer [field "b", field last], defer [field "b"]]

private def collected (last : Name) :=
  ((collectFields schema [] "Query" (.object "Query" 0) (selected last)).run 0).1

private def plan (last : Name) :=
  buildExecutionPlan (collected last).collectedFieldsMap []

private def completed (last : Name) :=
  ((executeExecutionPlan schema resolvers [] 30 "Query" (.object "Query" 0)
      (collected last).newDeferUsages (plan last)).run
    2).1

private def ownerField (name : Name) (ref : NodeRef) : FieldDetails :=
  {
    fieldName := name,
    arguments := [],
    selectionSet := [],
    directives := [],
    deferUsage := some { ref := ref }
  }

private def expectedPartitions (last : Name) : List (NodeRefs × CollectedFieldsMap) :=
  [
    ([0, 1], [("b", [ownerField "b" 0, ownerField "b" 1])]),
    ([0], [(last, [ownerField last 0])])
  ]

private def reference (last : Name) : ResponseValue :=
  (GraphQL.Execution.selectionSetResultToResponse
    (GraphQL.Execution.executeCollectedFields schema resolvers [] 30 "Query"
      (.object "Query" 0)
      (Semantics.eraseGroups (plan last).collectedFieldsMap
        ++ (plan last).newCollectedFieldsMaps.flatMap
            (fun partition => Semantics.eraseGroups partition.2)))).data

/-- The same field is assigned to both deferred owners by the real collection/plan stage.
Witness: reduction of the generated partition; its two contributors select one alias.
-/
example
    : (plan "fail").newCollectedFieldsMaps.head?.map (fun partition => partition.1)
      = some [0, 1] := by cbv

private theorem local_agreement (last : Name)
    (allowed : last = "fail" ∨ last = "required") (containers : Bool)
    : PreparedResponseCovers (reference last)
        (selectionSetResultToResponse (completed last).result) (completed last).work
        containers := by
  apply executeExecutionPlan_partition_coverage schema resolvers [] 30 "Query"
    (.object "Query" 0) (collected last).newDeferUsages (plan last) [] [] 2 containers
  · intro next
    rcases allowed with rfl | rfl <;> cbv
  · intro partition member next
    rcases allowed with rfl | rfl
    all_goals
      first
        | have actual : (plan "fail").newCollectedFieldsMaps
              = expectedPartitions "fail" := by cbv
          rw [actual] at member
        | have actual : (plan "required").newCollectedFieldsMaps
              = expectedPartitions "required" := by cbv
          rw [actual] at member
      simp only [expectedPartitions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> cbv

/-- A nullable deferred field error retains the ordinary null leaf and the shared value.
Witness: actual plan coverage, with local field comparisons reduced independently of the
state supply. Positive errors in successful payloads do not require failure scopes.
-/
example (containers : Bool)
    : PreparedResponseCovers
        (.object [("a", .scalar "a"), ("b", .scalar "b"), ("fail", .null)])
        { data := .object [("a", .scalar "a")], errors := 0 }
        (completed "fail").work containers := by
  have covered := local_agreement "fail" (Or.inl rfl) containers
  have basic : reference "fail"
      = .object [("a", .scalar "a"), ("b", .scalar "b"), ("fail", .null)] := by cbv
  have initial : (completed "fail").result = .ok ([("a", .scalar "a")], 0) := by cbv
  rw [basic, initial] at covered
  exact covered

/-- A non-null deferred failure explains ordinary root null without losing shared work.
Witness: the actual generated plan's failed retained partition, not a fabricated scope.
-/
example (containers : Bool)
    : PreparedResponseCovers .null { data := .object [("a", .scalar "a")], errors := 0 }
        (completed "required").work containers := by
  have covered := local_agreement "required" (Or.inr rfl) containers
  have basic : reference "required" = .null := by cbv
  have initial : (completed "required").result = .ok ([("a", .scalar "a")], 0) := by cbv
  rw [basic, initial] at covered
  exact covered

end GraphQL.IncrementalDelivery.Tests.DeferredFailureCoverage
