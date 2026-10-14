import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerNodeStack

/-! Node-only traversal, array-end reverse pushes and whole Map planning. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerNodeStack.Tests

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning SerializedPlanning PlannerFieldMaps

example : NodeStackOptimization := NodeStackOptimization_holds
example : ReversePushOptimization := ReversePushOptimization_holds
example : NodeStackMapPlanningOptimization := NodeStackMapPlanningOptimization_holds

private def forest : Forest :=
  .node 10 (.node 11 (.node 12 .empty .empty) (.node 13 .empty .empty))
    (.node 20 .empty .empty)

private theorem unique : forest.keys.Nodup := by decide

example
    : (traverse forest).ordinal = 5
      ∧ (traverse forest).visits = 10
      ∧ (traverse forest).finished = true := by decide

example
    : (traverse forest).completed.map
        (fun entry => (entry.usage.ref, entry.interval.start, entry.interval.stop))
      = [(12, 2, 3), (11, 1, 3), (13, 3, 4), (10, 0, 4), (20, 4, 5)] :=
  rfl

example : traverse forest = StackPlanning.traverse forest :=
  NodeStackOptimization_holds forest

example : (run 9 0 (pending [] forest)).finished = false := rfl
example : (traverse .empty).finished = true ∧ (traverse .empty).visits = 0 := by decide

private def roots : List Frame := [.enter 10 .empty [], .enter 20 .empty []]
private def oldStack : List Frame := [.close 99 [] 0]

example : (pushReverse oldStack roots).reverse = roots ++ oldStack.reverse :=
  ReversePushOptimization_holds oldStack roots

example : (pushReverse [] roots).reverse = roots := rfl

-- Forward-pushing ordered children onto an array-end stack reverses their visit order.
example : ([] ++ roots).reverse ≠ roots := by
  intro same
  have keys := congrArg (List.map (fun frame => match frame with | .enter key _ _ => key | .close key _ _ => key)) same
  contradiction

private def detail (key : Nat) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key }
  }

private def groups : CollectedFieldsMap :=
  [("first", [detail 20, detail 10]), ("same", [detail 10, detail 20])]

private theorem responseKeys : (groups.map Prod.fst).Nodup := by decide

private theorem generated : ∀ group ∈ groups, FieldsFromForest forest group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl <;>
    simp [FieldsFromForest, detail, forest, Forest.encode, Forest.keys]

example
    : (buildMapPlan (makeIndex (traverse forest).completed) groups).project
      = buildExecutionPlan groups :=
  (NodeStackMapPlanningOptimization_holds forest unique groups [] responseKeys
    generated).1

example
    : (buildMapPlan (makeIndex (traverse forest).completed) groups [10, 20]).project
      = buildExecutionPlan groups [10, 20] :=
  (NodeStackMapPlanningOptimization_holds forest unique groups [10, 20] responseKeys
    generated).1

#print axioms NodeStackOptimization_holds
#print axioms ReversePushOptimization_holds
#print axioms NodeStackMapPlanningOptimization_holds

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerNodeStack.Tests
