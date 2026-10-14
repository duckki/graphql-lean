import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StackPlanning

/-! Enter/exit order, continuation counters and same-index planning. Exit observations
are postorder; lookup must preserve intervals rather than assume list order equality.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.StackPlanning.Tests

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning

example : StackPreorderOptimization := StackPreorderOptimization_holds
example : StackPlanningOptimization := StackPlanningOptimization_holds

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
        (fun entry =>
          (entry.usage.ref, entry.interval.start, entry.interval.stop))
      = [(12, 2, 3), (11, 1, 3), (13, 3, 4), (10, 0, 4), (20, 4, 5)] :=
  rfl

example : makeIndex (traverse forest).completed = makeIndex (forest.encode 0 []) :=
  traverse_index forest unique

-- Output record order is deliberately not the original enter/collector order.
example : (traverse forest).completed ≠ forest.encode 0 [] := by
  intro equal
  have keys := congrArg (List.map (fun entry => entry.usage.ref)) equal
  contradiction

private def detail (key : Nat) (ancestors : List Nat := []) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors }
  }

private def groups : CollectedFieldsMap :=
  [
    ("first", [detail 12 [11, 10], detail 20, detail 11 [10], detail 10]),
    ("same", [detail 10, detail 20])
  ]

private theorem generated : ∀ group ∈ groups, FieldsFromForest forest group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl <;>
    simp [FieldsFromForest, forest, Forest.encode, Forest.keys, detail]

example
    : (IntervalPlanning.buildPlan (makeIndex (traverse forest).completed) groups).project
        = buildExecutionPlan groups
      ∧ CanonicalPlanning.KeysMatch
          (IntervalPlanning.buildPlan (makeIndex (traverse forest).completed)
            groups).partitions
      ∧ ((IntervalPlanning.buildPlan (makeIndex (traverse forest).completed)
            groups).partitions.map
          CanonicalPlanning.KeyedPartition.key).Nodup :=
  StackPlanningOptimization_holds forest unique groups [] generated

example
    : (IntervalPlanning.buildPlan (makeIndex (traverse forest).completed) groups
        [10, 20]).project
      = buildExecutionPlan groups [10, 20] :=
  (StackPlanningOptimization_holds forest unique groups [10, 20] generated).1

example
    : (traverse .empty).finished = true
      ∧ (traverse .empty).ordinal = 0
      ∧ (traverse .empty).visits = 0 := by decide

example : (run 0 0 [.scan forest []]).finished = false := rfl

-- The close frame sees the current counter, not the entered ordinal or subtree size.
example
    : (run 1 7 [.close 10 [] 3]).completed.map
        (fun entry =>
          (entry.interval.start, entry.interval.stop))
      = [(3, 7)] :=
  rfl

-- Closing before children makes the parent's interval exclude its own descendant.
example
    : (run 2 1 [.close 10 [] 0, .close 11 [10] 1]).completed.map
        (fun entry =>
          (entry.interval.start, entry.interval.stop))
      = [(0, 1), (1, 1)] :=
  rfl

#print axioms StackPreorderOptimization_holds
#print axioms StackPlanningOptimization_holds
#print axioms traverse_index

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.StackPlanning.Tests
