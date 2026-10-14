import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SerializedPlanning

/-! Whole string-keyed planning, original owners/details and the index-domain boundary. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.SerializedPlanning.Tests

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning

example : SerializedPlanningOptimization := SerializedPlanningOptimization_holds
example : StackSerializedPlanningOptimization := StackSerializedPlanningOptimization_holds

private def forest : Forest :=
  .node 10 (.node 11 (.node 12 .empty .empty) (.node 13 .empty .empty))
    (.node 20 .empty .empty)

private theorem unique : forest.keys.Nodup := by decide

private def detail (key : Nat) (ancestors : List Nat := [])
    (label : Option String := none)
    : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors, label }
  }

private def groups : CollectedFieldsMap :=
  [
    (
      "first",
      [detail 12 [11, 10], detail 20, detail 11 [10], detail 10 [] (some "A"), detail 20]
    ),
    ("same", [detail 10 [] (some "different label"), detail 20]),
    ("separate", [detail 13 [10]]),
    ("immediate", [{ (detail 10) with deferUsage := none }, detail 20]),
    ("empty", [])
  ]

private theorem generated : ∀ group ∈ groups, FieldsFromForest forest group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldsFromForest, forest, Forest.encode, Forest.keys, detail]

example
    : (buildPlan (makeIndex (forest.encode 0 [])) groups).project
      = buildExecutionPlan groups :=
  (SerializedPlanningOptimization_holds forest unique groups [] generated).1

example
    : (buildPlan (makeIndex (StackPlanning.traverse forest).completed) groups
        [20, 10]).project
      = buildExecutionPlan groups [20, 10] :=
  (StackSerializedPlanningOptimization_holds forest unique groups [20, 10] generated).1

-- Whole details, labels and group order are retained, not reconstructed from the key.
example
    : ((buildPlan (makeIndex (forest.encode 0 [])) groups).project.newCollectedFieldsMaps)
      = [([20, 10], [groups[0], groups[1]]), ([13], [groups[2]])] := by
  rw [(SerializedPlanningOptimization_holds forest unique groups [] generated).1]
  rfl

example
    : ((buildPlan (makeIndex (forest.encode 0 [])) groups).project.collectedFieldsMap)
      = [groups[3], groups[4]] := by
  rw [(SerializedPlanningOptimization_holds forest unique groups [] generated).1]
  rfl

example
    : Compatible (makeIndex (forest.encode 0 [])) forest.keys
        (buildPlan (makeIndex (forest.encode 0 [])) groups).partitions :=
  (SerializedPlanningOptimization_holds forest unique groups [] generated).2.1

example
    : ((buildPlan (makeIndex (forest.encode 0 [])) groups).partitions.map
        Partition.key).Nodup :=
  (SerializedPlanningOptimization_holds forest unique groups [] generated).2.2

-- Owner representatives are collector ordered; canonical serialization is only a locator.
example
    : ownerKey (makeIndex (forest.encode 0 [])) [20, 10]
      = ownerKey (makeIndex (forest.encode 0 [])) [10, 20] := by
  have equal := ownerKey_beq (makeIndex (forest.encode 0 [])) forest.keys [20, 10] [10, 20]
    (PreorderIndexConstruction_holds forest unique).2.1
    (by
      intro key present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> decide)
    (by
      intro key present
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> decide)
  exact beq_iff_eq.mp equal

-- Unknown keys share the default span; serialization cannot repair a wrong identity domain.
example
    : ownerKey (makeIndex (forest.encode 0 [])) [998]
      = ownerKey (makeIndex (forest.encode 0 [])) [999] :=
  rfl

example : deferUsageSetsEquivalent [998] [999] = false := rfl

-- Parent comparison remains the public set comparison, even with no index entry for it.
example
    : (buildPlan (makeIndex (Forest.empty.encode 0 [])) [("empty", [])] [998]).project
      = buildExecutionPlan [("empty", [])] [998] :=
  (SerializedPlanningOptimization_holds .empty (by simp [Forest.keys]) _ _
    (by simp [FieldsFromForest])).1

#print axioms SerializedPlanningOptimization_holds
#print axioms StackSerializedPlanningOptimization_holds
#print axioms ownerKey_beq

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.SerializedPlanning.Tests
