import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerFieldMaps

/-! Ordered Map writes, collector-derived uniqueness and whole stack/Map planning. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerFieldMaps.Tests

open GraphQL.IncrementalDelivery.Execution
open IntervalPlanning PreorderPlanning SerializedPlanning

example : FieldMapOptimization := FieldMapOptimization_holds
example : StackMapPlanningOptimization := StackMapPlanningOptimization_holds
example : CollectedFieldMapOptimization := CollectedFieldMapOptimization_holds

private def detail (name : String) (usage : Option DeferUsage := none) : FieldDetails :=
  { fieldName := name, arguments := [], selectionSet := [], deferUsage := usage }

example
    : putField ("new", [detail "N"]) [("first", [detail "F"]), ("last", [detail "L"])]
      = [("first", [detail "F"]), ("last", [detail "L"]), ("new", [detail "N"])] :=
  rfl

-- Replacing an existing key retains its position and does not append a second entry.
example
    : putField ("first", [detail "replacement"])
        [("first", [detail "F"]), ("last", [detail "L"])]
      = [("first", [detail "replacement"]), ("last", [detail "L"])] :=
  rfl

private def duplicate : CollectedFieldsMap :=
  [("same", [detail "old"]), ("same", [detail "new"])]

private def emptyIndex : Index := fun _ => ⟨0, 0⟩

example : ¬ (duplicate.map Prod.fst).Nodup := by decide

-- Raw repeated response keys refute the unrestricted Map/append equivalence.
example : (buildMapPlan emptyIndex duplicate).immediate = [("same", [detail "new"])] :=
  rfl

example : (SerializedPlanning.buildPlan emptyIndex duplicate).immediate = duplicate := rfl

example
    : buildMapPlan emptyIndex duplicate
      ≠ SerializedPlanning.buildPlan emptyIndex duplicate := by
  intro same
  have fields := congrArg Plan.immediate same
  have lengths := congrArg List.length fields
  change 1 = 2 at lengths
  omega

private def forest : Forest := .node 10 (.node 11 .empty .empty) (.node 20 .empty .empty)
private theorem unique : forest.keys.Nodup := by decide

private def groups : CollectedFieldsMap :=
  [
    ("first", [detail "A" (some { ref := 20 }), detail "B" (some { ref := 10 })]),
    ("sameOwners", [detail "C" (some { ref := 10 }), detail "D" (some { ref := 20 })]),
    ("child", [detail "E" (some { ref := 11, ancestors := [10] })]),
    ("immediate", [detail "F"]),
    ("empty", [])
  ]

private theorem responseKeys : (groups.map Prod.fst).Nodup := by decide

private theorem generated : ∀ group ∈ groups, FieldsFromForest forest group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [FieldsFromForest, detail, forest, Forest.encode, Forest.keys]

example
    : (buildMapPlan (makeIndex (StackPlanning.traverse forest).completed) groups).project
      = buildExecutionPlan groups :=
  (StackMapPlanningOptimization_holds forest unique groups [] responseKeys generated).1

example
    : (buildMapPlan (makeIndex (StackPlanning.traverse forest).completed) groups
        [10, 20]).project
      = buildExecutionPlan groups [10, 20] :=
  (StackMapPlanningOptimization_holds forest unique groups [10, 20] responseKeys
    generated).1

example
    : OrderedFields groups (buildMapPlan (makeIndex (forest.encode 0 [])) groups)
      ∧ UniqueFieldMaps (buildMapPlan (makeIndex (forest.encode 0 [])) groups) :=
  (FieldMapOptimization_holds _ _ [] responseKeys).2

-- No request-validation or response-key uniqueness premise is added to collection.
example {ObjectRef : Type} (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (state : Nat)
    : let groups :=
        ((collectSubfields schema variables parentType source fields).run
          state).1.collectedFieldsMap
      buildMapPlan emptyIndex groups = SerializedPlanning.buildPlan emptyIndex groups
      ∧ OrderedFields groups (buildMapPlan emptyIndex groups)
      ∧ UniqueFieldMaps (buildMapPlan emptyIndex groups) :=
  collectedSubfields_maps schema variables parentType source fields state emptyIndex []

#print axioms FieldMapOptimization_holds
#print axioms StackMapPlanningOptimization_holds
#print axioms CollectedFieldMapOptimization_holds
#print axioms collectedSubfields_maps

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerFieldMaps.Tests
