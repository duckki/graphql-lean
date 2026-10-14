import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PreorderPlanning

/-! Constructed forest certificates, exact ancestry/ordinals and same-input planning.
Labels and collector order remain original payload, not reconstructed forest metadata.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PreorderPlanning.Tests

open GraphQL.IncrementalDelivery.Execution
open IntervalPlanning

example : PreorderIndexConstruction := PreorderIndexConstruction_holds
example : ForestPlanningOptimization := ForestPlanningOptimization_holds

private def forest : Forest :=
  .node 10 (.node 11 (.node 12 .empty .empty) (.node 13 .empty .empty))
    (.node 20 .empty .empty)

private theorem unique : forest.keys.Nodup := by decide

example
    : (forest.encode 0 []).map
        (fun entry =>
          (entry.usage.ref, entry.interval.start, entry.interval.stop))
      = [(10, 0, 4), (11, 1, 3), (12, 2, 3), (13, 3, 4), (20, 4, 5)] :=
  rfl

example
    : (forest.encode 0 []).map (fun entry => (entry.usage.ref, entry.usage.ancestors))
      = [(10, []), (11, [10]), (12, [11, 10]), (13, [10]), (20, [])] :=
  rfl

example : (forest.encode 0 []).length = 5 := rfl

example (key : Nat) (present : key ∈ forest.keys)
    : (makeIndex (forest.encode 0 []) key).start
        < (makeIndex (forest.encode 0 []) key).stop
      ∧ (makeIndex (forest.encode 0 []) key).stop ≤ 5 :=
  forest_index_bounds forest unique key present

private def detail (key : Nat) (ancestors : List Nat := [])
    (label : Option String := none)
    : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors, label }
  }

private def overlapping : List FieldDetails :=
  [
    detail 12 [11, 10] (some "C"),
    detail 20,
    detail 11 [10],
    detail 10 [] (some "A"),
    detail 20
  ]

private def reversed : List FieldDetails := [detail 10 [] (some "A"), detail 20]

private theorem overlapping_fromForest : FieldsFromForest forest overlapping := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, overlapping, detail]

private theorem reversed_fromForest : FieldsFromForest forest reversed := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, reversed, detail]

example : IndexFor (makeIndex (forest.encode 0 [])) overlapping :=
  overlapping_fromForest.indexFor forest unique overlapping

example : filteredUsages (makeIndex (forest.encode 0 [])) overlapping = [20, 10] := by
  rw [IndexedFilterOptimization_holds _ _ (overlapping_fromForest.indexFor forest unique overlapping)]
  rfl

example
    : tupleKey (makeIndex (forest.encode 0 [])) overlapping
      = tupleKey (makeIndex (forest.encode 0 [])) reversed := by
  apply (forest_tupleKey_eq_iff forest unique overlapping reversed
    overlapping_fromForest reversed_fromForest).2
  rfl

-- One constructed index separates different field groups as well as their internal owners.
private theorem singleton_fromForest : FieldsFromForest forest [detail 20] := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, detail]

example
    : tupleKey (makeIndex (forest.encode 0 [])) reversed
      ≠ tupleKey (makeIndex (forest.encode 0 [])) [detail 20] := by
  intro collision
  have same := (forest_tupleKey_eq_iff forest unique reversed [detail 20]
    reversed_fromForest singleton_fromForest).1 collision
  contradiction

private def groups : CollectedFieldsMap := [("first", overlapping), ("same", reversed)]

private theorem groups_fromForest
    : ∀ group ∈ groups, FieldsFromForest forest group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl
  · exact overlapping_fromForest
  · exact reversed_fromForest

example
    : (IntervalPlanning.buildPlan (makeIndex (forest.encode 0 [])) groups).project
        = buildExecutionPlan groups
      ∧ CanonicalPlanning.KeysMatch
          (IntervalPlanning.buildPlan (makeIndex (forest.encode 0 [])) groups).partitions
      ∧ ((IntervalPlanning.buildPlan (makeIndex (forest.encode 0 []))
            groups).partitions.map
          CanonicalPlanning.KeyedPartition.key).Nodup :=
  ForestPlanningOptimization_holds forest unique groups [] groups_fromForest

example
    : ((IntervalPlanning.buildPlan (makeIndex (forest.encode 0 [])) groups).partitions.map
        CanonicalPlanning.KeyedPartition.usages)
      = [[20, 10]] := by
  have same := congrArg (fun plan => plan.newCollectedFieldsMaps.map Prod.fst)
    (ForestPlanningOptimization_holds forest unique groups [] groups_fromForest).1
  simp only [CanonicalPlanning.KeyedPlan.project, List.map_map, Function.comp_def,
    CanonicalPlanning.KeyedPartition.project] at same
  change ((IntervalPlanning.buildPlan (makeIndex (forest.encode 0 [])) groups).partitions.map
    CanonicalPlanning.KeyedPartition.usages) = [[20, 10]] at same
  exact same

-- Empty forests and immediate/empty fields make the domain non-vacuous at size zero.
example : ValidIntervals (makeIndex (Forest.empty.encode 0 [])) [] :=
  (PreorderIndexConstruction_holds .empty (by simp [Forest.keys])).2.1

example : FieldsFromForest .empty [{ (detail 10) with deferUsage := none }] := by
  simp [FieldsFromForest]

-- Duplicate identities can make keyed lookup return the wrong occurrence's interval.
private def duplicate : Forest := .node 1 .empty (.node 1 .empty .empty)

example : ¬ duplicate.keys.Nodup := by decide

example
    : ∃ entry ∈ duplicate.encode 0 [],
        makeIndex (duplicate.encode 0 []) entry.usage.ref ≠ entry.interval := by
  exact ⟨
    ⟨{ ref := 1, ancestors := [] }, ⟨1, 2⟩⟩,
    by simp [duplicate, Forest.encode, Forest.keys],
    by decide
  ⟩

-- Inconsistent field ancestry is not repaired by a plausible interval index.
example : ¬ FieldsFromForest forest [detail 12] := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, detail]

#print axioms PreorderIndexConstruction_holds
#print axioms ForestPlanningOptimization_holds
#print axioms forest_tupleKey_eq_iff
#print axioms forest_index_bounds

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PreorderPlanning.Tests
