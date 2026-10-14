import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ForestParentSource

/-! Forest-derived parent links/height and discovery from original, unfiltered fields. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ForestParentSource.Tests

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning ParentDiscovery

example : ForestParentConstruction := ForestParentConstruction_holds
example : ForestFieldDiscoveryOptimization := ForestFieldDiscoveryOptimization_holds

private def forest : Forest :=
  .node 10 (.node 11 (.node 12 .empty .empty) (.node 13 .empty .empty))
    (.node 20 .empty (.node 30 .empty .empty))

private theorem unique : forest.keys.Nodup := by decide

example
    : parents forest 12 = some 11
      ∧ parents forest 11 = some 10
      ∧ parents forest 10 = none
      ∧ parents forest 20 = none := by decide

example : height forest 12 = 2 ∧ height forest 13 = 1 ∧ height forest 20 = 0 := by decide

example
    : lookup forest 999 = none ∧ parents forest 999 = none ∧ height forest 999 = 0 := by
  decide

example : Decreasing (parents forest) (height forest) :=
  (ForestParentConstruction_holds forest unique).1

private def detail (key : Nat) (ancestors : List Nat := []) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors }
  }

private def groups : CollectedFieldsMap :=
  [
    ("first", [detail 12 [11, 10], detail 20]),
    ("immediate", [{ (detail 10) with deferUsage := none }, detail 13 [10]])
  ]

private theorem generated : ∀ group ∈ groups, FieldsFromForest forest group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl <;>
    simp [FieldsFromForest, forest, Forest.encode, Forest.keys, detail]

example : fieldSeeds groups = [12, 20, 13] := rfl

example
    : (discover (parents forest) (height forest) (fieldSeeds groups)).nodes
      = [12, 11, 10, 20, 13] :=
  rfl

example
    : (discover (parents forest) (height forest) (fieldSeeds groups)).parentReads = 5
      ∧ (discover (parents forest) (height forest) (fieldSeeds groups)).probes = 6 := by
  decide

-- Discovery visits ancestors and immediate-dominated usages, but no unrelated sibling root.
example : getFilteredDeferUsageSet groups[1].2 = [] := rfl

example
    : 13 ∈ (discover (parents forest) (height forest) (fieldSeeds groups)).nodes
      ∧ 30 ∉ (discover (parents forest) (height forest) (fieldSeeds groups)).nodes := by
  decide

example
    : ParentClosed (parents forest)
        (discover (parents forest) (height forest) (fieldSeeds groups)).nodes :=
  (ForestFieldDiscoveryOptimization_holds forest unique groups generated).2.2.1

example
    : (discover (parents forest) (height forest) (fieldSeeds groups)).nodes.Subset
        forest.keys :=
  (ForestFieldDiscoveryOptimization_holds forest unique groups generated).2.2.2.1

-- Correct immutable links cannot justify unrelated field ancestry metadata.
example : ¬ FieldsFromForest forest [detail 12 [10]] := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, detail]

example : (discover (parents .empty) (height .empty) []).nodes = [] := rfl

#print axioms ForestParentConstruction_holds
#print axioms ForestFieldDiscoveryOptimization_holds

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ForestParentSource.Tests
