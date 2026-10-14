import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.IntervalPlanning

/-! Same-plan interval certificate realizations, stable deletion, and malformed-index
counterexamples. These do not supply a native traversal or a string serialization bridge.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.IntervalPlanning.Tests

open GraphQL.IncrementalDelivery.Execution

example : IndexedFilterOptimization := IndexedFilterOptimization_holds
example : IndexedPlanningOptimization := IndexedPlanningOptimization_holds
example : TupleKeyOptimization := TupleKeyOptimization_holds

private def detail (key : Nat) (ancestors : List Nat := []) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors }
  }

-- Root 10 has chain 11→12 and child 13; root 20 starts exactly at root 10's stop.
private def index : Index
  | 10 => ⟨0, 4⟩
  | 11 => ⟨1, 3⟩
  | 12 => ⟨2, 3⟩
  | 13 => ⟨3, 4⟩
  | 20 => ⟨4, 5⟩
  | _ => ⟨5, 6⟩

private def overlapping : List FieldDetails :=
  [detail 12 [11, 10], detail 20, detail 11 [10], detail 10, detail 20]

private theorem overlapping_certified : IndexFor index overlapping := by
  constructor
  · constructor <;> simp [usageKeys, overlapping, detail, index]
  · simp [usageKeys, overlapping, detail, index]

example : filteredUsages index overlapping = [20, 10] := by
  rw [IndexedFilterOptimization_holds index overlapping overlapping_certified]
  rfl

-- Lookup ordinals are canonical [0,4] even though owners remain [20,10].
example : tupleKey index overlapping = [0, 4] := by
  rw [TupleKeyOptimization_holds index overlapping overlapping_certified]
  change CanonicalPlanning.partitionKey [4, 0] = [0, 4]
  calc
    _ = CanonicalPlanning.partitionKey [0, 4] :=
      (CanonicalPlanning.partitionKey_eq_iff _ _).2 (by simp [or_comm])
    _ = [0, 4] := CanonicalPlanning.partitionKey_eq_self _ (by decide) (by decide)

-- An unselected ancestor does not suppress either selected branch.
private def siblings : List FieldDetails := [detail 13 [10], detail 12 [11, 10]]

private theorem siblings_certified : IndexFor index siblings := by
  constructor
  · constructor <;> simp [usageKeys, siblings, detail, index]
  · simp [usageKeys, siblings, detail, index]

example : filteredUsages index siblings = [13, 12] := by
  rw [IndexedFilterOptimization_holds index siblings siblings_certified]
  rfl

private def groups : CollectedFieldsMap :=
  [("first", overlapping), ("same", [detail 10, detail 20]), ("siblings", siblings)]

private theorem groups_certified : ∀ group ∈ groups, IndexFor index group.2 := by
  intro group member
  simp [groups] at member
  rcases member with rfl | rfl | rfl
  · exact overlapping_certified
  · constructor
    · constructor <;> simp [usageKeys, detail, index]
    · simp [usageKeys, detail, index]
  · exact siblings_certified

example
    : (buildPlan index groups).project = buildExecutionPlan groups
      ∧ CanonicalPlanning.KeysMatch (buildPlan index groups).partitions
      ∧ ((buildPlan index groups).partitions.map
          CanonicalPlanning.KeyedPartition.key).Nodup :=
  IndexedPlanningOptimization_holds index groups [] groups_certified

-- The sorted sweep would emit [10,20], but stable deletion must retain [20,10].
example
    : ((buildPlan index groups).partitions.map CanonicalPlanning.KeyedPartition.usages)
      = [[20, 10], [13, 12]] := by
  have same := congrArg (fun plan => plan.newCollectedFieldsMaps.map Prod.fst)
    (IndexedPlanningOptimization_holds index groups [] groups_certified).1
  simp only [CanonicalPlanning.KeyedPlan.project, List.map_map, Function.comp_def,
    CanonicalPlanning.KeyedPartition.project] at same
  change ((buildPlan index groups).partitions.map CanonicalPlanning.KeyedPartition.usages)
    = [[20, 10], [13, 12]] at same
  exact same

example
    : (buildPlan index groups [10, 20]).project = buildExecutionPlan groups [10, 20] :=
  (IndexedPlanningOptimization_holds index groups [10, 20] groups_certified).1

-- Empty/immediate cases inspect no interval and need no valid index.
example (arbitrary : Index) : filteredUsages arbitrary [] = [] := by
  simp [filteredUsages, usageKeys]

example (arbitrary : Index)
    : filteredUsages arbitrary
        [{ (detail 12 [11, 10]) with deferUsage := none }, detail 10]
      = [] :=
  rfl

-- Crossing intervals are not a forest: a skipped interval can cover a later usage
-- beyond the retained barrier. The greedy scan then differs from ancestry suppression.
private def crossing : Index
  | 1 => ⟨0, 2⟩
  | 2 => ⟨1, 4⟩
  | _ => ⟨3, 4⟩

example : sweep crossing 0 [1, 2, 3] = [1, 3] := rfl

example : getFilteredDeferUsageSet [detail 1, detail 2 [1], detail 3 [2]] = [1] := rfl

example : ¬ ValidIntervals crossing [1, 2, 3] := by
  intro valid
  have cannotCross := valid.nested 1 (by simp) 2 (by simp) (by decide) (by decide)
  contradiction

-- A half-open stop is not inside its predecessor. Duplicate starts cannot identify owners.
example : sweep index 0 [10, 20] = [10, 20] := rfl

example : ¬ ValidIntervals (fun _ => ⟨0, 1⟩) [1, 2] := by
  intro valid
  have distinct := valid.separates 1 (by simp) 2 (by simp) rfl
  contradiction

-- Each singleton certificate can be valid while the keys collide across groups.
-- The native plan-wide ordinal index, not unrelated per-group indices, must separate them.
private theorem singleton_certified (key : Nat)
    : IndexFor (fun _ => ⟨0, 1⟩) [detail key] := by
  constructor
  · constructor <;> simp [usageKeys, detail]
  · simp [usageKeys, detail]

example
    : IndexFor (fun _ => ⟨0, 1⟩) [detail 1]
      ∧ IndexFor (fun _ => ⟨0, 1⟩) [detail 2]
      ∧ tupleKey (fun _ => ⟨0, 1⟩) [detail 1] = tupleKey (fun _ => ⟨0, 1⟩) [detail 2]
      ∧ deferUsageSetsEquivalent [1] [2] = false := by
  refine ⟨singleton_certified 1, singleton_certified 2, ?_, rfl⟩
  rw [TupleKeyOptimization_holds _ _ (singleton_certified 1),
    TupleKeyOptimization_holds _ _ (singleton_certified 2)]
  rfl

example : ¬ IndexFor index [detail 12, detail 10] := by
  intro valid
  have wrongAncestry := valid.ancestry { ref := 12, ancestors := [] }
    (by simp [detail]) 10 (by simp [usageKeys, detail])
  simp [index] at wrongAncestry

#print axioms IndexedFilterOptimization_holds
#print axioms IndexedPlanningOptimization_holds
#print axioms TupleKeyOptimization_holds
#print axioms tupleKey_eq_iff

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.IntervalPlanning.Tests
