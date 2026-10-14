import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CanonicalPlanning

/-! Canonical keys may sort identities; stored owners and details must retain collector
order. Colliding summaries and sorting the stored representative are deliberately refuted.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CanonicalPlanning.Tests

open GraphQL.IncrementalDelivery.Execution

example : CanonicalPartitionOptimization := CanonicalPartitionOptimization_holds

example (groups : CollectedFieldsMap) (parent : List Nat)
    : (buildPlan groups parent).project = buildExecutionPlan groups parent
      ∧ KeysMatch (buildPlan groups parent).partitions
      ∧ ((buildPlan groups parent).partitions.map KeyedPartition.key).Nodup :=
  CanonicalPartitionOptimization_holds groups parent

private def detail (key : Nat) (ancestors : List Nat := []) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors }
  }

private def details (keys : List Nat) : List FieldDetails :=
  keys.map fun key => detail key

private def groups : CollectedFieldsMap :=
  [("first", details [4, 1, 4]), ("same", details [1, 4]), ("different", details [9])]

example : partitionKey [4, 1, 4] = partitionKey [1, 4] :=
  (partitionKey_eq_iff _ _).2 (by simp [or_comm, or_left_comm])

private theorem storedOwners
    : ((buildPlan groups).partitions.map KeyedPartition.usages) = [[4, 1], [9]] := by
  have exactPlan := (CanonicalPartitionOptimization_holds groups []).1
  have same := congrArg (fun plan => plan.newCollectedFieldsMaps.map Prod.fst) exactPlan
  simp only [KeyedPlan.project, List.map_map, Function.comp_def, KeyedPartition.project] at same
  change ((buildPlan groups).partitions.map KeyedPartition.usages) = [[4, 1], [9]] at same
  exact same

private theorem sortedOwners : partitionKey [4, 1] = [1, 4] := by
  calc
    partitionKey [4, 1] = partitionKey [1, 4] :=
      (partitionKey_eq_iff _ _).2 (by simp [or_comm])
    _ = [1, 4] := partitionKey_eq_self _ (by decide) (by decide)

example : ((buildPlan groups).partitions.map KeyedPartition.key) = [[1, 4], [9]] := by
  have matching := (CanonicalPartitionOptimization_holds groups []).2.1
  calc
    _ = (buildPlan groups).partitions.map
          (fun partition => partitionKey partition.usages) :=
      List.map_congr_left matching
    _ = ((buildPlan groups).partitions.map KeyedPartition.usages).map partitionKey := by
      simp only [List.map_map, Function.comp_def]
    _ = [[1, 4], [9]] := by
      rw [storedOwners]
      simp only [List.map_cons, List.map_nil, sortedOwners,
        partitionKey_eq_self [9] (by decide) (by decide)]

example : ((buildPlan groups).partitions.map KeyedPartition.usages) = [[4, 1], [9]] :=
  storedOwners

example
    : ((buildPlan groups).partitions.map (fun partition => partition.fields.map Prod.fst))
      = [["first", "same"], ["different"]] := by
  have exactPlan := (CanonicalPartitionOptimization_holds groups []).1
  have same := congrArg (fun plan => plan.newCollectedFieldsMaps.map (fun part => part.2.map Prod.fst)) exactPlan
  simp only [KeyedPlan.project, List.map_map, Function.comp_def, KeyedPartition.project] at same
  change ((buildPlan groups).partitions.map (fun partition => partition.fields.map Prod.fst))
    = [["first", "same"], ["different"]] at same
  exact same

example : (buildPlan groups).project = buildExecutionPlan groups :=
  (CanonicalPartitionOptimization_holds groups []).1

example
    : (buildPlan [("dominance", [detail 9 [1], detail 4, detail 1])]).partitions.head?.map
        KeyedPartition.usages
      = some [4, 1] :=
  rfl

-- The parent set uses set equivalence but retains the exact original immediate details.
example : (buildPlan groups [1, 4, 1]).immediate = groups.take 2 := rfl

example
    : (buildPlan
        [
          ("immediate", [{ (detail 9) with deferUsage := none }, detail 1]),
          ("empty", [])
        ]).immediate
      = [
        ("immediate", [{ (detail 9) with deferUsage := none }, detail 1]),
        ("empty", [])
      ] :=
  rfl

example : ((buildPlan [("empty", [])] [1]).partitions.map KeyedPartition.key) = [[]] := by
  simp [buildPlan, KeyedPlan.step, addPartition, getFilteredDeferUsageSet, deferUsageSetsEquivalent, partitionKey]

example (ordinal : Nat → Nat) (left right : List Nat)
    (separates : ∀ a ∈ left, ∀ b ∈ right, ordinal a = ordinal b → a = b)
    : partitionKey (left.map ordinal) = partitionKey (right.map ordinal)
      ↔ deferUsageSetsEquivalent left right = true :=
  partitionKey_recode_iff ordinal left right separates

-- A hash/ordinal collision is not set equality; checking it is essential to a native bridge.
example
    : partitionKey ([1].map fun _ => 0) = partitionKey ([2].map fun _ => 0)
      ∧ deferUsageSetsEquivalent [1] [2] = false := by
  constructor <;> rfl

example
    : ([1, 4] : List Nat).sum = ([2, 3] : List Nat).sum
      ∧ partitionKey [1, 4] ≠ partitionKey [2, 3] := by
  constructor
  · rfl
  · intro collision
    have same := (partitionKey_eq_iff _ _).1 collision 1
    simp at same

private def sortedRepresentatives (plan : ExecutionPlan) : ExecutionPlan :=
  {
    plan with
      newCollectedFieldsMaps :=
        plan.newCollectedFieldsMaps.map
          (fun (owners, fields) => (partitionKey owners, fields))
  }

-- Replacing the first owner Set by its canonical key loses observable contributor order.
example
    : sortedRepresentatives (buildExecutionPlan groups) ≠ buildExecutionPlan groups := by
  intro changed
  have owners := congrArg (fun plan => plan.newCollectedFieldsMaps.map Prod.fst) changed
  change [partitionKey [4, 1], partitionKey [9]] = [[4, 1], [9]] at owners
  rw [sortedOwners] at owners
  contradiction

#print axioms CanonicalPartitionOptimization_holds
#print axioms partitionKey_recode_iff
#print axioms partitionKey_beq

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CanonicalPlanning.Tests
