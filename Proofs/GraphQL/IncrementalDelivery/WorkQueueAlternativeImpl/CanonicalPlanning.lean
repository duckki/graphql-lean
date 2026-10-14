import Proofs.GraphQL.IncrementalDelivery.Semantics.Planning
import Init.Data.List.Sort.Lemmas

/-! Canonical partition lookup with stable collector-order representatives. The key
is a sorted, duplicate-free tuple of usage identities, not a ported Map or queue rank.
This isolates indexed partition lookup from interval construction,
ancestry filtering and native ordinal/string correspondence, which remain separate.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CanonicalPlanning

open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Collision-free lookup keys; original ordered owners and details remain the payload
-----------------------------------------------------------------------------------------

def partitionKey (usages : List Nat) : List Nat :=
  usages.eraseDups.mergeSort (fun a b => decide (a ≤ b))

structure KeyedPartition where
  key : List Nat
  usages : List Nat
  fields : CollectedFieldsMap
deriving Repr

def KeyedPartition.project (partition : KeyedPartition) : List Nat × CollectedFieldsMap :=
  (partition.usages, partition.fields)

/-- An ordered semantic observer of keyed lookup. A runtime may use a Map locator;
neither list scanning nor a new collection framework is proposed for public execution.
-/
def addPartition (usages : List Nat) (group : Name × List FieldDetails)
    : List KeyedPartition → List KeyedPartition
  | [] => [⟨partitionKey usages, usages, [group]⟩]
  | partition :: rest =>
      if partition.key == partitionKey usages then
        { partition with fields := partition.fields ++ [group] } :: rest
      else
        partition :: addPartition usages group rest

structure KeyedPlan where
  immediate : CollectedFieldsMap := []
  partitions : List KeyedPartition := []
deriving Repr

def KeyedPlan.project (plan : KeyedPlan) : ExecutionPlan :=
  ⟨plan.immediate, plan.partitions.map KeyedPartition.project⟩

def KeyedPlan.step (parent : List Nat) (plan : KeyedPlan)
    (group : Name × List FieldDetails)
    : KeyedPlan :=
  let usages := getFilteredDeferUsageSet group.2
  if deferUsageSetsEquivalent usages parent then
    { plan with immediate := plan.immediate ++ [group] }
  else
    { plan with partitions := addPartition usages group plan.partitions }

def KeysMatch (partitions : List KeyedPartition) : Prop :=
  ∀ partition ∈ partitions, partition.key = partitionKey partition.usages

def buildPlan (groups : CollectedFieldsMap) (parent : List Nat := []) : KeyedPlan :=
  groups.foldl (KeyedPlan.step parent) {}

/-- Exact unchanged Execution plan, including first owner-set order and all field details.
No indexed-filter equality, collision freedom or output equality is supplied as a premise.
-/
def CanonicalPartitionOptimization : Prop :=
  ∀ groups parent,
    let observed := buildPlan groups parent
    observed.project = buildExecutionPlan groups parent
    ∧ KeysMatch observed.partitions
    ∧ (observed.partitions.map KeyedPartition.key).Nodup

-----------------------------------------------------------------------------------------
-- Key equality derives set equality, including raw duplicate/order variations
-----------------------------------------------------------------------------------------

private theorem eraseDups_nodup (keys : List Nat) : keys.eraseDups.Nodup := by
  cases keys with
  | nil => simp
  | cons key rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup _
termination_by keys.length
decreasing_by
  simp_wf
  exact Nat.lt_of_le_of_lt (List.length_filter_le _ rest) (Nat.lt_succ_self _)

theorem partitionKey_mem (keys : List Nat) (key : Nat)
    : key ∈ partitionKey keys ↔ key ∈ keys := by
  simp [partitionKey]

theorem partitionKey_nodup (keys : List Nat) : (partitionKey keys).Nodup :=
  (List.mergeSort_perm _ _).symm.nodup (eraseDups_nodup keys)

private theorem partitionKey_sorted (keys : List Nat)
    : (partitionKey keys).Pairwise (fun a b => a ≤ b) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c ab bc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) keys.eraseDups
  simpa only [partitionKey, decide_eq_true_eq] using sorted

theorem partitionKey_eq_self (keys : List Nat) (unique : keys.Nodup)
    (sorted : keys.Pairwise (fun a b => a ≤ b))
    : partitionKey keys = keys := by
  have permutation := (List.perm_ext_iff_of_nodup (partitionKey_nodup keys) unique).2
    (partitionKey_mem keys)
  exact List.Perm.eq_of_pairwise (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
    (partitionKey_sorted keys) sorted permutation

theorem partitionKey_eq_iff (left right : List Nat)
    : partitionKey left = partitionKey right ↔ ∀ key, key ∈ left ↔ key ∈ right := by
  constructor
  · intro equal key
    rw [← partitionKey_mem left key, ← partitionKey_mem right key, equal]
  · intro members
    have permutation := (List.perm_ext_iff_of_nodup (partitionKey_nodup left)
      (partitionKey_nodup right)).2 (by intro key; simpa only [partitionKey_mem] using members key)
    exact List.Perm.eq_of_pairwise (fun a b _ _ ab ba => Nat.le_antisymm ab ba)
      (partitionKey_sorted left) (partitionKey_sorted right) permutation

private theorem setsEquivalent_iff (left right : List Nat)
    : deferUsageSetsEquivalent left right = true ↔ ∀ key, key ∈ left ↔ key ∈ right := by
  simp only [deferUsageSetsEquivalent, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨forward, backward⟩ key
    exact ⟨forward key, backward key⟩
  · intro members
    exact ⟨fun key => (members key).1, fun key => (members key).2⟩

theorem partitionKey_beq (left right : List Nat)
    : (partitionKey left == partitionKey right)
      = deferUsageSetsEquivalent left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, partitionKey_eq_iff, setsEquivalent_iff]

/-- Re-encoding identities as unique plan-local ordinals preserves key equality. Only
cross-set identities actually used in this comparison need separation. Construction of
those ordinals by the native forest traversal is not assumed to be proved here.
-/
theorem partitionKey_recode_iff (ordinal : Nat → Nat) (left right : List Nat)
    (separates : ∀ a ∈ left, ∀ b ∈ right, ordinal a = ordinal b → a = b)
    : partitionKey (left.map ordinal) = partitionKey (right.map ordinal)
      ↔ deferUsageSetsEquivalent left right = true := by
  rw [partitionKey_eq_iff, setsEquivalent_iff]
  constructor
  · intro same key
    constructor
    · intro member
      obtain ⟨other, present, equal⟩ := List.mem_map.mp
        ((same (ordinal key)).1 (List.mem_map.mpr ⟨key, member, rfl⟩))
      exact (separates key member other present equal.symm).symm ▸ present
    · intro member
      obtain ⟨other, present, equal⟩ := List.mem_map.mp
        ((same (ordinal key)).2 (List.mem_map.mpr ⟨key, member, rfl⟩))
      exact separates other present key member equal ▸ present
  · intro same key
    constructor
    · rintro member
      obtain ⟨usage, present, equal⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨usage, (same usage).1 present, equal⟩
    · rintro member
      obtain ⟨usage, present, equal⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨usage, (same usage).2 present, equal⟩

-----------------------------------------------------------------------------------------
-- One compatible ordered keyed store through the actual plan fold
-----------------------------------------------------------------------------------------

private theorem addPartition_keysMatch (usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List KeyedPartition)
    (matching : KeysMatch partitions)
    : KeysMatch (addPartition usages group partitions) := by
  induction partitions with
  | nil => simp [addPartition, KeysMatch]
  | cons partition rest ih =>
      have head := matching partition (by simp)
      have tail := ih (fun item member => matching item (List.mem_cons_of_mem _ member))
      simp only [addPartition]
      split <;> simp_all [KeysMatch]

private theorem addPartition_memKey (usages : List Nat) (group : Name × List FieldDetails)
    (partitions : List KeyedPartition) (key : List Nat)
    : key ∈ (addPartition usages group partitions).map KeyedPartition.key
      ↔ key ∈ partitions.map KeyedPartition.key ∨ key = partitionKey usages := by
  induction partitions with
  | nil => simp [addPartition]
  | cons partition rest ih =>
      by_cases equal : partition.key = partitionKey usages
      · simp [addPartition, equal, or_comm]
      · simp [addPartition, equal, ih, or_assoc]

private theorem addPartition_keysUnique (usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List KeyedPartition)
    (unique : (partitions.map KeyedPartition.key).Nodup)
    : ((addPartition usages group partitions).map KeyedPartition.key).Nodup := by
  induction partitions with
  | nil => simp [addPartition]
  | cons partition rest ih =>
      by_cases equal : partition.key = partitionKey usages
      · simpa [addPartition, equal] using unique
      · obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
        simp only [addPartition, beq_iff_eq, equal, ↓reduceIte, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih tail⟩
        intro member
        rcases (addPartition_memKey usages group rest partition.key).mp member with old | fresh
        · exact absent old
        · exact equal fresh

theorem addPartition_project (usages : List Nat) (group : Name × List FieldDetails)
    (partitions : List KeyedPartition) (matching : KeysMatch partitions)
    : (addPartition usages group partitions).map KeyedPartition.project
      = addExecutionPartition usages group (partitions.map KeyedPartition.project) := by
  induction partitions with
  | nil => rfl
  | cons partition rest ih =>
      have head := matching partition (by simp)
      have tail := ih (fun item member => matching item (List.mem_cons_of_mem _ member))
      simp only [addPartition, List.map_cons, KeyedPartition.project, addExecutionPartition,
        head, partitionKey_beq]
      split <;> simp [KeyedPartition.project, tail]

private theorem KeyedPlan.step_keysMatch (parent : List Nat) (plan : KeyedPlan)
    (group : Name × List FieldDetails) (matching : KeysMatch plan.partitions)
    : KeysMatch (plan.step parent group).partitions := by
  dsimp only [KeyedPlan.step]
  split
  · exact matching
  · exact addPartition_keysMatch _ _ _ matching

private theorem KeyedPlan.step_keysUnique (parent : List Nat) (plan : KeyedPlan)
    (group : Name × List FieldDetails)
    (unique : (plan.partitions.map KeyedPartition.key).Nodup)
    : ((plan.step parent group).partitions.map KeyedPartition.key).Nodup := by
  dsimp only [KeyedPlan.step]
  split
  · exact unique
  · exact addPartition_keysUnique _ _ _ unique

private theorem fold_keys (groups : CollectedFieldsMap) (parent : List Nat)
    (plan : KeyedPlan) (matching : KeysMatch plan.partitions)
    (unique : (plan.partitions.map KeyedPartition.key).Nodup)
    : let observed := groups.foldl (KeyedPlan.step parent) plan
      KeysMatch observed.partitions
      ∧ (observed.partitions.map KeyedPartition.key).Nodup := by
  induction groups generalizing plan with
  | nil => exact ⟨matching, unique⟩
  | cons group rest ih =>
      exact ih _ (plan.step_keysMatch parent group matching) (plan.step_keysUnique parent group unique)

private theorem fold_project (groups : CollectedFieldsMap) (parent : List Nat)
    (plan : KeyedPlan) (matching : KeysMatch plan.partitions)
    : (groups.foldl (KeyedPlan.step parent) plan).project
      = groups.foldl
          (fun old group =>
            if deferUsageSetsEquivalent (getFilteredDeferUsageSet group.2) parent then
              { old with collectedFieldsMap := old.collectedFieldsMap ++ [group] }
            else
              {
                old with
                  newCollectedFieldsMaps :=
                    addExecutionPartition (getFilteredDeferUsageSet group.2) group
                      old.newCollectedFieldsMaps
              })
          plan.project := by
  induction groups generalizing plan with
  | nil => rfl
  | cons group rest ih =>
      rw [List.foldl_cons, List.foldl_cons, ih _ (plan.step_keysMatch parent group matching)]
      dsimp only [KeyedPlan.step]
      cases condition
            : deferUsageSetsEquivalent (getFilteredDeferUsageSet group.2) parent with
      | false => simp [KeyedPlan.project, addPartition_project _ _ _ matching]
      | true => simp [KeyedPlan.project]

theorem CanonicalPartitionOptimization_holds : CanonicalPartitionOptimization := by
  intro groups parent
  refine ⟨?_, fold_keys groups parent {} (by simp [KeysMatch]) (by simp)⟩
  simpa only [buildPlan, buildExecutionPlan, KeyedPlan.project, List.map_nil]
    using fold_project groups parent {} (by simp [KeysMatch])

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.CanonicalPlanning
