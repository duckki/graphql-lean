import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerKeyEncoding

/-! Same-run string-keyed partition planning. The observer uses ordered lists solely to
specify Map insertion/lookup observations; it is not a new public container or algorithm.
The actual indexed sweep supplies both stable owners and serialized ordinal keys.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.SerializedPlanning

open GraphQL.IncrementalDelivery.Execution
open IntervalPlanning PreorderPlanning PlannerKeyEncoding

-----------------------------------------------------------------------------------------
-- Native partition locator and unchanged original payload
-----------------------------------------------------------------------------------------

def ownerKey (index : Index) (usages : List Nat) : String :=
  encode (CanonicalPlanning.partitionKey (usages.map (fun key => (index key).start)))

structure Partition where
  key : String
  usages : List Nat
  fields : CollectedFieldsMap
deriving Repr

def Partition.project (partition : Partition) : List Nat × CollectedFieldsMap :=
  (partition.usages, partition.fields)

def addPartition (key : String) (usages : List Nat) (group : Name × List FieldDetails)
    : List Partition → List Partition
  | [] => [⟨key, usages, [group]⟩]
  | partition :: rest =>
      if partition.key == key then
        { partition with fields := partition.fields ++ [group] } :: rest
      else
        partition :: addPartition key usages group rest

structure Plan where
  immediate : CollectedFieldsMap := []
  partitions : List Partition := []
deriving Repr

def Plan.project (plan : Plan) : ExecutionPlan :=
  ⟨plan.immediate, plan.partitions.map Partition.project⟩

def Plan.step (index : Index) (parent : List Nat) (plan : Plan)
    (group : Name × List FieldDetails)
    : Plan :=
  let usages := filteredUsages index group.2
  if deferUsageSetsEquivalent usages parent then
    { plan with immediate := plan.immediate ++ [group] }
  else
    {
      plan with
        partitions := addPartition (stringKey index group.2) usages group plan.partitions
    }

def buildPlan (index : Index) (groups : CollectedFieldsMap) (parent : List Nat := [])
    : Plan :=
  groups.foldl (Plan.step index parent) {}

/-- An independently meaningful representation invariant, not assumed plan equality.
Every stored owner belongs to this index's identity domain; its string encodes its set.
-/
def Compatible (index : Index) (domain : List Nat) (partitions : List Partition) : Prop :=
  ∀ partition ∈ partitions,
    partition.key = ownerKey index partition.usages ∧ partition.usages.Subset domain

def SerializedPlanningOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups parent,
        (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let index := makeIndex (forest.encode 0 [])
          let observed := buildPlan index groups parent
          observed.project = buildExecutionPlan groups parent
          ∧ Compatible index forest.keys observed.partitions
          ∧ (observed.partitions.map Partition.key).Nodup

def StackSerializedPlanningOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ groups parent,
        (∀ group ∈ groups, FieldsFromForest forest group.2)
        → let index := makeIndex (StackPlanning.traverse forest).completed
          let observed := buildPlan index groups parent
          observed.project = buildExecutionPlan groups parent
          ∧ Compatible index forest.keys observed.partitions
          ∧ (observed.partitions.map Partition.key).Nodup

-----------------------------------------------------------------------------------------
-- Constructed index derives string equality and the store's owner domain
-----------------------------------------------------------------------------------------

theorem stringKey_eq_ownerKey (index : Index) (fields : List FieldDetails)
    (certificate : IndexFor index fields)
    : stringKey index fields = ownerKey index (getFilteredDeferUsageSet fields) := by
  rw [stringKey, TupleKeyOptimization_holds index fields certificate]
  rfl

theorem ownerKey_beq (index : Index) (domain left right : List Nat)
    (intervals : ValidIntervals index domain)
    (leftIn : left.Subset domain) (rightIn : right.Subset domain)
    : (ownerKey index left == ownerKey index right)
      = deferUsageSetsEquivalent left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, ownerKey, encode_eq_iff]
  exact CanonicalPlanning.partitionKey_recode_iff _ left right
    (fun a ha b hb => intervals.separates a (leftIn ha) b (rightIn hb))

private theorem filtered_subset (forest : Forest) (fields : List FieldDetails)
    (fromForest : FieldsFromForest forest fields)
    : (getFilteredDeferUsageSet fields).Subset forest.keys := by
  intro key present
  simp only [getFilteredDeferUsageSet] at present
  split at present
  · contradiction
  · obtain ⟨selected, _⟩ := List.mem_filter.mp present
    obtain ⟨usage, member, equal⟩ := by
      simpa only [List.mem_eraseDups, List.mem_map] using selected
    obtain ⟨entry, entryMember, keyEq, _⟩ := fromForest usage member
    rw [← equal, ← keyEq, ← Forest.encode_keys forest 0 []]
    exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩

-----------------------------------------------------------------------------------------
-- Lookup refines public set comparison; appends preserve the first representative
-----------------------------------------------------------------------------------------

private theorem addPartition_compatible (index : Index) (domain usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List Partition)
    (matching : Compatible index domain partitions) (inDomain : usages.Subset domain)
    : Compatible index domain
        (addPartition (ownerKey index usages) usages group partitions) := by
  induction partitions with
  | nil => simp [addPartition, Compatible, inDomain]
  | cons partition rest ih =>
      have head := matching partition (by simp)
      have tail := ih (fun item member => matching item (List.mem_cons_of_mem _ member))
      simp only [addPartition]
      split <;> simp_all [Compatible]

private theorem addPartition_memKey (key : String) (usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List Partition) (query : String)
    : query ∈ (addPartition key usages group partitions).map Partition.key
      ↔ query ∈ partitions.map Partition.key ∨ query = key := by
  induction partitions with
  | nil => simp [addPartition]
  | cons partition rest ih =>
      by_cases equal : partition.key = key
      · simp [addPartition, equal, or_comm]
      · simp [addPartition, equal, ih, or_assoc]

private theorem addPartition_unique (key : String) (usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List Partition)
    (unique : (partitions.map Partition.key).Nodup)
    : ((addPartition key usages group partitions).map Partition.key).Nodup := by
  induction partitions with
  | nil => simp [addPartition]
  | cons partition rest ih =>
      by_cases equal : partition.key = key
      · simpa [addPartition, equal] using unique
      · obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
        simp only [addPartition, beq_iff_eq, equal, ↓reduceIte, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih tail⟩
        intro member
        rcases (addPartition_memKey key usages group rest partition.key).mp member with old | fresh
        · exact absent old
        · exact equal fresh

private theorem addPartition_project (index : Index) (domain usages : List Nat)
    (group : Name × List FieldDetails) (partitions : List Partition)
    (intervals : ValidIntervals index domain)
    (matching : Compatible index domain partitions) (inDomain : usages.Subset domain)
    : (addPartition (ownerKey index usages) usages group partitions).map Partition.project
      = addExecutionPartition usages group (partitions.map Partition.project) := by
  induction partitions with
  | nil => rfl
  | cons partition rest ih =>
      obtain ⟨headKey, headIn⟩ := matching partition (by simp)
      have tail := ih (fun item member => matching item (List.mem_cons_of_mem _ member))
      simp only [addPartition, List.map_cons, Partition.project, addExecutionPartition,
        headKey, ownerKey_beq index domain partition.usages usages intervals headIn inDomain]
      split <;> simp [Partition.project, tail]

-----------------------------------------------------------------------------------------
-- Whole-plan refinement and derived invariants through the same fold
-----------------------------------------------------------------------------------------

private theorem fold_invariants (forest : Forest) (unique : forest.keys.Nodup)
    (groups : CollectedFieldsMap) (parent : List Nat) (plan : Plan)
    (fromForest : ∀ group ∈ groups, FieldsFromForest forest group.2)
    (matching : Compatible (makeIndex (forest.encode 0 [])) forest.keys plan.partitions)
    (keysUnique : (plan.partitions.map Partition.key).Nodup)
    : let observed :=
        groups.foldl (Plan.step (makeIndex (forest.encode 0 [])) parent) plan
      Compatible (makeIndex (forest.encode 0 [])) forest.keys observed.partitions
      ∧ (observed.partitions.map Partition.key).Nodup := by
  induction groups generalizing plan with
  | nil => exact ⟨matching, keysUnique⟩
  | cons group rest ih =>
      have source := fromForest group (by simp)
      have certificate := source.indexFor forest unique group.2
      apply ih _ (fun item member => fromForest item (List.mem_cons_of_mem _ member))
      · dsimp only [Plan.step]
        rw [IndexedFilterOptimization_holds _ _ certificate, stringKey_eq_ownerKey _ _ certificate]
        split
        · exact matching
        · exact addPartition_compatible _ _ _ _ _ matching (filtered_subset forest group.2 source)
      · dsimp only [Plan.step]
        split
        · exact keysUnique
        · exact addPartition_unique _ _ _ _ keysUnique

private theorem fold_project (forest : Forest) (unique : forest.keys.Nodup)
    (groups : CollectedFieldsMap) (parent : List Nat) (plan : Plan)
    (fromForest : ∀ group ∈ groups, FieldsFromForest forest group.2)
    (matching : Compatible (makeIndex (forest.encode 0 [])) forest.keys plan.partitions)
    : (groups.foldl (Plan.step (makeIndex (forest.encode 0 [])) parent) plan).project
      = groups.foldl
          (fun old group =>
            if deferUsageSetsEquivalent (getFilteredDeferUsageSet group.2) parent then
              { old with collectedFieldsMap := old.collectedFieldsMap ++ [group] }
            else
              {
                old with
                  newCollectedFieldsMaps :=
                    addExecutionPartition
                      (getFilteredDeferUsageSet group.2) group old.newCollectedFieldsMaps
              })
          plan.project := by
  induction groups generalizing plan with
  | nil => rfl
  | cons group rest ih =>
      have source := fromForest group (by simp)
      have certificate := source.indexFor forest unique group.2
      have compatibleStep : Compatible (makeIndex (forest.encode 0 [])) forest.keys
          (plan.step (makeIndex (forest.encode 0 [])) parent group).partitions := by
        dsimp only [Plan.step]
        rw [IndexedFilterOptimization_holds _ _ certificate, stringKey_eq_ownerKey _ _ certificate]
        split
        · exact matching
        · exact addPartition_compatible _ _ _ _ _ matching (filtered_subset forest group.2 source)
      rw [List.foldl_cons, List.foldl_cons,
        ih _ (fun item member => fromForest item (List.mem_cons_of_mem _ member)) compatibleStep]
      dsimp only [Plan.step]
      rw [IndexedFilterOptimization_holds _ _ certificate, stringKey_eq_ownerKey _ _ certificate]
      split
      · rfl
      · simp only [Plan.project, addPartition_project _ _ _ _ _
          (PreorderIndexConstruction_holds forest unique).2.1 matching
          (filtered_subset forest group.2 source)]

theorem SerializedPlanningOptimization_holds : SerializedPlanningOptimization := by
  intro forest unique groups parent fromForest
  exact ⟨
    fold_project forest unique groups parent {} fromForest (by simp [Compatible]),
    fold_invariants forest unique groups parent {} fromForest (by simp [Compatible])
      (by simp)
  ⟩

theorem StackSerializedPlanningOptimization_holds
    : StackSerializedPlanningOptimization := by
  intro forest unique groups parent fromForest
  rw [StackPlanning.traverse_index forest unique]
  exact SerializedPlanningOptimization_holds forest unique groups parent fromForest

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.SerializedPlanning
