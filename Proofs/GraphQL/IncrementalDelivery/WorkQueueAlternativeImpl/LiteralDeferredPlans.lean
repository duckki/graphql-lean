import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.LiteralGrowingFields

/-! Constructed execution of deferred partitions with literal-valued resolver leaves.
Each actual field scope constructs its map; later partitions preserve all earlier owner,
ancestor and child-work images. A failed group remains a task and does not cancel the
following partitions. This is not general recursive object or native-history refinement. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Bounds on already allocated input metadata, independent of execution outcomes
-----------------------------------------------------------------------------------------

def FieldsBelow (bound : Nat) (fields : CollectedFieldsMap) : Prop :=
  ∀ entry ∈ fields, ∀ details ∈ entry.2, ∀ key ∈ fieldKeys details, key < bound

def PartitionsBelow (bound : Nat) (partitions : List (List Nat × CollectedFieldsMap))
    : Prop :=
  ∀ partition ∈ partitions,
    (∀ key ∈ partition.1, key < bound) ∧ FieldsBelow bound partition.2

def LiteralPartitions (resolvers : Resolvers ObjectRef) (parentType : Name)
    (source : ResolverValue ObjectRef) (partitions : List (List Nat × CollectedFieldsMap))
    : Prop :=
  ∀ partition ∈ partitions, LiteralFields resolvers parentType source partition.2

theorem fields_prefix {before after : Nat → Nat} {bound : Nat}
    (fields : CollectedFieldsMap) (bounded : FieldsBelow bound fields)
    (same : ∀ key < bound, after key = before key)
    : KeyRenaming.fields after fields = KeyRenaming.fields before fields := by
  apply List.map_congr_left
  intro entry member
  have details : entry.2.map (field after) = entry.2.map (field before) :=
    List.map_congr_left (fun details inFields => field_congr details
      (fun key inKeys => same key (bounded entry member details inFields key inKeys)))
  exact congrArg (fun tail => (entry.1, tail)) details

theorem context_prefix {before after : Nat → Nat} {bound : Nat} (context : DeferMap)
    (bounded : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < bound)
    (same : ∀ key < bound, after key = before key)
    : context.map (fragment after) = context.map (fragment before) :=
  List.map_congr_left
    (fun group member =>
      fragment_congr group
        (fun key inGroup =>
          same key (bounded key (List.mem_flatMap.mpr ⟨group, member, inGroup⟩))))

theorem partitions_prefix {before after : Nat → Nat} {bound : Nat}
    (partitions : List (List Nat × CollectedFieldsMap))
    (bounded : PartitionsBelow bound partitions)
    (same : ∀ key < bound, after key = before key)
    : KeyRenaming.partitions after partitions
      = KeyRenaming.partitions before partitions := by
  apply List.map_congr_left
  intro partition member
  have usages : partition.1.map after = partition.1.map before :=
    List.map_congr_left (fun key inKeys => same key ((bounded partition member).1 key inKeys))
  change (partition.1.map after, KeyRenaming.fields after partition.2)
    = (partition.1.map before, KeyRenaming.fields before partition.2)
  rw [usages, fields_prefix partition.2 (bounded partition member).2 same]

theorem lookup_groups_maps {keys : Nat → Nat} (injective : Function.Injective keys)
    (context : DeferMap) (usages : List Nat)
    : (usages.map keys).filterMap (lookupDeferredFragment? (context.map (fragment keys)))
      = (usages.filterMap (lookupDeferredFragment? context)).map (fragment keys) := by
  simp only [List.filterMap_map, Function.comp_def, lookup_fragment injective, List.map_filterMap]

/-- Adapt a Work-returning actual run to the same full run certificate; the dummy result
has no error contribution. No task payload is replaced or discarded. -/
def workRun (actual : Work × Nat) : Completion Unit × Nat :=
  ({ result := .ok ((), 0), work := actual.1 }, actual.2)

-----------------------------------------------------------------------------------------
-- Actual deferred-group construction carries one map through every partition
-----------------------------------------------------------------------------------------

theorem literal_collectExecutionGroups_run (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
    (context : DeferMap) (keys : Nat → Nat) (left right : Nat)
    (literal : LiteralPartitions resolvers parentType source partitions)
    (supplies : SupplyMap keys left right) (bounded : PartitionsBelow left partitions)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          (workRun
            ((ScheduledExecution.collectExecutionGroups schema resolvers variables
                fuel parentType source partitions path context).run
              left))
          (workRun
            ((Execution.collectExecutionGroups schema resolvers variables fuel parentType
                source (KeyRenaming.partitions keys partitions) path
                (context.map (fragment keys))).run
              right)) := by
  induction partitions generalizing keys left right with
  | nil =>
      simp only [ScheduledExecution.collectExecutionGroups, Execution.collectExecutionGroups,
        KeyRenaming.partitions, List.map_nil, StateT.run_pure, id_pure_eq, workRun]
      refine ⟨keys, ⟨fun _ _ => rfl, supplies, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩⟩
      · simp [allRefs, rootRefs, hiddenRegions]
      · exact ⟨ResultRefines.refl _, .empty, rfl⟩
  | cons partition rest ih =>
      rcases partition with ⟨usages, fields⟩
      let partition := (usages, fields)
      obtain ⟨middle, head⟩ := literalGrowingFieldScope_holds _ schema resolvers variables fuel
        parentType source partition.2 path partition.1 context keys left right
        (literal partition (by simp [partition])) supplies (bounded partition (by simp [partition])).2
        (bounded partition (by simp [partition])).1 contextBound
      have restBelow : PartitionsBelow left rest :=
        fun partition member => bounded partition (List.mem_cons_of_mem _ member)
      have restAdvanced : PartitionsBelow
          ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel parentType
            source partition.2 path partition.1 context).run left).2 rest := by
        intro entry member
        refine ⟨fun key inKeys => Nat.lt_of_lt_of_le ((restBelow entry member).1 key inKeys)
          head.scheduledMonotone, ?_⟩
        intro group inFields details inGroup key inKeys
        exact Nat.lt_of_lt_of_le ((restBelow entry member).2 group inFields details inGroup key inKeys)
          head.scheduledMonotone
      obtain ⟨next, tail⟩ := ih middle _ _
        (fun partition member => literal partition (List.mem_cons_of_mem _ member))
        head.supplies restAdvanced
        (fun key member => Nat.lt_of_lt_of_le (contextBound key member) head.scheduledMonotone)
      have restMapped := partitions_prefix rest restBelow head.compatible
      have contextMapped := context_prefix context contextBound head.compatible
      rw [restMapped, contextMapped] at tail
      have prefixSame : ∀ key < left, next key = keys key := fun key earlier =>
        (tail.compatible key (Nat.lt_of_lt_of_le earlier head.scheduledMonotone)).trans
          (head.compatible key earlier)
      have ownersMapped :
          (partition.1.filterMap (lookupDeferredFragment? context)).map (fragment next)
          = (partition.1.filterMap (lookupDeferredFragment? context)).map (fragment keys) :=
        List.map_congr_left (fun group member => fragment_congr group (fun key inGroup =>
          prefixSame key (contextBound key
            (mapRefs_filterMap_subset context partition.1
              (List.mem_flatMap.mpr ⟨group, member, inGroup⟩)))))
      have regions := ScheduledExecution.collectExecutionGroups_regions schema resolvers
        variables fuel parentType source (partition :: rest) path context left contextBound
      simp only [partition, ScheduledExecution.collectExecutionGroups, run_bind,
        StateT.run_pure, id_pure_eq] at regions
      simp only [ScheduledExecution.collectExecutionGroups, Execution.collectExecutionGroups,
        Execution.executeExecutionGroup, KeyRenaming.partitions, List.map_cons,
        lookup_groups_maps supplies.injective, run_bind, StateT.run_pure, id_pure_eq, workRun]
      refine ⟨next, ⟨prefixSame, tail.supplies,
        Nat.le_trans head.scheduledMonotone tail.scheduledMonotone,
        Nat.le_trans head.eagerMonotone tail.eagerMonotone, regions.bounded, ?_⟩⟩
      refine ⟨ResultRefines.refl _, .combine ?_ tail.completion.2.1, rfl⟩
      rw [← ownersMapped]
      exact WorkRefines.executionGroup ⟨head.completion.1, head.completion.2.2⟩
        (head.completion.2.1.rekey
          (fun key member => tail.compatible key (head.bounded key member)))

/-- Literal deferred partitions construct their witnesses even after an earlier failed
partition skips allocations. One existential covers owners, ancestors and child Work. -/
def LiteralDeferredGroupRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    partitions path context keys left right,
    LiteralPartitions resolvers parentType source partitions
    → SupplyMap keys left right
    → PartitionsBelow left partitions
    → (∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    → ∃ next,
        RunRefines keys next left right
          (workRun
            ((ScheduledExecution.collectExecutionGroups schema resolvers variables
                fuel parentType source partitions path context).run
              left))
          (workRun
            ((Execution.collectExecutionGroups schema resolvers variables fuel parentType
                source (KeyRenaming.partitions keys partitions) path
                (context.map (fragment keys))).run
              right))

theorem literalDeferredGroupRefinement_holds : LiteralDeferredGroupRefinement := by
  intro ObjectRef schema resolvers variables fuel parentType source partitions path context
    keys left right literal supplies bounded contextBound
  exact literal_collectExecutionGroups_run schema resolvers variables fuel parentType source
    partitions path context keys left right literal supplies bounded contextBound

-----------------------------------------------------------------------------------------
-- Actual plan execution: initial fatal cut, or retained initial Work plus all groups
-----------------------------------------------------------------------------------------

theorem literal_executeExecutionPlan_run (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (newUsages : List DeferUsage)
    (original : ExecutionPlan) (path : ResponsePath) (usages : List Nat)
    (context : DeferMap) (keys : Nat → Nat) (left right : Nat)
    (initialLiteral
      : LiteralFields resolvers parentType source original.collectedFieldsMap)
    (deferredLiteral
      : LiteralPartitions resolvers parentType source original.newCollectedFieldsMaps)
    (supplies : SupplyMap keys left right)
    (initialBound : FieldsBelow left original.collectedFieldsMap)
    (deferredBound : PartitionsBelow left original.newCollectedFieldsMaps)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound
      : ∀ key ∈ (getNewDeferMap newUsages path context).flatMap RefRoles.fragmentRefs,
          key < left)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.executeExecutionPlan schema resolvers variables fuel
              parentType source newUsages original path usages context).run
            left)
          ((Execution.executeExecutionPlan schema resolvers variables fuel parentType
              source (newUsages.map (usage keys)) (plan keys original) path
              (usages.map keys) (context.map (fragment keys))).run
            right) := by
  obtain ⟨middle, head⟩ := literalGrowingFieldScope_holds _ schema resolvers variables fuel
    parentType source original.collectedFieldsMap path usages (getNewDeferMap newUsages path context)
    keys left right initialLiteral supplies initialBound usageBound contextBound
  have same := head.completion.1.1
  simp only [ScheduledExecution.executeExecutionPlan, Execution.executeExecutionPlan,
    plan, new_defer_map supplies.injective, run_bind]
  cases cutOutcome :
      ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel parentType
        source original.collectedFieldsMap path usages (getNewDeferMap newUsages path context)).run
        left).1.result
  <;> cases eagerOutcome :
      ((Execution.executeCollectedFields schema resolvers variables fuel parentType source
        (KeyRenaming.fields keys original.collectedFieldsMap) path (usages.map keys)
        ((getNewDeferMap newUsages path context).map (fragment keys))).run right).1.result
  <;> simp only [SameData, cutOutcome, eagerOutcome] at same
  · simp only [StateT.run_pure, id_pure_eq]
    exact ⟨middle, head⟩
  · have advanced : PartitionsBelow
        ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel parentType
          source original.collectedFieldsMap path usages (getNewDeferMap newUsages path context)).run
          left).2 original.newCollectedFieldsMaps := by
      intro partition member
      refine ⟨fun key inKeys => Nat.lt_of_lt_of_le ((deferredBound partition member).1 key inKeys)
        head.scheduledMonotone, ?_⟩
      intro entry inFields details inEntry key inKeys
      exact Nat.lt_of_lt_of_le ((deferredBound partition member).2 entry inFields details inEntry
        key inKeys) head.scheduledMonotone
    obtain ⟨next, tail⟩ := literal_collectExecutionGroups_run schema resolvers variables fuel
      parentType source original.newCollectedFieldsMaps path (getNewDeferMap newUsages path context)
      middle _ _ deferredLiteral head.supplies advanced
      (fun key member => Nat.lt_of_lt_of_le (contextBound key member) head.scheduledMonotone)
    rw [partitions_prefix _ deferredBound head.compatible,
      context_prefix _ contextBound head.compatible] at tail
    simp only [run_bind, StateT.run_pure, id_pure_eq]
    refine ⟨next, ⟨?_, tail.supplies,
      Nat.le_trans head.scheduledMonotone tail.scheduledMonotone,
      Nat.le_trans head.eagerMonotone tail.eagerMonotone, ?_, ?_⟩⟩
    · intro key earlier
      exact (tail.compatible key (Nat.lt_of_lt_of_le earlier head.scheduledMonotone)).trans
        (head.compatible key earlier)
    · intro key member
      rcases (mem_allRefs_combine _ _ _).mp member with inHead | inTail
      · exact Nat.lt_of_lt_of_le (head.bounded key inHead) tail.scheduledMonotone
      · exact tail.bounded key inTail
    · refine ⟨?_, .combine
        (head.completion.2.1.rekey (fun key member => tail.compatible key (head.bounded key member)))
        tail.completion.2.1, by simpa only [cutOutcome, eagerOutcome] using head.completion.2.2⟩
      simpa only [cutOutcome, eagerOutcome] using head.completion.1

/-- Literal-valued execution plans construct one full witness, including initial
failure and failed deferred tasks. Bounds concern the original actual input metadata;
no recursive paired-output or independently selected per-group map is assumed. -/
def LiteralExecutionPlanRefinement : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) fuel parentType (source : ResolverValue ObjectRef)
    newUsages original path usages context keys left right,
    LiteralFields resolvers parentType source original.collectedFieldsMap
    → LiteralPartitions resolvers parentType source original.newCollectedFieldsMaps
    → SupplyMap keys left right
    → FieldsBelow left original.collectedFieldsMap
    → PartitionsBelow left original.newCollectedFieldsMaps
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ (getNewDeferMap newUsages path context).flatMap RefRoles.fragmentRefs,
        key < left)
    → ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.executeExecutionPlan schema resolvers variables fuel
              parentType source newUsages original path usages context).run
            left)
          ((Execution.executeExecutionPlan schema resolvers variables fuel parentType
              source (newUsages.map (usage keys)) (plan keys original) path
              (usages.map keys) (context.map (fragment keys))).run
            right)

theorem literalExecutionPlanRefinement_holds : LiteralExecutionPlanRefinement := by
  intro ObjectRef schema resolvers variables fuel parentType source newUsages original path
    usages context keys left right initialLiteral deferredLiteral supplies initialBound
    deferredBound usageBound contextBound
  exact literal_executeExecutionPlan_run schema resolvers variables fuel parentType source
    newUsages original path usages context keys left right initialLiteral deferredLiteral
    supplies initialBound deferredBound usageBound contextBound

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
