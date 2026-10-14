import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveFieldComposition

/-! General deferred-group and execution-plan composition. A single field-scope
construction hypothesis is used at every actual growing supply, including failed tasks.
No literal resolver domain or paired collected-output premise remains in these edges. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Ordered input metadata is inherited by every original execution partition
-----------------------------------------------------------------------------------------

def PartitionsBefore (bound : Nat) (partitions : List (List Nat × CollectedFieldsMap))
    : Prop :=
  ∀ partition ∈ partitions,
    (∀ key ∈ partition.1, key < bound) ∧ FieldsBefore bound partition.2

theorem PartitionsBefore.below {bound : Nat}
    {partitions : List (List Nat × CollectedFieldsMap)}
    (known : PartitionsBefore bound partitions)
    : PartitionsBelow bound partitions :=
  fun partition member => ⟨(known partition member).1, (known partition member).2.below⟩

theorem PartitionsBefore.mono {left right : Nat}
    {partitions : List (List Nat × CollectedFieldsMap)}
    (known : PartitionsBefore left partitions) (advanced : left ≤ right)
    : PartitionsBefore right partitions :=
  fun partition member =>
    ⟨
      fun key inKeys =>
        Nat.lt_of_lt_of_le ((known partition member).1 key inKeys) advanced,
      (known partition member).2.mono advanced
    ⟩

def PlanRunConstruction (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ parentType (source : ResolverValue ObjectRef) newUsages original path usages context
    keys left right,
    SupplyMap keys left right
    → FieldsBefore left original.collectedFieldsMap
    → PartitionsBefore left original.newCollectedFieldsMaps
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

theorem build_plan_before {bound : Nat} (fields : CollectedFieldsMap) (parent : List Nat)
    (known : FieldsBefore bound fields)
    : FieldsBefore bound (buildExecutionPlan fields parent).collectedFieldsMap
      ∧ PartitionsBefore bound
          (buildExecutionPlan fields parent).newCollectedFieldsMaps := by
  have ordered := buildExecutionPlan_preserves_property
    (fun details => UsageBefore bound details.deferUsage) fields parent known
  have bounded := build_plan_below fields parent known.below
  exact ⟨ordered.1, fun partition member =>
    ⟨(bounded.2 partition member).1, ordered.2 partition member⟩⟩

-----------------------------------------------------------------------------------------
-- Each actual deferred task constructs its map, even when its result is fatal
-----------------------------------------------------------------------------------------

theorem collectExecutionGroups_run_of_fields (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (children : FieldScopeRunConstruction schema resolvers variables fuel)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
    (context : DeferMap) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right) (ordered : PartitionsBefore left partitions)
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
      · exact ⟨ResultRefines.refl _, .empty⟩
  | cons partition rest ih =>
      rcases partition with ⟨usages, fields⟩
      let partition := (usages, fields)
      obtain ⟨middle, head⟩ := children parentType source partition.2 path partition.1
        context keys left right supplies (ordered partition (by simp [partition])).2
        (ordered partition (by simp [partition])).1 contextBound
      have restBefore : PartitionsBefore left rest :=
        fun partition member => ordered partition (List.mem_cons_of_mem _ member)
      obtain ⟨next, tail⟩ := ih middle _ _ head.supplies
        (restBefore.mono head.scheduledMonotone)
        (fun key member => Nat.lt_of_lt_of_le (contextBound key member) head.scheduledMonotone)
      rw [partitions_prefix rest restBefore.below head.compatible,
        context_prefix context contextBound head.compatible] at tail
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
      refine ⟨ResultRefines.refl _, .combine ?_ tail.completion.2⟩
      rw [← ownersMapped]
      exact WorkRefines.executionGroup head.completion.1
        (head.completion.2.rekey
          (fun key member => tail.compatible key (head.bounded key member)))

-----------------------------------------------------------------------------------------
-- Original execution-plan branches consume the same constructed field witnesses
-----------------------------------------------------------------------------------------

theorem plan_run_of_fields (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : FieldScopeRunConstruction schema resolvers variables fuel)
    : PlanRunConstruction schema resolvers variables fuel := by
  intro parentType source newUsages original path usages context keys left right supplies
    initialBefore deferredBefore usageBound contextBound
  obtain ⟨middle, head⟩ := children parentType source original.collectedFieldsMap path usages
    (getNewDeferMap newUsages path context) keys left right supplies initialBefore
    usageBound contextBound
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
  · obtain ⟨next, tail⟩ := collectExecutionGroups_run_of_fields schema resolvers variables fuel
      children parentType source original.newCollectedFieldsMaps path
      (getNewDeferMap newUsages path context) middle _ _ head.supplies
      (deferredBefore.mono head.scheduledMonotone)
      (fun key member => Nat.lt_of_lt_of_le (contextBound key member) head.scheduledMonotone)
    rw [partitions_prefix _ deferredBefore.below head.compatible,
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
        (head.completion.2.rekey (fun key member => tail.compatible key (head.bounded key member)))
        tail.completion.2⟩
      simpa only [cutOutcome, eagerOutcome] using head.completion.1

-----------------------------------------------------------------------------------------
-- Actual object collection derives ordered metadata before invoking a recursive plan
-----------------------------------------------------------------------------------------

theorem object_run_of_plan (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : PlanRunConstruction schema resolvers variables fuel)
    (parentType runtimeType : Name) (reference : ObjectRef) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (keys : Nat → Nat) (left right : Nat) (supplies : SupplyMap keys left right)
    (inherited : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeValue schema resolvers variables (fuel + 1)
              (.named parentType) fields (.object runtimeType reference) path usages
              context allowStream).run
            left)
          ((Execution.completeValue schema resolvers variables (fuel + 1)
              (.named parentType) (fields.map (field keys))
              (.object runtimeType reference) path (usages.map keys)
              (context.map (fragment keys)) allowStream).run
            right) := by
  cases includes : schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      exact ⟨
        keys,
        by
          simpa only [ScheduledExecution.completeValue, Execution.completeValue, includes,
            Bool.not_false, ↓reduceIte, Completion.error]
            using pureResult_run supplies (.error 1)
      ⟩
  | true =>
      let collected := (collectSubfields schema variables runtimeType
        (.object runtimeType reference) fields).run left
      have collectedKeys := collectSubfields_refs schema variables runtimeType
        (.object runtimeType reference) fields left inherited
      have plannedBefore := build_plan_before collected.1.collectedFieldsMap usages collectedKeys.2.1
      have afterContext : ∀ key ∈ (getNewDeferMap collected.1.newDeferUsages path context).flatMap
          RefRoles.fragmentRefs, key < collected.2 :=
        mapRefs_new_bound context collected.1.newDeferUsages path collected.2
          (fun key member => Nat.lt_of_lt_of_le (contextBound key member) collectedKeys.1)
          (fun usage member => (collectedKeys.2.2 usage member).2.1)
      obtain ⟨next, planned⟩ := children runtimeType (.object runtimeType reference)
        collected.1.newDeferUsages (buildExecutionPlan collected.1.collectedFieldsMap usages)
        path usages context keys collected.2 (keys collected.2)
        (supplies.advance collectedKeys.1) plannedBefore.1 plannedBefore.2
        (fun key member => Nat.lt_of_lt_of_le (usageBound key member) collectedKeys.1) afterContext
      have collectedMapped := collectSubfields_maps keys schema variables runtimeType
        (.object runtimeType reference) fields left supplies.fresh
      rw [supplies.boundary] at collectedMapped
      simp only [ScheduledExecution.completeValue, Execution.completeValue, includes,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, run_bind, collectedMapped,
        collection, build_plan supplies.injective, StateT.run_pure, id_pure_eq]
      have caught := planned.catchNull ResponseValue.object
      refine ⟨next, ⟨?_, caught.supplies,
        Nat.le_trans collectedKeys.1 caught.scheduledMonotone,
        Nat.le_trans (supplies.orderedBoundary collectedKeys.1) caught.eagerMonotone,
        caught.bounded, caught.completion⟩⟩
      intro key earlier
      exact caught.compatible key (Nat.lt_of_lt_of_le earlier collectedKeys.1)

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
