import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CutFieldComposition

/-! Defer-group, plan and object cut derivations. Original collection and
planning derive the input metadata laws. Every deferred task retains its own report,
including a failed task; a task failure does not skip subsequent partitions. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open ScheduledWork KeyRenaming

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

theorem groups_cuts_of_fields (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : FieldCutConstruction schema resolvers variables fuel)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
    (context : DeferMap) (route : List Nat) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right) (ordered : PartitionsBefore left partitions)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : WorkCutTrace
        ((RecordedExecution.collectExecutionGroups schema resolvers variables fuel
            parentType source partitions path context route).run
          left).1
        ((EagerRecordedExecution.collectExecutionGroups schema resolvers variables fuel
            parentType source (KeyRenaming.partitions keys partitions) path
            (context.map (fragment keys)) route).run
          right).1 := by
  induction partitions generalizing route keys left right with
  | nil =>
      simpa only [RecordedExecution.collectExecutionGroups, EagerRecordedExecution.collectExecutionGroups,
        KeyRenaming.partitions, List.map_nil, StateT.run_pure, id_pure_eq] using WorkCutTrace.empty
  | cons partition rest ih =>
      obtain ⟨usages, fields⟩ := partition
      have head := children parentType source fields path usages context (route ++ [0]) keys left right
        supplies (ordered (usages, fields) (by simp)).2 (ordered (usages, fields) (by simp)).1 contextBound
      obtain ⟨middle, mapped⟩ := fields_mapped_run schema resolvers variables fuel parentType source fields
        path usages context (route ++ [0]) keys left right supplies (ordered (usages, fields) (by simp)).2
        (ordered (usages, fields) (by simp)).1 contextBound
      dsimp only [eraseCompletionRun] at mapped
      have restBefore : PartitionsBefore left rest :=
        fun partition member => ordered partition (List.mem_cons_of_mem _ member)
      have tail := ih (route ++ [1]) middle _ _ mapped.supplies
        (restBefore.mono mapped.scheduledMonotone)
        (fun key member => Nat.lt_of_lt_of_le (contextBound key member) mapped.scheduledMonotone)
      rw [partitions_prefix rest restBefore.below mapped.compatible,
        context_prefix context contextBound mapped.compatible] at tail
      simpa only [RecordedExecution.collectExecutionGroups,
        EagerRecordedExecution.collectExecutionGroups, KeyRenaming.partitions,
        List.map_cons, run_bind, StateT.run_pure, id_pure_eq]
        using WorkCutTrace.combine (WorkCutTrace.executionGroup head.1 head.2) tail

theorem plan_cuts_of_fields (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : FieldCutConstruction schema resolvers variables fuel)
    : PlanCutConstruction schema resolvers variables fuel := by
  intro parentType source newUsages original path usages context route keys left right supplies
    initialBefore deferredBefore usageBound contextBound
  have head := children parentType source original.collectedFieldsMap path usages
    (getNewDeferMap newUsages path context) (route ++ [0]) keys left right supplies initialBefore
    usageBound contextBound
  obtain ⟨middle, mapped⟩ := fields_mapped_run schema resolvers variables fuel parentType source
    original.collectedFieldsMap path usages (getNewDeferMap newUsages path context) (route ++ [0])
    keys left right supplies initialBefore usageBound contextBound
  dsimp only [eraseCompletionRun] at mapped
  have same := head.1.refines.1.1
  simp only [RecordedExecution.executeExecutionPlan, EagerRecordedExecution.executeExecutionPlan,
    plan, new_defer_map supplies.injective, run_bind]
  cases outcome : ((RecordedExecution.executeCollectedFields schema resolvers variables fuel parentType source
      original.collectedFieldsMap path usages (getNewDeferMap newUsages path context) (route ++ [0])).run
      left).1.report.outcome
  <;> cases eagerOutcome : ((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel
      parentType source (KeyRenaming.fields keys original.collectedFieldsMap) path (usages.map keys)
      ((getNewDeferMap newUsages path context).map (fragment keys)) (route ++ [0])).run right).1.report.outcome
  <;> simp only [ScheduledErrors.SameData, outcome, eagerOutcome] at same
  · simpa only [StateT.run_pure, id_pure_eq] using head
  · have tail := groups_cuts_of_fields schema resolvers variables fuel children parentType source
      original.newCollectedFieldsMaps path (getNewDeferMap newUsages path context) (route ++ [1])
      middle _ _ mapped.supplies (deferredBefore.mono mapped.scheduledMonotone)
      (fun key member => Nat.lt_of_lt_of_le (contextBound key member) mapped.scheduledMonotone)
    rw [partitions_prefix _ deferredBefore.below mapped.compatible,
      context_prefix _ contextBound mapped.compatible] at tail
    simp only [run_bind, StateT.run_pure, id_pure_eq, CompletionCutTrace]
    exact ⟨head.1, .combine head.2 tail⟩

theorem object_cuts_of_plan (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    (children : PlanCutConstruction schema resolvers variables fuel)
    (parentType runtimeType : Name) (reference : ObjectRef) (fields : List FieldDetails)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (route : List Nat) (keys : Nat → Nat) (left right : Nat)
    (supplies : SupplyMap keys left right)
    (inherited : ∀ details ∈ fields, UsageBefore left details.deferUsage)
    (usageBound : ∀ key ∈ usages, key < left)
    (contextBound : ∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    : CompletionCutTrace
        ((RecordedExecution.completeValue schema resolvers variables (fuel + 1)
            (.named parentType) fields (.object runtimeType reference) path usages context
            allowStream route).run
          left).1
        ((EagerRecordedExecution.completeValue schema resolvers variables (fuel + 1)
            (.named parentType) (fields.map (field keys)) (.object runtimeType reference)
            path (usages.map keys) (context.map (fragment keys)) allowStream route).run
          right).1 := by
  cases includes : schema.typeIncludesObjectBool parentType runtimeType with
  | false =>
      simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
        includes, Bool.not_false, ↓reduceIte, StateT.run_pure, id_pure_eq]
        using CompletionCutTrace.fault route (.error 1)
  | true =>
      let collected := (collectSubfields schema variables runtimeType (.object runtimeType reference)
        fields).run left
      have collectedKeys := collectSubfields_refs schema variables runtimeType (.object runtimeType reference)
        fields left inherited
      have plannedBefore := build_plan_before collected.1.collectedFieldsMap usages collectedKeys.2.1
      have afterContext : ∀ key ∈ (getNewDeferMap collected.1.newDeferUsages path context).flatMap
          RefRoles.fragmentRefs, key < collected.2 :=
        mapRefs_new_bound context collected.1.newDeferUsages path collected.2
          (fun key member => Nat.lt_of_lt_of_le (contextBound key member) collectedKeys.1)
          (fun usage member => (collectedKeys.2.2 usage member).2.1)
      have child := children runtimeType (.object runtimeType reference) collected.1.newDeferUsages
        (buildExecutionPlan collected.1.collectedFieldsMap usages) path usages context (route ++ [0])
        keys collected.2 (keys collected.2) (supplies.advance collectedKeys.1)
        plannedBefore.1 plannedBefore.2
        (fun key member => Nat.lt_of_lt_of_le (usageBound key member) collectedKeys.1) afterContext
      have collectedMapped := collectSubfields_maps keys schema variables runtimeType
        (.object runtimeType reference) fields left supplies.fresh
      rw [supplies.boundary] at collectedMapped
      simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
        includes, Bool.not_true, Bool.false_eq_true, ↓reduceIte, run_bind,
        collectedMapped, collection, build_plan supplies.injective, StateT.run_pure,
        id_pure_eq]
        using child.catchNull ResponseValue.object

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
