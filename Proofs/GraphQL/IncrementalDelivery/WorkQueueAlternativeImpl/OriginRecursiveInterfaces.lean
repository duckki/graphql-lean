import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginMappedRuns

/-! Exact recursive origin-coverage nodes. Premises describe allocated input
metadata and compatible supplies, never desired outputs or originating references.
Each node compares the two actual annotated executions at the same structural route. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork KeyRenaming

def ValueOriginsConstruction (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ fieldType fields (source : ResolverValue ObjectRef) path usages context allowStream
    route keys left right,
    SupplyMap keys left right
    → (∀ details ∈ fields, UsageBefore left details.deferUsage)
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    → CompletionOriginsRefine
        ((RecordedExecution.completeValue schema resolvers variables fuel fieldType fields
            source path usages context allowStream route).run
          left).1
        ((EagerRecordedExecution.completeValue schema resolvers variables fuel fieldType
            (fields.map (field keys)) source path (usages.map keys)
            (context.map (fragment keys)) allowStream route).run
          right).1

theorem valueOrigins_zero (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues)
    : ValueOriginsConstruction schema resolvers variables 0 := by
  intro fieldType fields source path usages context allowStream route keys left right supplies ordered
    usageBound contextBound
  simpa only [RecordedExecution.completeValue, EagerRecordedExecution.completeValue,
    StateT.run_pure, id_pure_eq] using CompletionOriginsRefine.fault route (.error 1)

def FieldOriginsConstruction (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ parentType (source : ResolverValue ObjectRef) fields path usages context route keys
    left right,
    SupplyMap keys left right
    → FieldsBefore left fields
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ context.flatMap RefRoles.fragmentRefs, key < left)
    → CompletionOriginsRefine
        ((RecordedExecution.executeCollectedFields schema resolvers variables fuel
            parentType source fields path usages context route).run
          left).1
        ((EagerRecordedExecution.executeCollectedFields schema resolvers variables fuel
            parentType source (KeyRenaming.fields keys fields) path (usages.map keys)
            (context.map (fragment keys)) route).run
          right).1

def PlanOriginsConstruction (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat)
    : Prop :=
  ∀ parentType (source : ResolverValue ObjectRef) newUsages original path usages context
    route keys left right,
    SupplyMap keys left right
    → FieldsBefore left original.collectedFieldsMap
    → PartitionsBefore left original.newCollectedFieldsMaps
    → (∀ key ∈ usages, key < left)
    → (∀ key ∈ (getNewDeferMap newUsages path context).flatMap RefRoles.fragmentRefs,
        key < left)
    → CompletionOriginsRefine
        ((RecordedExecution.executeExecutionPlan schema resolvers variables fuel
            parentType source newUsages original path usages context route).run
          left).1
        ((EagerRecordedExecution.executeExecutionPlan schema resolvers variables fuel
            parentType source (newUsages.map (usage keys)) (plan keys original) path
            (usages.map keys) (context.map (fragment keys)) route).run
          right).1

theorem fieldDetails_prefix {before after : Nat → Nat} {bound : Nat}
    (fields : List FieldDetails)
    (ordered : ∀ details ∈ fields, UsageBefore bound details.deferUsage)
    (same : ∀ key < bound, after key = before key)
    : fields.map (field after) = fields.map (field before) :=
  List.map_congr_left
    (fun details member =>
      field_congr details
        (fun key inField =>
          same key (usageBefore_fieldKeys details (ordered details member) key inField)))

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
