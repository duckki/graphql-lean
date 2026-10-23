import Proofs.GraphQL.IncrementalDelivery.Semantics.SharedAncestorCollection
import Proofs.GraphQL.IncrementalDelivery.Semantics.FieldExecution
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.CollectedForestPlanning

/-! Proof-only execution target for constructed forest planning plus shared ancestry.
Every object/root boundary uses the optimized planner; deferred groups and list/stream
items recursively use this same executor.
The field-head factorization is the existing `executeCollectedFields_eq` decomposition;
all other branches mirror public execution. This is not a second public executor. -/

namespace GraphQL.IncrementalDelivery.Semantics.PlannerExecution

open GraphQL.IncrementalDelivery.Execution
open SharedAncestorConstruction

mutual
  def executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap)
      : StateM Nat (Completion (List (Name × ResponseValue))) := do
    match fields with
    | [] => return .pure []
    | (name, group) :: rest =>
        let head ←
          executeResponseField schema resolvers variables fuel parentType source
            name group path usages context
        let tail ←
          executeCollectedFields schema resolvers variables fuel parentType source
            rest path usages context
        return Completion.combine List.append head tail
  termination_by (fuel, 4, 0, sizeOf fields)

  def executeResponseField (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap)
      : StateM Nat (Completion (List (Name × ResponseValue))) := do
    match fuel, fields with
    | 0, _ | _, [] => return .error 1
    | fuel + 1, field :: _ =>
        match schema.lookupField parentType field.fieldName with
        | none => return .error 1
        | some definition =>
            let failed : Completion (List (Name × ResponseValue)) :=
              {
                result := singleFieldResult name (handleFieldError definition.outputType),
                cause := if definition.outputType.isNonNull then some 1 else none
              }
            match coerceArgumentValues schema variables definition.arguments
                    field.arguments with
            | .error => return failed
            | .success arguments =>
                match resolveFieldValue resolvers parentType field.fieldName arguments
                        source with
                | none => return failed
                | some resolved =>
                    let completed ←
                      completeValue schema resolvers variables fuel
                        definition.outputType fields resolved (path ++ [.field name])
                        usages context true
                    return completed.map (fun value => [(name, value)])
  termination_by (fuel, 3, 0, sizeOf fields)

  def completeValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      : StateM Nat (Completion ResponseValue) := do
    match fuel, fieldType, value with
    | 0, _, _ => return .error 1
    | fuel, .nonNull inner, value =>
        return (← completeValue schema resolvers variables fuel inner fields value path
                    usages context allowStream).nonNull
    | _ + 1, _, .null => return .pure .null
    | _ + 1, .named typeName, .scalar scalar =>
        if (TypeRef.named typeName).isCompositeBool schema then return .error 1
        return .pure (.scalar scalar)
    | fuel + 1, .named parentType, source@(.object runtimeType _) =>
        if !schema.typeIncludesObjectBool parentType runtimeType then return .error 1
        let collection ← collectSubfields schema variables runtimeType source fields
        let plan :=
          AlternativeWorkQueue.NativeRefinement.CollectedForestPlanning.buildPlan
            collection.collectedFieldsMap usages
        let completed ←
          executeExecutionPlan schema resolvers variables fuel runtimeType
            source collection.newDeferUsages plan path usages context
        return completed.catchNull ResponseValue.object
    | fuel + 1, .list inner, .list values =>
        completeListValueWithStream schema resolvers variables fuel inner fields values
          path usages context allowStream
    | _ + 1, _, _ => return .error 1
  termination_by (fuel, 1, sizeOf fieldType, 0)

  def completeListValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      : StateM Nat (Completion (List ResponseValue)) := do
    match values with
    | [] => return .pure []
    | value :: rest =>
        let head ←
          completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages context false
        let tail ←
          completeListValue schema resolvers variables fuel itemType fields rest
            path (index + 1) usages context
        return Completion.combine List.cons head tail
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)

  def completeListValueWithStream (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (inner : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      : StateM Nat (Completion ResponseValue) := do
    let streamUsage :=
      if allowStream then
        getStreamUsage variables (fields.head?.map FieldDetails.directives |>.getD [])
      else
        .ok none
    match streamUsage with
    | .error errors => return { result := .ok (.null, errors), cause := some errors }
    | .ok none =>
        return (← completeListValue schema resolvers variables fuel inner fields values
                    path 0 usages context).catchNull
          ResponseValue.list
    | .ok (some usage) =>
        let initial ←
          completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages context
        match initial.result with
        | .error _ => return initial.catchNull ResponseValue.list
        | .ok _ =>
            let remaining := values.drop usage.initialCount
            if values.length < usage.initialCount then
              return initial.catchNull ResponseValue.list
            let key ← freshNodeRef
            let streamFields :=
              fields.map (fun field => { field with deferUsage := none })
            let items ←
              completeStreamItems schema resolvers variables fuel inner streamFields
                remaining path usage.initialCount
            let completed := initial.catchNull ResponseValue.list
            return {
              completed with
                work :=
                  .combine completed.work
                    (.stream { ref := key, path, label := usage.label } items)
            }
  termination_by (fuel, 3, 0, 0)

  def completeStreamItems (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat)
      : StateM Nat (List (TaskOutcome ResponseValue × Work)) := do
    match values with
    | [] => return []
    | value :: rest =>
        let head ←
          completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) [] [] false
        match head.result with
        | .error _ => return [(head.outcome, .empty)]
        | .ok _ =>
            let tail ←
              completeStreamItems schema resolvers variables fuel itemType fields rest
                path (index + 1)
            return (head.outcome, head.work) :: tail
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)

  def executeExecutionPlan (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (newUsages : List DeferUsage)
      (plan : ExecutionPlan) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap)
      : StateM Nat (Completion (List (Name × ResponseValue))) := do
    let newMap := getNewDeferMapShared newUsages path context
    let initial ←
      executeCollectedFields schema resolvers variables fuel parentType source
        plan.collectedFieldsMap path usages newMap
    match initial.result with
    | .error _ => return initial
    | .ok _ =>
        let tasks ←
          collectExecutionGroups schema resolvers variables fuel parentType source
            plan.newCollectedFieldsMaps path newMap
        let declarations :=
          newUsages.filterMap (fun usage => lookupDeferredFragment? newMap usage.ref)
        return {
          initial with
            work := .combine initial.work (.declareGroups declarations tasks)
        }
  termination_by (fuel, 6, 0, 0)

  def collectExecutionGroups (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (context : DeferMap)
      : StateM Nat Work := do
    match partitions with
    | [] => return .empty
    | (usages, fields) :: rest =>
        let groups := usages.filterMap (lookupDeferredFragment? context)
        let completed ←
          executeCollectedFields schema resolvers variables fuel parentType
            source fields path usages context
        let tail ←
          collectExecutionGroups schema resolvers variables fuel parentType source
            rest path context
        return .combine (.executionGroup groups path completed.outcome completed.work)
          tail
  termination_by (fuel, 5, 0, sizeOf partitions)
end

-- Evaluate overlapping null/non-null branches without conditional branch equations.
attribute [cbv_eval] completeValue.eq_def

def executeRootSelectionSetCore (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    : StateM Nat (Completion (List (Name × ResponseValue))) := do
  let collected ← collectFields schema variables parentType source selections
  executeExecutionPlan schema resolvers variables fuel parentType source
    collected.newDeferUsages
    (AlternativeWorkQueue.NativeRefinement.CollectedForestPlanning.buildPlan
      collected.collectedFieldsMap []) [] [] []

end GraphQL.IncrementalDelivery.Semantics.PlannerExecution
