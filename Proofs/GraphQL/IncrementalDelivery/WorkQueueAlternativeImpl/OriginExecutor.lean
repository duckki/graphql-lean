import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginAnnotations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledExecutor

/-! The actual recursive sibling-cut executor with primitive-origin annotations.
Only primitive failure branches mint references; parents keep child references.
Call routes do not use delivery keys or response paths. Separate recursive siblings
therefore remain distinct even for aliases, repeated list values and shared owners.
Erasure to the unchanged ScheduledExecution policy is proved separately. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution

namespace RecordedExecution

mutual
  def executeCollectedFields (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      : StateM Nat (RecordedCompletion (List (Name × ResponseValue))) := do
    match fields with
    | [] => return .pure []
    | (name, group) :: rest =>
        let head ←
          executeResponseField schema resolvers variables fuel parentType source
            name group path usages context (route ++ [0])
        match head.report.outcome with
        | .error _ => return head
        | .ok _ =>
            let tail ←
              executeCollectedFields schema resolvers variables fuel parentType
                source rest path usages context (route ++ [1])
            return RecordedCompletion.combine List.append head tail
  termination_by (fuel, 4, 0, sizeOf fields)

  def executeResponseField (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (name : Name) (fields : List FieldDetails)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (route : List Nat)
      : StateM Nat (RecordedCompletion (List (Name × ResponseValue))) := do
    match fuel, fields with
    | 0, _ | _, [] => return .fault route (.error 1)
    | fuel + 1, field :: _ =>
        match schema.lookupField parentType field.fieldName with
        | none => return .fault route (.error 1)
        | some definition =>
            let failed :=
              RecordedCompletion.fault route
                (singleFieldResult name (handleFieldError definition.outputType))
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
                        usages context true (route ++ [0])
                    return completed.map (fun value => [(name, value)])
  termination_by (fuel, 3, 0, sizeOf fields)

  def completeValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (fields : List FieldDetails) (value : ResolverValue ObjectRef)
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      (route : List Nat)
      : StateM Nat (RecordedCompletion ResponseValue) := do
    match fuel, fieldType, value with
    | 0, _, _ => return .fault route (.error 1)
    | fuel, .nonNull inner, value =>
        return (← completeValue schema resolvers variables fuel inner fields value path
                    usages context allowStream (route ++ [0])).nonNull
          route
    | _ + 1, _, .null => return .pure .null
    | _ + 1, .named typeName, .scalar scalar =>
        if (TypeRef.named typeName).isCompositeBool schema then
          return .fault route (.error 1)
        return .pure (.scalar scalar)
    | fuel + 1, .named parentType, source@(.object runtimeType _) =>
        if !schema.typeIncludesObjectBool parentType runtimeType then
          return .fault route (.error 1)
        let collection ← collectSubfields schema variables runtimeType source fields
        let plan := buildExecutionPlan collection.collectedFieldsMap usages
        let completed ←
          executeExecutionPlan schema resolvers variables fuel runtimeType
            source collection.newDeferUsages plan path usages context (route ++ [0])
        return completed.catchNull ResponseValue.object
    | fuel + 1, .list inner, .list values =>
        completeListValueWithStream schema resolvers variables fuel inner fields values
          path usages context allowStream (route ++ [0])
    | _ + 1, _, _ => return .fault route (.error 1)
  termination_by (fuel, 1, sizeOf fieldType, 0)

  def completeListValue (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
      (route : List Nat)
      : StateM Nat (RecordedCompletion (List ResponseValue)) := do
    match values with
    | [] => return .pure []
    | value :: rest =>
        let head ←
          completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) usages context false (route ++ [0])
        match head.report.outcome with
        | .error _ => return head.map (fun value => [value])
        | .ok _ =>
            let tail ←
              completeListValue schema resolvers variables fuel itemType fields
                rest path (index + 1) usages context (route ++ [1])
            return RecordedCompletion.combine List.cons head tail
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)

  def completeListValueWithStream (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (inner : TypeRef)
      (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
      (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
      (route : List Nat)
      : StateM Nat (RecordedCompletion ResponseValue) := do
    let streamUsage :=
      if allowStream then
        getStreamUsage variables (fields.head?.map FieldDetails.directives |>.getD [])
      else
        .ok none
    match streamUsage with
    | .error errors => return .fault route (.ok (.null, errors))
    | .ok none =>
        return (← completeListValue schema resolvers variables fuel inner fields values
                    path 0 usages context (route ++ [0])).catchNull
          ResponseValue.list
    | .ok (some usage) =>
        let initial ←
          completeListValue schema resolvers variables fuel inner fields
            (values.take usage.initialCount) path 0 usages context (route ++ [0])
        match initial.report.outcome with
        | .error _ => return initial.catchNull ResponseValue.list
        | .ok _ =>
            let remaining := values.drop usage.initialCount
            if values.length < usage.initialCount then
              return initial.catchNull ResponseValue.list
            let key ← freshNodeRef
            let streamFields :=
              fields.map (fun field => { field with deferUsage := none })
            let items ←
              completeStreamItems schema resolvers variables fuel inner
                streamFields remaining path usage.initialCount (route ++ [1])
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
      (path : ResponsePath) (index : Nat) (route : List Nat)
      : StateM Nat (List (Report ResponseValue × RecordedWork)) := do
    match values with
    | [] => return []
    | value :: rest =>
        let head ←
          completeValue schema resolvers variables fuel itemType fields value
            (path ++ [.index index]) [] [] false (route ++ [0])
        match head.report.outcome with
        | .error _ => return [(head.report, .empty)]
        | .ok _ =>
            let tail ←
              completeStreamItems schema resolvers variables fuel itemType
                fields rest path (index + 1) (route ++ [1])
            return (head.report, head.work) :: tail
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)

  def executeExecutionPlan (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef) (newUsages : List DeferUsage)
      (plan : ExecutionPlan) (path : ResponsePath) (usages : List Nat)
      (context : DeferMap) (route : List Nat)
      : StateM Nat (RecordedCompletion (List (Name × ResponseValue))) := do
    let newMap := getNewDeferMap newUsages path context
    let initial ←
      executeCollectedFields schema resolvers variables fuel parentType source
        plan.collectedFieldsMap path usages newMap (route ++ [0])
    match initial.report.outcome with
    | .error _ => return initial
    | .ok _ =>
        let tasks ←
          collectExecutionGroups schema resolvers variables fuel parentType source
            plan.newCollectedFieldsMaps path newMap (route ++ [1])
        return { initial with work := .combine initial.work tasks }
  termination_by (fuel, 6, 0, 0)

  def collectExecutionGroups (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (parentType : Name)
      (source : ResolverValue ObjectRef)
      (partitions : List (List Nat × CollectedFieldsMap)) (path : ResponsePath)
      (context : DeferMap) (route : List Nat)
      : StateM Nat RecordedWork := do
    match partitions with
    | [] => return .empty
    | (usages, fields) :: rest =>
        let groups := usages.filterMap (lookupDeferredFragment? context)
        let completed ←
          executeCollectedFields schema resolvers variables fuel parentType
            source fields path usages context (route ++ [0])
        let tail ←
          collectExecutionGroups schema resolvers variables fuel parentType source
            rest path context (route ++ [1])
        return .combine (.executionGroup groups path completed.report completed.work) tail
  termination_by (fuel, 5, 0, sizeOf partitions)
end

-- Evaluate overlapping null/non-null branches without conditional branch equations.
attribute [cbv_eval] completeValue.eq_def

def executeRootSelectionSetCore (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection)
    (route : List Nat := [])
    : StateM Nat (RecordedCompletion (List (Name × ResponseValue))) := do
  let collected ← collectFields schema variables parentType source selections
  executeExecutionPlan schema resolvers variables fuel parentType source
    collected.newDeferUsages (buildExecutionPlan collected.collectedFieldsMap []) [] [] []
    route

end RecordedExecution

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
