import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Slots

/-!
Scope scheduling and one-step execution facts for the breadth executor.

`scheduleScope` handles one concrete object scope. It collects field groups, enqueues one
segment per collected group, and emits a `TraceFrame.scope` that records only the field
keys needed during reverse completion.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

theorem scope_scheduleScope_eq_of_collectFieldsByKey
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (queue : ScheduleQueue ObjectRef)
    : collectFieldsByKey schema variableValues parentType selectionSet = groups
      -> scheduleScope schema variableValues parentType sources selectionSet queue
          = let keyedGroups :=
              groups.map
                (fun group =>
                  (scheduleKeyForFields parentType group.fst group.snd, group.snd))
            let queue :=
              keyedGroups.foldl
                (fun queue group =>
                  let segment :=
                    {
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                  enqueueSegment group.fst segment queue)
                queue
            let fieldKeys := keyedGroups.map Prod.fst
            (queue, .scope [sources.length] fieldKeys) := by
  intro hgroups
  simp [scheduleScope, hgroups]

theorem scope_scheduleScope_empty_groups
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (selectionSet : List Selection)
    (queue : ScheduleQueue ObjectRef)
    : collectFieldsByKey schema variableValues parentType selectionSet = []
      -> scheduleScope schema variableValues parentType sources selectionSet queue
          = (queue, .scope [sources.length] []) := by
  intro hgroups
  simp [scheduleScope, hgroups]

theorem scope_schedulePendingChildWork_nil
    (schema : Schema) (variableValues : VariableValues)
    (queue : ScheduleQueue ObjectRef)
    : schedulePendingChildWork schema variableValues
        ([] : PendingChildWorkList ObjectRef) queue
      = (queue, []) := by
  rfl

theorem scope_schedulePendingChildWork_cons
    (schema : Schema) (variableValues : VariableValues)
    (work : PendingChildWork ObjectRef)
    (rest : PendingChildWorkList ObjectRef)
    (queue : ScheduleQueue ObjectRef)
    : schedulePendingChildWork schema variableValues (work :: rest) queue
      = let head :=
          scheduleScope schema variableValues work.runtimeType
            [work.source] work.selectionSet queue
        let tail := schedulePendingChildWork schema variableValues rest head.fst
        (tail.fst, head.snd :: tail.snd) := by
  rfl

theorem scope_executeScheduleItem_lookup_none
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues) (item : ScheduleItem ObjectRef)
    : schema.lookupField item.key.parentType item.key.fieldName = none
      -> executeScheduleItem schema resolvers variableValues item
          = (
            [],
            [.field item.key (.named "") item.segmentLengths
              (List.replicate item.sources.length (.completed (.error 1)))]
          ) := by
  intro hlookup
  simp [executeScheduleItem, hlookup]

theorem scope_executeScheduleItem_result_count_mismatch
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues) (item : ScheduleItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> ((resolvers.resolve item.key.parentType item.key.fieldName
              (coerceArgumentValues schema variableValues fieldDefinition.arguments
                item.key.arguments) item.sources).length
            == item.sources.length)
          = false
      -> executeScheduleItem schema resolvers variableValues item
          = (
            [],
            [.field item.key fieldDefinition.outputType item.segmentLengths
              (List.replicate item.sources.length
                (.completed (handleFieldError fieldDefinition.outputType)))]
          ) := by
  intro hlookup hlength
  simp [executeScheduleItem, hlookup, hlength]

theorem scope_executeScheduleItem_fromSpecResolvers_length_ok
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (_variableValues : VariableValues) (item : ScheduleItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> ((ResolverMap.fromSpecResolvers resolvers).resolve item.key.parentType
            item.key.fieldName item.key.arguments item.sources).length
          = item.sources.length := by
  intro _hlookup
  simp [ResolverMap.fromSpecResolvers]

theorem scope_executeScheduleItem_fromSpecResolvers_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (item : ScheduleItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> executeScheduleItem schema (ResolverMap.fromSpecResolvers resolvers)
            variableValues item
          = let resolved :=
              item.sources.map
                (fun source =>
                  GraphQL.Execution.resolveFieldValue schema resolvers variableValues
                    fieldDefinition item.key.parentType item.key.fieldName
                    item.key.arguments source)
            let built :=
              buildFieldSlots schema fieldDefinition.outputType item.segments resolved
            let scheduled := schedulePendingChildWork schema variableValues built.fst []
            (
              scheduled.fst,
              .field item.key fieldDefinition.outputType item.segmentLengths built.snd
              :: scheduled.snd
            ) := by
  intro hlookup
  simp [executeScheduleItem, GraphQL.Execution.resolveFieldValue, hlookup,
    ResolverMap.fromSpecResolvers]

theorem scope_expectedChildQueueForItem_fromSpecResolvers_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemFuelsAligned item
      -> expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item
      -> expectedScheduleQueueToQueue
            (expectedChildQueueForItem schema resolvers variableValues item).fst
          = (executeScheduleItem schema (ResolverMap.fromSpecResolvers resolvers)
              variableValues item.toScheduleItem).fst := by
  intro hlookup haligned hready
  rw [scope_executeScheduleItem_fromSpecResolvers_lookup_some
    (ObjectRef := ObjectRef) schema resolvers variableValues item.toScheduleItem
    fieldDefinition hlookup]
  simp [expectedChildQueueForItem, hlookup]
  rw [expectedScheduleQueueToQueue_scheduleExpectedPendingChildWork]
  rw [slots_expectedPendingChildWorkForItem_toPending_eq_buildFieldSlots
    (ObjectRef := ObjectRef) schema resolvers variableValues fieldDefinition.outputType
    item haligned hready]
  simp [GraphQL.Execution.resolveFieldValueByName, hlookup,
    ExpectedQueueItem.toScheduleItem, expectedScheduleQueueToQueue]

theorem scope_expectedChildQueueForItem_frames_fromSpecResolvers_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (item : ExpectedQueueItem ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemFuelsAligned item
      -> expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item
      -> (expectedChildQueueForItem schema resolvers variableValues item).snd
          = let resolved :=
              item.toScheduleItem.sources.map
                (fun source =>
                  GraphQL.Execution.resolveFieldValue schema resolvers variableValues
                    fieldDefinition item.key.parentType item.key.fieldName
                    item.key.arguments source)
            let built :=
              buildFieldSlots schema fieldDefinition.outputType
                item.toScheduleItem.segments resolved
            (schedulePendingChildWork schema variableValues built.fst []).snd := by
  intro hlookup haligned hready
  simp [expectedChildQueueForItem, hlookup]
  rw [scheduleExpectedPendingChildWork_frames]
  rw [slots_expectedPendingChildWorkForItem_toPending_eq_buildFieldSlots
    (ObjectRef := ObjectRef) schema resolvers variableValues fieldDefinition.outputType
    item haligned hready]
  simp [GraphQL.Execution.resolveFieldValueByName, hlookup,
    ExpectedQueueItem.toScheduleItem, expectedScheduleQueueToQueue]

end ExecutionBreadth

end Algorithms

end GraphQL
