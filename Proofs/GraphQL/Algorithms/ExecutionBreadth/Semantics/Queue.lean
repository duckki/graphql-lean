import Proofs.GraphQL.Execution.ArgumentCoercion
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Scope

/-!
Queue-drain and reverse-completion facts for the breadth executor.

The forward queue is deterministic: `drainLoop` always executes the head item, appends
the resulting trace fragment, and merges discovered child work back into the remaining
queue by `ScheduleKey`.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

theorem queue_outOfFuelQueueTrace_nil (schema : Schema)
    : outOfFuelQueueTrace schema ([] : ScheduleQueue ObjectRef) = [] := by
  rfl

theorem queue_drainLoop_nil
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    : drainLoop schema resolvers variableValues fuel ([] : ScheduleQueue ObjectRef)
      = [] := by
  cases fuel <;> rfl

theorem queue_drainLoop_zero
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues)
    (queue : ScheduleQueue ObjectRef)
    : drainLoop schema resolvers variableValues 0 queue
      = outOfFuelQueueTrace schema queue := by
  cases queue <;> rfl

theorem queue_drainLoop_succ
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (item : ScheduleItem ObjectRef)
    (rest : ScheduleQueue ObjectRef)
    : drainLoop schema resolvers variableValues (fuel + 1) (item :: rest)
      = let executed := executeScheduleItem schema resolvers variableValues item
        executed.snd
        ++ drainLoop schema resolvers variableValues fuel
            (enqueueScheduleItems rest executed.fst) := by
  rfl

theorem queue_completeExecutionTrace_empty
    : completeExecutionTrace [] = (.error 1 : Result (List (Name × ResponseValue))) := by
  rfl

theorem queue_completeFrames_empty (stack : CompletionStack)
    : completeFrames ([] : ExecutionTrace) stack = stack := by
  rfl

theorem queue_completeScopeFrame_eq_of_pop
    (segmentLengths : List Nat) (fieldBindings : List FieldBinding)
    (stack stack' : CompletionStack)
    (entries : List (FieldBinding × List (Result ResponseValue)))
    (fieldResults : ObjectFieldSegments)
    (objectResults : List (Result ResponseValue))
    : popFieldValuesByBindings fieldBindings stack = (entries, stack')
      -> nameFieldValueBlocks entries = fieldResults
      -> combineScopeFieldResults segmentLengths.sum fieldResults = objectResults
      -> completeScopeFrame segmentLengths fieldBindings stack
          = {
            stack' with
              valueStack :=
                (splitResultsByLengths segmentLengths objectResults).reverse
                ++ stack'.valueStack
          } := by
  intro hpop hfields hobjects
  simp [completeScopeFrame, hpop, hfields, hobjects]

theorem queue_completeFrames_append
    (left right : ExecutionTrace) (stack : CompletionStack)
    : completeFrames (left ++ right) stack
      = completeFrames right (completeFrames left stack) := by
  induction left generalizing stack with
  | nil =>
      rfl
  | cons frame rest ih =>
      cases frame with
      | field key fieldType segmentLengths slots =>
          simp [completeFrames, ih]
      | scope segmentLengths fieldKeys =>
          simp [completeFrames, ih]

theorem queue_scheduleItem_sources_length (item : ScheduleItem ObjectRef)
    : item.sources.length = item.segmentLengths.sum := by
  unfold ScheduleItem.sources ScheduleItem.segmentLengths
  induction item.segments with
  | nil =>
      rfl
  | cons segment segments ih =>
      simp [ScheduleSegment.length, ih]

theorem queue_splitResultsByLengths_replicate {α : Type} (lengths : List Nat) (value : α)
    : splitResultsByLengths lengths (List.replicate lengths.sum value)
      = lengths.map (fun length => List.replicate length value) := by
  induction lengths with
  | nil =>
      rfl
  | cons length lengths ih =>
      simp [splitResultsByLengths, ih]

theorem queue_bindFieldSegments_expectedMap
    (segments : List (ExpectedQueueSegment ObjectRef))
    (results : ExpectedQueueSegment ObjectRef -> List (Result ResponseValue))
    : bindFieldSegments
        (segments.map
          (fun segment =>
            (segment.segment.responseName, segment.segment.sources.length)))
        (segments.map results)
      = segments.map
          (fun segment =>
            (segment.segment.responseName, results segment)) := by
  induction segments with
  | nil =>
      rfl
  | cons segment segments ih =>
      simp [bindFieldSegments, ih]

theorem queue_singleFieldResultValue_singleFieldResult
    (responseName : Name) (completed : Result ResponseValue)
    : singleFieldResultValue responseName
        (GraphQL.Execution.singleFieldResult responseName completed)
      = completed := by
  cases completed with
  | error errors =>
      rfl
  | ok result =>
      cases result
      simp [singleFieldResultValue, GraphQL.Execution.singleFieldResult]

theorem queue_singleFieldResult_executeField_roundtrip
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (responseName : Name) (fields : List ExecutableField)
    : GraphQL.Execution.singleFieldResult responseName
        (singleFieldResultValue responseName
          (GraphQL.Execution.executeField schema resolvers variableValues fuel
            parentType source responseName fields))
      = GraphQL.Execution.executeField schema resolvers variableValues fuel
          parentType source responseName fields := by
  cases fields with
  | nil =>
      simp [GraphQL.Execution.executeField, singleFieldResultValue,
        GraphQL.Execution.singleFieldResult]
  | cons field fields =>
      cases fuel with
      | zero =>
          simp [GraphQL.Execution.executeField, GraphQL.Execution.outOfFuel,
            singleFieldResultValue,
            GraphQL.Execution.singleFieldResult]
      | succ fuel =>
          cases hlookup : schema.lookupField parentType field.fieldName with
          | none =>
              simp [GraphQL.Execution.executeField, hlookup, singleFieldResultValue,
                GraphQL.Execution.singleFieldResult]
          | some fieldDefinition =>
              cases hresolve
                    : GraphQL.Execution.coerceAndResolveFieldValue schema resolvers
                        variableValues fieldDefinition parentType field.fieldName
                        field.arguments source with
              | none =>
                  simp [hlookup, hresolve,
                    queue_singleFieldResultValue_singleFieldResult]
              | some resolved =>
                  simp [hlookup, hresolve,
                    queue_singleFieldResultValue_singleFieldResult]

theorem queue_fieldBindingEqBool_false_of_responseName_ne {left right : FieldBinding}
    : left.responseName ≠ right.responseName
      -> fieldBindingEqBool left right = false := by
  intro hne
  cases h : fieldBindingEqBool left right with
  | false =>
      rfl
  | true =>
      have heq : left = right :=
        fieldBindingEqBool_eq h
      exact False.elim (hne (by simp [heq]))

theorem queue_foldr_zipResultWith_singleton
    (blocks : List (Result (List (Name × ResponseValue))))
    : List.foldr
        (fun fields tail => zipResultWith (fun left right => left ++ right) fields tail)
        [(.ok ([], 0))]
        (blocks.map List.singleton)
      = [blocks.foldr
          (fun block tail => Result.combine List.append block tail)
          (.ok ([], 0))] := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      simp [ih]
      cases block <;> rfl

theorem queue_combineScopeFieldResults_singleton
    (blocks : List (Result (List (Name × ResponseValue))))
    : combineScopeFieldResults 1 (blocks.map List.singleton)
      = [objectResultFromFields
          (blocks.foldr
            (fun block tail => Result.combine List.append block tail)
            (.ok ([], 0)))] := by
  simp [combineScopeFieldResults, queue_foldr_zipResultWith_singleton,
    objectResultFromFields]

theorem queue_executeCollectedFields_eq_fieldFold
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : groups.foldr
        (fun group tail =>
          Result.combine List.append
            (GraphQL.Execution.executeField schema resolvers variableValues fuel
              parentType source group.fst group.snd)
            tail)
        (.ok ([], 0))
      = GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          fuel parentType source groups := by
  induction groups with
  | nil =>
      simp [GraphQL.Execution.executeCollectedFields]
  | cons group groups ih =>
      rw [GraphQL.Execution.executeCollectedFields]
      simp [ih]

theorem queue_combineScopeFieldResults_singleton_executeCollectedFields
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : combineScopeFieldResults 1
        (groups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues fuel
              parentType source group.fst group.snd]))
      = [objectResultFromFields
          (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel parentType source groups)] := by
  calc
    combineScopeFieldResults 1
          (groups.map
            (fun group =>
              [GraphQL.Execution.executeField schema resolvers variableValues fuel
                parentType source group.fst group.snd]))
        = [objectResultFromFields
            ((groups.map
                (fun group =>
                  GraphQL.Execution.executeField schema resolvers variableValues fuel
                    parentType source group.fst group.snd)).foldr
              (fun block tail => Result.combine List.append block tail)
              (.ok ([], 0)))] := by
      have hsingleton :
          groups.map (fun group =>
              List.singleton
                (GraphQL.Execution.executeField schema resolvers
                  variableValues fuel parentType source group.fst group.snd)) =
            groups.map (fun group =>
              [GraphQL.Execution.executeField schema resolvers
                variableValues fuel parentType source group.fst group.snd]) := by
        induction groups with
        | nil =>
            rfl
        | cons group groups ih =>
            simp [List.singleton]
      rw [← hsingleton]
      simpa [List.map_map, Function.comp_def]
        using (queue_combineScopeFieldResults_singleton
                (blocks :=
                  groups.map
                    (fun group =>
                      GraphQL.Execution.executeField schema resolvers variableValues fuel
                        parentType source group.fst group.snd)))
    _ = [objectResultFromFields
          (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel parentType source groups)] := by
      have hfoldMap :
          (groups.map (fun group =>
            GraphQL.Execution.executeField schema resolvers variableValues fuel
              parentType source group.fst group.snd)).foldr
            (fun block tail => Result.combine List.append block tail)
            (.ok ([], 0)) =
          GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel parentType source groups := by
        induction groups with
        | nil =>
            simp [GraphQL.Execution.executeCollectedFields]
        | cons group groups ih =>
            simp
            rw [ih]
            rw [GraphQL.Execution.executeCollectedFields]
      simp [hfoldMap]

theorem queue_expectedPendingChildWorkSpecResult_eq_scopeSingleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    : [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
      = combineScopeFieldResults 1
          ((collectFieldsByKey schema variableValues
              work.work.runtimeType work.work.selectionSet).map
            (fun group =>
              [GraphQL.Execution.executeField schema resolvers variableValues
                work.specFuel work.work.runtimeType work.work.source
                group.fst group.snd])) := by
  simp [expectedPendingChildWorkSpecResult]
  rw [queue_combineScopeFieldResults_singleton_executeCollectedFields
    (ObjectRef := ObjectRef) schema resolvers variableValues work.specFuel
    work.work.runtimeType work.work.source
    (collectFieldsByKey schema variableValues
      work.work.runtimeType work.work.selectionSet)]

theorem queue_expectedScheduleSegmentSpecFieldResults_lookup_none
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : schema.lookupField key.parentType key.fieldName = none
      -> expectedQueueSegmentFuelsAligned segment
      -> expectedScheduleSegmentSpecFieldResults schema resolvers variableValues key
            segment
          = List.replicate segment.segment.sources.length (.error 1) := by
  intro hlookup haligned
  cases segment with
  | mk segment specFuels =>
      simp [expectedScheduleSegmentSpecFieldResults,
        expectedQueueSegmentFuelsAligned] at haligned ⊢
      revert specFuels haligned
      induction segment.sources with
      | nil =>
          intro specFuels haligned
          cases specFuels <;> simp [expectedScheduleSegmentSpecFieldResultsWithFuels] at haligned ⊢
      | cons source sources ih =>
          intro specFuels haligned
          cases specFuels with
          | nil =>
              simp at haligned
          | cons fuel specFuels =>
              have htail : specFuels.length = sources.length := by
                simpa using haligned
              have hrep :
                  List.replicate (sources.length + 1) (.error 1 : Result ResponseValue) =
                    (.error 1 : Result ResponseValue) ::
                      List.replicate sources.length (.error 1) := by
                rw [show sources.length + 1 = Nat.succ sources.length by omega]
                rfl
              cases fuel with
              | zero =>
                  have hout :
                      singleFieldResultValue segment.responseName
                          GraphQL.Execution.outOfFuel =
                        (.error 1 : Result ResponseValue) := by
                    rfl
                  simp [expectedScheduleSegmentSpecFieldResultsWithFuels,
                    GraphQL.Execution.executeField, hrep, ih specFuels htail, hout]
              | succ fuel =>
                  simp [expectedScheduleSegmentSpecFieldResultsWithFuels,
                    GraphQL.Execution.executeField, ScheduleKey.executableField,
                    singleFieldResultValue, hlookup, hrep, ih specFuels htail]

theorem queue_expectedScheduleSegmentSpecFieldResults_lookup_none_map
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (segments : List (ExpectedQueueSegment ObjectRef))
    : schema.lookupField key.parentType key.fieldName = none
      -> (∀ segment, segment ∈ segments -> expectedQueueSegmentFuelsAligned segment)
      -> segments.map
            (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues key)
          = segments.map
              (fun segment =>
                List.replicate segment.segment.sources.length (.error 1)) := by
  intro hlookup haligned
  induction segments with
  | nil =>
      rfl
  | cons segment segments ih =>
      have hhead :
          expectedScheduleSegmentSpecFieldResults schema resolvers variableValues key segment =
            List.replicate segment.segment.sources.length (.error 1) :=
        queue_expectedScheduleSegmentSpecFieldResults_lookup_none
          schema resolvers variableValues key segment hlookup
          (haligned segment (by simp))
      have htail :
          segments.map
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues key) =
            segments.map
              (fun segment => List.replicate segment.segment.sources.length (.error 1)) :=
        ih (fun segment hmem => haligned segment (by simp [hmem]))
      simp [hhead, htail]

theorem queue_expectedScheduleSegmentSpecFieldResults_length
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (key : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    : expectedQueueSegmentFuelsAligned segment
      -> (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            key segment).length
          = segment.segment.sources.length := by
  intro haligned
  cases segment with
  | mk segment specFuels =>
      simp [expectedScheduleSegmentSpecFieldResults,
        expectedQueueSegmentFuelsAligned] at haligned ⊢
      revert specFuels haligned
      induction segment.sources with
      | nil =>
          intro specFuels haligned
          cases specFuels <;> simp [expectedScheduleSegmentSpecFieldResultsWithFuels] at haligned ⊢
      | cons source sources ih =>
          intro specFuels haligned
          cases specFuels with
          | nil =>
              simp at haligned
          | cons fuel specFuels =>
              have htail : specFuels.length = sources.length := by
                simpa using Nat.succ.inj haligned
              simp [expectedScheduleSegmentSpecFieldResultsWithFuels, ih specFuels htail]

theorem queue_completeExecutionTrace_singleton_empty_scope
    : completeExecutionTrace [.scope [1] []] = .ok ([], 0) := by
  rfl

theorem queue_executeRootSelectionSet_empty
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : executeRootSelectionSet schema resolvers variableValues fuel parentType source []
      = .ok ([], 0) := by
  simpa [executeRootSelectionSet, scheduleScope, collectFieldsByKey, drainLoop]
    using queue_completeExecutionTrace_singleton_empty_scope

theorem queue_executeRootSelectionSet_trace
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : executeRootSelectionSet schema resolvers variableValues fuel
        parentType source selectionSet
      = let scheduled :=
          scheduleScope schema variableValues parentType [source] selectionSet []
        let trace :=
          scheduled.snd :: drainLoop schema resolvers variableValues fuel scheduled.fst
        completeExecutionTrace trace := by
  rfl

theorem queue_drainLoopMatchesExpectedSpec_empty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (breadthFuel : Nat)
    : drainLoopMatchesExpectedSpec schema resolvers variableValues breadthFuel
        ([] : ExpectedScheduleQueue ObjectRef) := by
  cases breadthFuel <;> rfl

theorem queue_expectedDrainStepMatchesSpec_lookup_none
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : expectedQueueItemFuelsAligned item
      -> schema.lookupField item.key.parentType item.key.fieldName = none
      -> expectedDrainStepMatchesSpec schema resolvers variableValues item rest := by
  intro haligned hlookup
  unfold expectedDrainStepMatchesSpec
  constructor
  · simp [expectedChildQueueForItem, executeScheduleItem, hlookup,
      ExpectedQueueItem.toScheduleItem, expectedScheduleQueueToQueue]
  ·
    have hstack :
        completeSlotList (.named "")
            (List.replicate item.toScheduleItem.sources.length (.completed (.error 1)))
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              (enqueueExpectedScheduleItems rest [])) =
          ( List.replicate item.toScheduleItem.sources.length (.error 1)
          , expectedScheduleQueueCompletionStack schema resolvers variableValues
              (enqueueExpectedScheduleItems rest []) ) := by
        simpa using
          slots_completeSlotList_completed_error (.named "") 1
            item.toScheduleItem.sources.length
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              (enqueueExpectedScheduleItems rest []))
    have hsegments :
          splitResultsByLengths item.toScheduleItem.segmentLengths
              (List.replicate item.toScheduleItem.sources.length
                (.error 1 : Result ResponseValue)) =
            item.segments.map
              (fun segment =>
                List.replicate segment.segment.sources.length
                  (.error 1 : Result ResponseValue)) := by
      rw [queue_scheduleItem_sources_length (item := item.toScheduleItem)]
      simpa [ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentLengths,
        ScheduleSegment.length, Function.comp_def] using
        queue_splitResultsByLengths_replicate item.toScheduleItem.segmentLengths
          (.error 1 : Result ResponseValue)
    have hexpected :
          item.segments.map
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues item.key) =
            item.segments.map
              (fun segment => List.replicate segment.segment.sources.length (.error 1)) := by
      exact queue_expectedScheduleSegmentSpecFieldResults_lookup_none_map
        schema resolvers variableValues item.key item.segments hlookup haligned
    have hdescriptors :
        item.toScheduleItem.segmentDescriptors =
          item.segments.map (fun segment =>
            (segment.segment.responseName, segment.segment.sources.length)) := by
      simp [ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentDescriptors,
        ScheduleSegment.length, Function.comp_def]
    have hdescriptorLengths :
        item.toScheduleItem.segmentDescriptors.map Prod.snd =
          item.toScheduleItem.segmentLengths := by
      simp [ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentDescriptors,
        ScheduleItem.segmentLengths, ScheduleSegment.length, Function.comp_def]
    simp [enqueueExpectedScheduleItems, ExpectedQueueItem.toScheduleItem,
      expectedScheduleQueueCompletionStack] at hstack
    simp [expectedChildQueueForItem, executeScheduleItem, hlookup,
      ExpectedQueueItem.toScheduleItem,
      completeFrames, completeFieldFrame, expectedScheduleQueueCompletionStack,
      expectedQueueItemCompletion, ScheduleItem.segmentDescriptors,
      enqueueExpectedScheduleItems]
    rw [hstack]
    simp only [true_and]
    simp [ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentDescriptors,
      ScheduleItem.segmentLengths, ScheduleItem.sources, ScheduleSegment.length,
      Function.comp_def] at hsegments hdescriptors hdescriptorLengths ⊢
    rw [hsegments, ← hexpected]
    rw [queue_bindFieldSegments_expectedMap]

theorem queue_completeFrames_fieldFrame_expectedItem_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemFuelsAligned item
      -> expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item
      -> completeFrames
            [.field item.key fieldDefinition.outputType
              item.toScheduleItem.segmentDescriptors
              (buildFieldSlots schema fieldDefinition.outputType
                item.toScheduleItem.segments
                (item.toScheduleItem.sources.map
                  (fun source =>
                    GraphQL.Execution.coerceAndResolveFieldValue schema resolvers
                      variableValues fieldDefinition item.key.parentType
                      item.key.fieldName item.key.arguments source))).snd]
            {
              valueStack :=
                (expectedPendingChildWorkCompletionStack schema resolvers variableValues
                  (expectedPendingChildWorkForItem schema resolvers
                    fieldDefinition.outputType item variableValues)).valueStack
              fieldStore :=
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  rest).fieldStore
            }
          = expectedScheduleQueueCompletionStack schema resolvers variableValues
              (item :: rest) := by
  intro hlookup haligned hready
  let restStack :=
    expectedScheduleQueueCompletionStack schema resolvers variableValues rest
  let blocks :=
    item.segments.map
      (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
        item.key)
  have hcomplete :
      completeSlotList fieldDefinition.outputType
          (buildFieldSlots schema fieldDefinition.outputType
            item.toScheduleItem.segments
            (item.toScheduleItem.sources.map (fun source =>
              GraphQL.Execution.coerceAndResolveFieldValue schema resolvers variableValues
                fieldDefinition item.key.parentType item.key.fieldName
                item.key.arguments source))).snd
          { valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers variableValues
                (expectedPendingChildWorkForItem schema resolvers
                  fieldDefinition.outputType item variableValues)).valueStack ++
                restStack.valueStack
            fieldStore := restStack.fieldStore } =
        (blocks.flatten, restStack) := by
    simpa [GraphQL.Execution.resolveFieldValueByName, hlookup, blocks, restStack]
      using
        slots_completeSlotList_buildFieldSlots_eq_expectedScheduleSegmentResultsFlatten
          (ObjectRef := ObjectRef) schema resolvers variableValues item.key
          fieldDefinition item restStack hlookup rfl haligned hready
  have hlengths :
      item.toScheduleItem.segmentLengths = blocks.map List.length := by
    simp [blocks, ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentLengths,
      ScheduleSegment.length]
    intro segment hsegment
    exact (queue_expectedScheduleSegmentSpecFieldResults_length
      schema resolvers variableValues item.key segment
      (haligned segment hsegment)).symm
  have hcomplete' :
      completeSlotList fieldDefinition.outputType
          (buildFieldSlots schema fieldDefinition.outputType
            item.toScheduleItem.segments
            (item.toScheduleItem.sources.map (fun source =>
              GraphQL.Execution.coerceAndResolveFieldValue schema resolvers variableValues
                fieldDefinition item.key.parentType item.key.fieldName
                item.key.arguments source))).snd
          { valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers variableValues
                (expectedPendingChildWorkForItem schema resolvers
                  fieldDefinition.outputType item variableValues)).valueStack
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                rest).fieldStore } =
        (blocks.flatten,
          expectedScheduleQueueCompletionStack schema resolvers variableValues rest) := by
    simpa [restStack, expectedScheduleQueueCompletionStack] using hcomplete
  have hsplit :
      splitResultsByLengths item.toScheduleItem.segmentLengths blocks.flatten =
        blocks := by
    rw [hlengths]
    exact slots_splitResultsByLengths_map_length_flatten blocks
  have hdescriptors :
      item.toScheduleItem.segmentDescriptors =
        item.segments.map (fun segment =>
          (segment.segment.responseName, segment.segment.sources.length)) := by
    simp [ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentDescriptors,
      ScheduleSegment.length, Function.comp_def]
  have hdescriptorLengths :
      item.toScheduleItem.segmentDescriptors.map Prod.snd =
        item.toScheduleItem.segmentLengths := by
    simp [ExpectedQueueItem.toScheduleItem, ScheduleItem.segmentDescriptors,
      ScheduleItem.segmentLengths, ScheduleSegment.length, Function.comp_def]
  change
    completeFieldFrame item.key fieldDefinition.outputType
        item.toScheduleItem.segmentDescriptors
        (buildFieldSlots schema fieldDefinition.outputType
          item.toScheduleItem.segments
          (item.toScheduleItem.sources.map (fun source =>
            GraphQL.Execution.coerceAndResolveFieldValue schema resolvers variableValues
              fieldDefinition item.key.parentType item.key.fieldName
              item.key.arguments source))).snd
        { valueStack :=
            (expectedPendingChildWorkCompletionStack schema resolvers variableValues
              (expectedPendingChildWorkForItem schema resolvers
                fieldDefinition.outputType item variableValues)).valueStack
          fieldStore :=
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              rest).fieldStore } =
      expectedScheduleQueueCompletionStack schema resolvers variableValues
        (item :: rest)
  unfold completeFieldFrame
  rw [hcomplete']
  dsimp
  rw [hdescriptorLengths, hsplit, hdescriptors]
  rw [queue_bindFieldSegments_expectedMap]
  simp [expectedScheduleQueueCompletionStack, expectedQueueItemCompletion]

theorem queue_drainLoopMatchesExpectedSpec_cons_of_expected_step
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (breadthFuel : Nat)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : expectedDrainStepMatchesSpec schema resolvers variableValues item rest
      -> drainLoopMatchesExpectedSpec schema resolvers variableValues breadthFuel
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst)
      -> drainLoopMatchesExpectedSpec schema resolvers variableValues
          (breadthFuel + 1) (item :: rest) := by
  intro hstep htail
  unfold expectedDrainStepMatchesSpec at hstep
  rcases hstep with ⟨hqueue, hcomplete⟩
  unfold drainLoopMatchesExpectedSpec expectedQueueTraceMatchesSpec at htail ⊢
  simp [expectedScheduleQueueToQueue] at htail ⊢
  let executed :=
    executeScheduleItem schema (ResolverMap.fromSpecResolvers resolvers)
      variableValues item.toScheduleItem
  let expectedChild :=
    expectedChildQueueForItem schema resolvers variableValues item
  have hqueue' :
      enqueueScheduleItems (expectedScheduleQueueToQueue rest) executed.fst =
        expectedScheduleQueueToQueue
          (enqueueExpectedScheduleItems rest expectedChild.fst) := by
    rw [← hqueue, expectedScheduleQueueToQueue_enqueueExpectedScheduleItems]
  simp [queue_drainLoop_succ,
    List.reverse_append, queue_completeFrames_append]
  have htail' :
      completeFrames
          (List.reverse
            (drainLoop schema (ResolverMap.fromSpecResolvers resolvers)
              variableValues breadthFuel
              (enqueueScheduleItems (expectedScheduleQueueToQueue rest) executed.fst)))
          ∅ =
        expectedScheduleQueueCompletionStack schema resolvers variableValues
          (enqueueExpectedScheduleItems rest expectedChild.fst) := by
    rw [hqueue']
    exact htail
  have hmid :
      completeFrames executed.snd.reverse
          (completeFrames
            (List.reverse
              (drainLoop schema (ResolverMap.fromSpecResolvers resolvers)
                variableValues breadthFuel
                (enqueueScheduleItems (expectedScheduleQueueToQueue rest)
                  executed.fst)))
            ∅) =
        completeFrames executed.snd.reverse
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            (enqueueExpectedScheduleItems rest expectedChild.fst)) := by
    exact congrArg
      (fun stack => completeFrames executed.snd.reverse stack)
      htail'
  simpa [executed, expectedChild, expectedScheduleQueueToQueue] using hmid.trans hcomplete

theorem queue_drainLoopMatchesExpectedSpec_of_ready_and_stepSound
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : (∀ (item : ExpectedQueueItem ObjectRef) (rest : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueFuelsAligned (item :: rest)
        -> expectedScheduleQueueItemsNonempty (item :: rest)
        -> expectedScheduleQueueKeysDistinct (item :: rest)
        -> expectedQueueItemStepFuelReady schema item
        -> expectedDrainStepMatchesSpec schema resolvers variableValues item rest)
      -> ∀ (breadthFuel : Nat) (queue : ExpectedScheduleQueue ObjectRef),
          expectedDrainQueueReady schema resolvers variableValues breadthFuel queue
          -> drainLoopMatchesExpectedSpec schema resolvers variableValues breadthFuel
              queue := by
  intro hstep
  intro breadthFuel
  induction breadthFuel with
  | zero =>
      intro queue hready
      cases queue with
      | nil =>
          exact queue_drainLoopMatchesExpectedSpec_empty
            (ObjectRef := ObjectRef) schema resolvers variableValues 0
      | cons item rest =>
          cases hready
  | succ breadthFuel ih =>
      intro queue hready
      cases queue with
      | nil =>
          exact queue_drainLoopMatchesExpectedSpec_empty
            (ObjectRef := ObjectRef) schema resolvers variableValues (breadthFuel + 1)
      | cons item rest =>
          rcases hready with ⟨haligned, hnonempty, hdistinct, hitemReady, htailReady⟩
          have hstepItem :
              expectedDrainStepMatchesSpec schema resolvers variableValues item rest :=
            hstep item rest haligned hnonempty hdistinct hitemReady
          have htail :
              drainLoopMatchesExpectedSpec schema resolvers variableValues breadthFuel
                (enqueueExpectedScheduleItems rest
                  (expectedChildQueueForItem schema resolvers variableValues item).fst) :=
            ih _ htailReady
          exact queue_drainLoopMatchesExpectedSpec_cons_of_expected_step
            (ObjectRef := ObjectRef) schema resolvers variableValues
            breadthFuel item rest hstepItem htail

theorem queue_expectedScheduleQueueCompletionStack_enqueueExpectedSegment_eq_push
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (enqueueExpectedSegment key segment queue)
      = pushExpectedFieldSegment
          { responseName := segment.segment.responseName, key := key }
          (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            key segment)
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            queue) := by
  induction queue with
  | nil =>
      simp [enqueueExpectedSegment, expectedScheduleQueueCompletionStack,
        expectedQueueItemCompletion, pushExpectedFieldSegment,
        pushExpectedFieldSegmentInStore]
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · have hkeyEq : key = item.key :=
          scheduleKeyEqBool_eq hkey
        cases hkeyEq
        simp [enqueueExpectedSegment, expectedScheduleQueueCompletionStack,
          expectedQueueItemCompletion, pushExpectedFieldSegment,
          pushExpectedFieldSegmentInStore, hkey, List.map_append,
          List.reverse_append]
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have ihStore := congrArg CompletionState.fieldStore ih
        simp [enqueueExpectedSegment, expectedScheduleQueueCompletionStack,
          expectedQueueItemCompletion, pushExpectedFieldSegment,
          pushExpectedFieldSegmentInStore, hkeyFalse] at ihStore ⊢
        exact ihStore

theorem queue_expectedScheduleQueueCompletionStack_enqueueExpectedSegments_eq_foldl_push
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (key : ScheduleKey) (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (enqueueExpectedSegments key segments queue)
      = segments.foldl
          (fun stack segment =>
            pushExpectedFieldSegment
              { responseName := segment.segment.responseName, key := key }
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                key segment)
              stack)
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            queue) := by
  induction segments generalizing queue with
  | nil =>
      rfl
  | cons segment rest ih =>
      calc
        expectedScheduleQueueCompletionStack schema resolvers variableValues
              (enqueueExpectedSegments key rest
                (enqueueExpectedSegment key segment queue))
            = rest.foldl
                (fun stack segment =>
                  pushExpectedFieldSegment
                    { responseName := segment.segment.responseName, key := key }
                    (expectedScheduleSegmentSpecFieldResults schema resolvers
                      variableValues key segment)
                    stack)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (enqueueExpectedSegment key segment queue)) :=
          ih _
        _ = rest.foldl
              (fun stack segment =>
                pushExpectedFieldSegment
                  { responseName := segment.segment.responseName, key := key }
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    key segment)
                  stack)
              (pushExpectedFieldSegment
                { responseName := segment.segment.responseName, key := key }
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  key segment)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  queue)) := by
          rw [queue_expectedScheduleQueueCompletionStack_enqueueExpectedSegment_eq_push]
        _ = (segment :: rest).foldl
              (fun stack segment =>
                pushExpectedFieldSegment
                  { responseName := segment.segment.responseName, key := key }
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    key segment)
                  stack)
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue) := by
          rfl

theorem
    queue_expectedScheduleQueueCompletionStack_enqueueExpectedScheduleItems_eq_foldl_push
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (queue items : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (enqueueExpectedScheduleItems queue items)
      = items.foldl
          (fun stack item =>
            item.segments.foldl
              (fun stack segment =>
                pushExpectedFieldSegment
                  { responseName := segment.segment.responseName, key := item.key }
                  (expectedScheduleSegmentSpecFieldResults schema resolvers
                    variableValues item.key segment)
                  stack)
              stack)
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            queue) := by
  induction items generalizing queue with
  | nil =>
      rfl
  | cons item rest ih =>
      calc
        expectedScheduleQueueCompletionStack schema resolvers variableValues
              (enqueueExpectedScheduleItems
                (enqueueExpectedSegments item.key item.segments queue)
                rest)
            = rest.foldl
                (fun stack item =>
                  item.segments.foldl
                    (fun stack segment =>
                      pushExpectedFieldSegment
                        { responseName := segment.segment.responseName, key := item.key }
                        (expectedScheduleSegmentSpecFieldResults schema resolvers
                          variableValues item.key segment)
                        stack)
                    stack)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (enqueueExpectedSegments item.key item.segments queue)) :=
          ih _
        _ = rest.foldl
              (fun stack item =>
                item.segments.foldl
                  (fun stack segment =>
                    pushExpectedFieldSegment
                      { responseName := segment.segment.responseName, key := item.key }
                      (expectedScheduleSegmentSpecFieldResults schema resolvers
                        variableValues item.key segment)
                      stack)
                  stack)
              (item.segments.foldl
                (fun stack segment =>
                  pushExpectedFieldSegment
                    { responseName := segment.segment.responseName, key := item.key }
                    (expectedScheduleSegmentSpecFieldResults schema resolvers
                      variableValues item.key segment)
                    stack)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  queue)) := by
          rw [queue_expectedScheduleQueueCompletionStack_enqueueExpectedSegments_eq_foldl_push]
        _ = (item :: rest).foldl
              (fun stack item =>
                item.segments.foldl
                  (fun stack segment =>
                    pushExpectedFieldSegment
                      { responseName := segment.segment.responseName, key := item.key }
                      (expectedScheduleSegmentSpecFieldResults schema resolvers
                        variableValues item.key segment)
                      stack)
                  stack)
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue) := by
          rfl

theorem queue_expectedScheduleQueueCompletionStack_scheduleExpectedScopeGroups
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (groups : List (FieldBinding × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (groups.foldl
          (fun queue group =>
            enqueueExpectedSegment group.fst.key
              {
                segment :=
                  {
                    responseName := group.fst.responseName
                    sources := sources
                    childSelectionSet := childSelectionSetForFields group.snd
                  }
                specFuels := specFuels
              }
              queue)
          queue)
      = groups.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst.key
                {
                  segment :=
                    {
                      responseName := group.fst.responseName
                      sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd
                    }
                  specFuels := specFuels
                })
              stack)
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            queue) := by
  induction groups generalizing queue with
  | nil =>
      rfl
  | cons group groups ih =>
      let segment : ExpectedQueueSegment ObjectRef :=
        { segment :=
            { responseName := group.fst.responseName
              sources := sources
              childSelectionSet := childSelectionSetForFields group.snd }
          specFuels := specFuels }
      calc
        expectedScheduleQueueCompletionStack schema resolvers variableValues
              (groups.foldl
                (fun queue group =>
                  enqueueExpectedSegment group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)
                (enqueueExpectedSegment group.fst.key
                  {
                    segment :=
                      {
                        responseName := group.fst.responseName
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := specFuels
                  }
                  queue))
            = groups.foldl
                (fun stack group =>
                  pushExpectedFieldSegment group.fst
                    (expectedScheduleSegmentSpecFieldResults schema resolvers
                      variableValues group.fst.key
                      {
                        segment :=
                          {
                            responseName := group.fst.responseName
                            sources := sources
                            childSelectionSet := childSelectionSetForFields group.snd
                          }
                        specFuels := specFuels
                      })
                    stack)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (enqueueExpectedSegment group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)) :=
          ih _
        _ = groups.foldl
              (fun stack group =>
                pushExpectedFieldSegment group.fst
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    })
                  stack)
              (pushExpectedFieldSegment group.fst
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  group.fst.key
                  {
                    segment :=
                      {
                        responseName := group.fst.responseName
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := specFuels
                  })
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  queue)) := by
          rw [queue_expectedScheduleQueueCompletionStack_enqueueExpectedSegment_eq_push]
        _ = (group :: groups).foldl
              (fun stack group =>
                pushExpectedFieldSegment group.fst
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    })
                  stack)
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue) := by
          rfl

theorem queue_foldl_enqueueExpectedSegment_cons_of_absent
    (entries : List (ScheduleKey × ExpectedQueueSegment ObjectRef))
    (item : ExpectedQueueItem ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : (∀ entry, entry ∈ entries -> scheduleKeyEqBool entry.fst item.key = false)
      -> entries.foldl
            (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
            (item :: queue)
          = item
            :: entries.foldl
                (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
                queue := by
  intro habsent
  induction entries generalizing queue with
  | nil =>
      rfl
  | cons entry entries ih =>
      have hhead : scheduleKeyEqBool entry.fst item.key = false :=
        habsent entry (by simp)
      have htail :
          ∀ later, later ∈ entries ->
            scheduleKeyEqBool later.fst item.key = false := by
        intro later hlater
        exact habsent later (by simp [hlater])
      simp only [List.foldl_cons]
      simp [enqueueExpectedSegment, hhead,
        ih (enqueueExpectedSegment entry.fst entry.snd queue) htail]

def expectedQueueContainsKey (key : ScheduleKey) : ExpectedScheduleQueue ObjectRef -> Prop
  | [] => False
  | item :: rest =>
      scheduleKeyEqBool key item.key = true ∨ expectedQueueContainsKey key rest

theorem queue_expectedQueueContainsKey_enqueueExpectedSegment_self
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueContainsKey key (enqueueExpectedSegment key segment queue) := by
  induction queue with
  | nil =>
      simp [enqueueExpectedSegment, expectedQueueContainsKey, scheduleKeyEqBool_self]
  | cons item rest ih =>
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · simp [enqueueExpectedSegment, expectedQueueContainsKey, hkey]
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        simp [enqueueExpectedSegment, expectedQueueContainsKey, hkeyFalse, ih]

theorem queue_expectedQueueContainsKey_enqueueExpectedSegment_of_present
    (key pushedKey : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueContainsKey key queue
      -> expectedQueueContainsKey key
          (enqueueExpectedSegment pushedKey segment queue) := by
  intro hpresent
  induction queue with
  | nil =>
      cases hpresent
  | cons item rest ih =>
      simp [expectedQueueContainsKey] at hpresent ⊢
      by_cases hpushed : scheduleKeyEqBool pushedKey item.key = true
      · rcases hpresent with hkey | htail
        · simp [enqueueExpectedSegment, hpushed, expectedQueueContainsKey, hkey]
        · simp [enqueueExpectedSegment, hpushed, expectedQueueContainsKey, htail]
      · have hpushedFalse : scheduleKeyEqBool pushedKey item.key = false := by
          cases h : scheduleKeyEqBool pushedKey item.key with
          | false => rfl
          | true => exact False.elim (hpushed h)
        rcases hpresent with hkey | htail
        · simp [enqueueExpectedSegment, hpushedFalse, expectedQueueContainsKey, hkey]
        · have htail' := ih htail
          simp [enqueueExpectedSegment, hpushedFalse, expectedQueueContainsKey,
            htail']

theorem queue_expectedQueueContainsKey_enqueueExpectedSegments_of_present
    (key pushedKey : ScheduleKey)
    (segments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueContainsKey key queue
      -> expectedQueueContainsKey key
          (enqueueExpectedSegments pushedKey segments queue) := by
  intro hpresent
  induction segments generalizing queue with
  | nil =>
      simpa [enqueueExpectedSegments] using hpresent
  | cons segment rest ih =>
      exact ih _
        (queue_expectedQueueContainsKey_enqueueExpectedSegment_of_present
          (ObjectRef := ObjectRef) key pushedKey segment queue hpresent)

theorem queue_enqueueExpectedSegment_commute_of_present
    (key pushedKey : ScheduleKey)
    (segment pushedSegment : ExpectedQueueSegment ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueContainsKey key queue
      -> scheduleKeyEqBool key pushedKey = false
      -> enqueueExpectedSegment pushedKey pushedSegment
            (enqueueExpectedSegment key segment queue)
          = enqueueExpectedSegment key segment
              (enqueueExpectedSegment pushedKey pushedSegment queue) := by
  intro hpresent hneq
  induction queue with
  | nil =>
      cases hpresent
  | cons item rest ih =>
      simp [expectedQueueContainsKey] at hpresent
      by_cases hkeyItem : scheduleKeyEqBool key item.key = true
      · have hpushedItemFalse : scheduleKeyEqBool pushedKey item.key = false := by
          have hkeyEq : key = item.key := scheduleKeyEqBool_eq hkeyItem
          have hneq' : scheduleKeyEqBool item.key pushedKey = false := by
            simpa [hkeyEq] using hneq
          exact scheduleKeyEqBool_false_symm hneq'
        simp [enqueueExpectedSegment, hkeyItem, hpushedItemFalse]
      · have hkeyItemFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkeyItem h)
        have htailPresent : expectedQueueContainsKey key rest := by
          rcases hpresent with hpresentHead | hpresentTail
          · exact False.elim (by simp [hkeyItemFalse] at hpresentHead)
          · exact hpresentTail
        by_cases hpushedItem : scheduleKeyEqBool pushedKey item.key = true
        · simp [enqueueExpectedSegment, hkeyItemFalse, hpushedItem]
        · have hpushedItemFalse : scheduleKeyEqBool pushedKey item.key = false := by
            cases h : scheduleKeyEqBool pushedKey item.key with
            | false => rfl
            | true => exact False.elim (hpushedItem h)
          have htail := ih htailPresent
          simp [enqueueExpectedSegment, hkeyItemFalse, hpushedItemFalse, htail]

theorem queue_enqueueExpectedSegments_commute_of_present
    (key pushedKey : ScheduleKey)
    (segment : ExpectedQueueSegment ObjectRef)
    (pushedSegments : List (ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueContainsKey key queue
      -> scheduleKeyEqBool key pushedKey = false
      -> enqueueExpectedSegments pushedKey pushedSegments
            (enqueueExpectedSegment key segment queue)
          = enqueueExpectedSegment key segment
              (enqueueExpectedSegments pushedKey pushedSegments queue) := by
  intro hpresent hneq
  induction pushedSegments generalizing queue with
  | nil =>
      rfl
  | cons pushedSegment rest ih =>
      have hcomm :=
        queue_enqueueExpectedSegment_commute_of_present
          (ObjectRef := ObjectRef) key pushedKey segment pushedSegment queue
          hpresent hneq
      have hpresent' :
          expectedQueueContainsKey key
            (enqueueExpectedSegment pushedKey pushedSegment queue) :=
        queue_expectedQueueContainsKey_enqueueExpectedSegment_of_present
          (ObjectRef := ObjectRef) key pushedKey pushedSegment queue hpresent
      simp [enqueueExpectedSegments]
      rw [hcomm]
      exact ih _ hpresent'

theorem queue_enqueueExpectedScheduleItems_enqueueExpectedSegment_of_present_absent
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (items queue : ExpectedScheduleQueue ObjectRef)
    : expectedQueueContainsKey key queue
      -> scheduleKeyAbsentFromExpectedQueue key items
      -> enqueueExpectedScheduleItems (enqueueExpectedSegment key segment queue) items
          = enqueueExpectedSegment key segment
              (enqueueExpectedScheduleItems queue items) := by
  intro hpresent habsent
  induction items generalizing queue with
  | nil =>
      rfl
  | cons item rest ih =>
      have hkeyItemFalse : scheduleKeyEqBool key item.key = false :=
        habsent item (by simp)
      have hrestAbsent : scheduleKeyAbsentFromExpectedQueue key rest := by
        intro restItem hrestItem
        exact habsent restItem (by simp [hrestItem])
      have hcomm :=
        queue_enqueueExpectedSegments_commute_of_present
          (ObjectRef := ObjectRef) key item.key segment item.segments queue
          hpresent hkeyItemFalse
      have hpresent' :
          expectedQueueContainsKey key
            (enqueueExpectedSegments item.key item.segments queue) :=
        queue_expectedQueueContainsKey_enqueueExpectedSegments_of_present
          (ObjectRef := ObjectRef) key item.key item.segments queue hpresent
      have htail := ih _ hpresent' hrestAbsent
      simp [enqueueExpectedScheduleItems]
      rw [hcomm]
      exact htail

theorem queue_enqueueExpectedScheduleItems_enqueueExpectedSegment
    (key : ScheduleKey) (segment : ExpectedQueueSegment ObjectRef)
    (base queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty base
      -> expectedScheduleQueueKeysDistinct base
      -> enqueueExpectedScheduleItems queue (enqueueExpectedSegment key segment base)
          = enqueueExpectedSegment key segment
              (enqueueExpectedScheduleItems queue base) := by
  intro hbaseNonempty hbaseDistinct
  induction base generalizing queue with
  | nil =>
      rfl
  | cons item rest ih =>
      rcases hbaseDistinct with ⟨hitemAbsent, hrestDistinct⟩
      have hrestNonempty :
          expectedScheduleQueueItemsNonempty rest := by
        intro restItem hrestItem
        exact hbaseNonempty restItem (by simp [hrestItem])
      by_cases hkey : scheduleKeyEqBool key item.key = true
      · have hkeyEq : key = item.key := scheduleKeyEqBool_eq hkey
        subst key
        have hitemSegments : item.segments ≠ [] :=
          hbaseNonempty item (by simp)
        cases hsegments : item.segments with
        | nil =>
            exact False.elim (hitemSegments hsegments)
        | cons head tail =>
            let baseQueue :=
              enqueueExpectedSegments item.key tail
                (enqueueExpectedSegment item.key head queue)
            have hpresentHead :
                expectedQueueContainsKey item.key
                  (enqueueExpectedSegment item.key head queue) :=
              queue_expectedQueueContainsKey_enqueueExpectedSegment_self
                (ObjectRef := ObjectRef) item.key head queue
            have hpresent :
                expectedQueueContainsKey item.key baseQueue :=
              queue_expectedQueueContainsKey_enqueueExpectedSegments_of_present
                (ObjectRef := ObjectRef) item.key item.key tail
                (enqueueExpectedSegment item.key head queue) hpresentHead
            have hcomm :=
              queue_enqueueExpectedScheduleItems_enqueueExpectedSegment_of_present_absent
                (ObjectRef := ObjectRef) item.key segment rest baseQueue
                hpresent hitemAbsent
            simpa [baseQueue, enqueueExpectedSegment, enqueueExpectedScheduleItems,
              enqueueExpectedSegments, hkey, hsegments] using hcomm
      · have hkeyFalse : scheduleKeyEqBool key item.key = false := by
          cases h : scheduleKeyEqBool key item.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        have htail :=
          ih (enqueueExpectedSegments item.key item.segments queue)
            hrestNonempty hrestDistinct
        simpa [enqueueExpectedSegment, enqueueExpectedScheduleItems, hkeyFalse]
          using htail

theorem queue_enqueueExpectedScheduleItems_scheduleExpectedScope
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (base queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty base
      -> expectedScheduleQueueKeysDistinct base
      -> enqueueExpectedScheduleItems queue
            (scheduleExpectedScope schema variableValues parentType sources
              specFuels selectionSet base).fst
          = (scheduleExpectedScope schema variableValues parentType sources
              specFuels selectionSet
              (enqueueExpectedScheduleItems queue base)).fst := by
  intro hbaseNonempty hbaseDistinct
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let boundGroups := groups.map (bindCollectedGroup parentType)
  have hfold :
      ∀ (groups0 : List (FieldBinding × List ExecutableField))
        (base0 : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueItemsNonempty base0 ->
        expectedScheduleQueueKeysDistinct base0 ->
          enqueueExpectedScheduleItems queue
              (groups0.foldl
                (fun queue group =>
                  enqueueExpectedSegment group.fst.key
                    { segment :=
                        { responseName := group.fst.responseName
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd }
                      specFuels := specFuels }
                    queue)
                base0) =
            groups0.foldl
              (fun queue group =>
                enqueueExpectedSegment group.fst.key
                  { segment :=
                      { responseName := group.fst.responseName
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := specFuels }
                  queue)
              (enqueueExpectedScheduleItems queue base0) := by
    intro groups0
    induction groups0 with
    | nil =>
        intro base0 _hbaseNonempty _hbaseDistinct
        rfl
    | cons group rest ih =>
        intro base0 hbase0Nonempty hbase0Distinct
        let segment : ExpectedQueueSegment ObjectRef :=
          { segment :=
              { responseName := group.fst.responseName
                sources := sources
                childSelectionSet := childSelectionSetForFields group.snd }
            specFuels := specFuels }
        have hnextNonempty :
            expectedScheduleQueueItemsNonempty
              (enqueueExpectedSegment group.fst.key segment base0) :=
          enqueueExpectedSegment_itemsNonempty group.fst.key segment base0
            hbase0Nonempty
        have hnextDistinct :
            expectedScheduleQueueKeysDistinct
              (enqueueExpectedSegment group.fst.key segment base0) :=
          enqueueExpectedSegment_keysDistinct group.fst.key segment base0
            hbase0Distinct
        have htail :=
          ih (enqueueExpectedSegment group.fst.key segment base0)
            hnextNonempty hnextDistinct
        have hhead :=
          queue_enqueueExpectedScheduleItems_enqueueExpectedSegment
            (ObjectRef := ObjectRef) group.fst.key segment base0 queue
            hbase0Nonempty hbase0Distinct
        simpa [segment] using htail.trans (congrArg
          (fun q =>
            rest.foldl
              (fun queue group =>
                enqueueExpectedSegment group.fst.key
                  { segment :=
                      { responseName := group.fst.responseName
                        sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := specFuels }
                  queue)
              q)
          hhead)
  simpa [scheduleExpectedScope, groups, boundGroups]
    using hfold boundGroups base hbaseNonempty hbaseDistinct

theorem queue_enqueueExpectedScheduleItems_scheduleExpectedScope_empty
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : enqueueExpectedScheduleItems queue
        (scheduleExpectedScope schema variableValues parentType sources
          specFuels selectionSet []).fst
      = (scheduleExpectedScope schema variableValues parentType sources
          specFuels selectionSet queue).fst := by
  exact queue_enqueueExpectedScheduleItems_scheduleExpectedScope
    (ObjectRef := ObjectRef) schema variableValues parentType sources specFuels
    selectionSet [] queue (by simp [expectedScheduleQueueItemsNonempty])
    (by simp [expectedScheduleQueueKeysDistinct])

theorem queue_expectedScheduleQueueCompletionStack_scheduleExpectedScope_enqueue_empty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name)
    (sources : List (ResolverValue ObjectRef)) (specFuels : List Nat)
    (selectionSet : List Selection)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (enqueueExpectedScheduleItems queue
          (scheduleExpectedScope schema variableValues parentType sources
            specFuels selectionSet []).fst)
      = {
        valueStack := []
        fieldStore :=
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            (scheduleExpectedScope schema variableValues parentType sources
              specFuels selectionSet queue).fst).fieldStore
      } := by
  rw [queue_enqueueExpectedScheduleItems_scheduleExpectedScope_empty]
  simp [expectedScheduleQueueCompletionStack]

theorem queue_fieldStoreSegmentsNonempty_append (left right : FieldStore)
    : fieldStoreSegmentsNonempty left
      -> fieldStoreSegmentsNonempty right
      -> fieldStoreSegmentsNonempty (left ++ right) := by
  intro hleft hright
  induction left with
  | nil =>
      simpa using hright
  | cons entry left ih =>
      rcases entry with ⟨binding, segments⟩
      exact ⟨hleft.1, ih hleft.2⟩

theorem queue_pruneEmptyFieldItems_eq_of_segmentsNonempty (store : FieldStore)
    : fieldStoreSegmentsNonempty store -> pruneEmptyFieldItems store = store := by
  intro hstore
  induction store with
  | nil =>
      rfl
  | cons entry store ih =>
      rcases entry with ⟨key, segments⟩
      rcases hstore with ⟨hsegments, hstore⟩
      cases segments with
      | nil =>
          exact False.elim (hsegments rfl)
      | cons segment segments =>
          simp [pruneEmptyFieldItems, ih hstore]

theorem queue_normalizeCompletionState_eq_of_fieldSegmentsNonempty
    (stack : CompletionStack)
    : completionStackFieldSegmentsNonempty stack
      -> normalizeCompletionState stack = stack := by
  intro hstack
  cases stack with
  | mk valueStack fieldStore =>
      simp only [completionStackFieldSegmentsNonempty] at hstack
      simp [normalizeCompletionState,
        queue_pruneEmptyFieldItems_eq_of_segmentsNonempty fieldStore hstack]

theorem queue_expectedQueueItemCompletion_fieldSegmentsNonempty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (item : ExpectedQueueItem ObjectRef)
    : item.segments ≠ []
      -> fieldStoreSegmentsNonempty
          [expectedQueueItemCompletion schema resolvers variableValues item] := by
  intro hsegments
  simp [expectedQueueItemCompletion, fieldStoreSegmentsNonempty, hsegments]

theorem queue_expectedScheduleQueueCompletionStack_fieldSegmentsNonempty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty queue
      -> completionStackFieldSegmentsNonempty
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            queue) := by
  intro hqueue
  induction queue with
  | nil =>
      simp [expectedScheduleQueueCompletionStack, completionStackFieldSegmentsNonempty,
        fieldStoreSegmentsNonempty]
  | cons queueItem rest ih =>
      have hitem : queueItem.segments ≠ [] := hqueue queueItem (by simp)
      have hrest :
          expectedScheduleQueueItemsNonempty rest := by
        intro restItem hrestItem
        exact hqueue restItem (by simp [hrestItem])
      have htail := ih hrest
      simpa [completionStackFieldSegmentsNonempty, expectedScheduleQueueCompletionStack]
        using queue_fieldStoreSegmentsNonempty_append
          [expectedQueueItemCompletion schema resolvers variableValues queueItem]
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            rest).fieldStore
          (queue_expectedQueueItemCompletion_fieldSegmentsNonempty
            schema resolvers variableValues queueItem hitem)
          (by simpa [completionStackFieldSegmentsNonempty] using htail)

theorem queue_pushExpectedFieldSegment_fieldSegmentsNonempty
    (key : FieldBinding)
    (segmentResults : List (Result ResponseValue))
    (stack : CompletionStack)
    : completionStackFieldSegmentsNonempty stack
      -> completionStackFieldSegmentsNonempty
          (pushExpectedFieldSegment key segmentResults stack) := by
  cases stack with
  | mk valueStack fieldStore =>
      simp [completionStackFieldSegmentsNonempty, pushExpectedFieldSegment]
      intro hstore
      induction fieldStore with
      | nil =>
          simp [pushExpectedFieldSegmentInStore, fieldStoreSegmentsNonempty]
      | cons entry fieldStore ih =>
          rcases entry with ⟨fieldKey, fieldSegments⟩
          by_cases hkey : scheduleKeyEqBool key.key fieldKey = true
          · simp [pushExpectedFieldSegmentInStore, hkey,
              fieldStoreSegmentsNonempty, hstore.2]
          · have hkeyFalse : scheduleKeyEqBool key.key fieldKey = false := by
              cases h : scheduleKeyEqBool key.key fieldKey with
              | false => rfl
              | true => exact False.elim (hkey h)
            have htail : fieldStoreSegmentsNonempty fieldStore := hstore.2
            simp [pushExpectedFieldSegmentInStore, hkeyFalse,
              fieldStoreSegmentsNonempty, hstore.1, ih htail]

theorem queue_popFieldResultByBinding_pushExpectedFieldSegment_self
    (key : FieldBinding)
    (segmentResults : List (Result ResponseValue))
    (stack : CompletionStack)
    : let popped :=
        popFieldResultByBinding key (pushExpectedFieldSegment key segmentResults stack)
      popped.fst = segmentResults
      ∧ normalizeCompletionState popped.snd = normalizeCompletionState stack := by
  cases stack with
  | mk valueStack fieldStore =>
      induction fieldStore with
      | nil =>
          simp [pushExpectedFieldSegmentInStore,
            popFieldResultByBindingFromStore, popBoundFieldSegment,
            popFieldResultByBinding, pushExpectedFieldSegment,
            normalizeCompletionState, pruneEmptyFieldItems,
            scheduleKeyEqBool_self]
      | cons entry fieldStore ih =>
          rcases entry with ⟨fieldKey, fieldSegments⟩
          by_cases hkey : scheduleKeyEqBool key.key fieldKey = true
          · simp [pushExpectedFieldSegmentInStore,
              popFieldResultByBindingFromStore, popBoundFieldSegment,
              popFieldResultByBinding, pushExpectedFieldSegment,
              normalizeCompletionState, hkey]
          · have hkeyFalse : scheduleKeyEqBool key.key fieldKey = false := by
              cases h : scheduleKeyEqBool key.key fieldKey with
              | false => rfl
              | true => exact False.elim (hkey h)
            cases fieldSegments with
            | nil =>
                simpa [pushExpectedFieldSegmentInStore,
                  popFieldResultByBindingFromStore, popFieldResultByBinding,
                  pushExpectedFieldSegment, normalizeCompletionState,
                  pruneEmptyFieldItems, hkeyFalse] using ih
            | cons fieldSegment fieldSegments =>
                simpa [pushExpectedFieldSegmentInStore,
                  popFieldResultByBindingFromStore, popFieldResultByBinding,
                  pushExpectedFieldSegment, normalizeCompletionState,
                  pruneEmptyFieldItems, hkeyFalse] using ih

theorem queue_popBoundFieldSegment_cons_of_ne
    (responseName pushedResponseName : Name)
    (segmentResults : List (Result ResponseValue))
    (segments : BoundFieldSegments)
    : responseName ≠ pushedResponseName
      -> popBoundFieldSegment responseName
            ((pushedResponseName, segmentResults) :: segments)
          = match popBoundFieldSegment responseName segments with
            | none => none
            | some (popped, segments') =>
                some (popped, (pushedResponseName, segmentResults) :: segments') := by
  intro hne
  simp only [popBoundFieldSegment]
  simp [hne]
  cases hpop : popBoundFieldSegment responseName segments with
  | none => rfl
  | some popped => rfl

theorem queue_responseName_ne_of_fieldBinding_false_scheduleKey_true
    {left right : FieldBinding}
    : fieldBindingEqBool left right = false
      -> scheduleKeyEqBool left.key right.key = true
      -> left.responseName ≠ right.responseName := by
  intro hbinding hkey hresponse
  have hkeyEq : left.key = right.key := scheduleKeyEqBool_eq hkey
  cases left with
  | mk leftResponse leftKey =>
      cases right with
      | mk rightResponse rightKey =>
          change leftResponse = rightResponse at hresponse
          change leftKey = rightKey at hkeyEq
          subst rightResponse
          subst rightKey
          simp [fieldBindingEqBool_self] at hbinding

theorem queue_popFieldResultByBindingFromStore_pushExpectedFieldSegmentInStore_commute
    (key pushedKey : FieldBinding)
    (segmentResults : List (Result ResponseValue))
    (store : FieldStore)
    : fieldBindingEqBool key pushedKey = false
      -> popFieldResultByBindingFromStore key
            (pushExpectedFieldSegmentInStore pushedKey segmentResults store)
          = let popped := popFieldResultByBindingFromStore key store
            (
              popped.fst,
              pushExpectedFieldSegmentInStore pushedKey segmentResults popped.snd
            ) := by
  intro hneq
  induction store with
  | nil =>
      by_cases hkey : scheduleKeyEqBool key.key pushedKey.key = true
      · have hresponse :=
          queue_responseName_ne_of_fieldBinding_false_scheduleKey_true hneq hkey
        simp [pushExpectedFieldSegmentInStore,
          popFieldResultByBindingFromStore, popBoundFieldSegment, hkey, hresponse]
      · have hkeyFalse : scheduleKeyEqBool key.key pushedKey.key = false := by
          cases h : scheduleKeyEqBool key.key pushedKey.key with
          | false => rfl
          | true => exact False.elim (hkey h)
        simp [pushExpectedFieldSegmentInStore,
          popFieldResultByBindingFromStore, hkeyFalse]
  | cons entry store ih =>
      rcases entry with ⟨fieldKey, fieldSegments⟩
      by_cases hpushed : scheduleKeyEqBool pushedKey.key fieldKey = true
      · have hpushedEq : pushedKey.key = fieldKey :=
          scheduleKeyEqBool_eq hpushed
        by_cases hkey : scheduleKeyEqBool key.key fieldKey = true
        · have hkeyPushed : scheduleKeyEqBool key.key pushedKey.key = true := by
            simpa [hpushedEq] using hkey
          have hresponse :=
            queue_responseName_ne_of_fieldBinding_false_scheduleKey_true
              hneq hkeyPushed
          cases hpop : popBoundFieldSegment key.responseName fieldSegments with
          | none =>
              simp [pushExpectedFieldSegmentInStore,
                popFieldResultByBindingFromStore, hpushed, hkey,
                queue_popBoundFieldSegment_cons_of_ne, hresponse, hpop]
          | some popped =>
              rcases popped with ⟨values, remaining⟩
              simp [pushExpectedFieldSegmentInStore,
                popFieldResultByBindingFromStore, hpushed, hkey,
                queue_popBoundFieldSegment_cons_of_ne, hresponse, hpop]
        · have hkeyFalse : scheduleKeyEqBool key.key fieldKey = false := by
            cases h : scheduleKeyEqBool key.key fieldKey with
            | false => rfl
            | true => exact False.elim (hkey h)
          simp [pushExpectedFieldSegmentInStore,
            popFieldResultByBindingFromStore, hpushed, hkeyFalse]
      · have hpushedFalse : scheduleKeyEqBool pushedKey.key fieldKey = false := by
          cases h : scheduleKeyEqBool pushedKey.key fieldKey with
          | false => rfl
          | true => exact False.elim (hpushed h)
        by_cases hkey : scheduleKeyEqBool key.key fieldKey = true
        · cases hpop : popBoundFieldSegment key.responseName fieldSegments with
          | none =>
              simp [pushExpectedFieldSegmentInStore,
                popFieldResultByBindingFromStore, hpushedFalse, hkey, hpop]
          | some popped =>
              rcases popped with ⟨values, remaining⟩
              simp [pushExpectedFieldSegmentInStore,
                popFieldResultByBindingFromStore, hpushedFalse, hkey, hpop]
        · have hkeyFalse : scheduleKeyEqBool key.key fieldKey = false := by
            cases h : scheduleKeyEqBool key.key fieldKey with
            | false => rfl
            | true => exact False.elim (hkey h)
          simp [pushExpectedFieldSegmentInStore,
            popFieldResultByBindingFromStore, hpushedFalse, hkeyFalse, ih]

theorem queue_popFieldResultByBinding_pushExpectedFieldSegment_commute
    (key pushedKey : FieldBinding)
    (segmentResults : List (Result ResponseValue))
    (stack : CompletionStack)
    : fieldBindingEqBool key pushedKey = false
      -> popFieldResultByBinding key
            (pushExpectedFieldSegment pushedKey segmentResults stack)
          = let popped := popFieldResultByBinding key stack
            (
              popped.fst,
              pushExpectedFieldSegment pushedKey segmentResults popped.snd
            ) := by
  intro hneq
  cases stack
  simp [pushExpectedFieldSegment, popFieldResultByBinding,
    queue_popFieldResultByBindingFromStore_pushExpectedFieldSegmentInStore_commute,
    hneq]

theorem queue_popFieldResultByBinding_foldl_pushExpectedFieldSegments_commute
    (key : FieldBinding)
    (entries : List (FieldBinding × List (Result ResponseValue)))
    (stack : CompletionStack)
    : (∀ entry, entry ∈ entries -> fieldBindingEqBool key entry.fst = false)
      -> popFieldResultByBinding key
            (entries.foldl
              (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
              stack)
          = let popped := popFieldResultByBinding key stack
            (
              popped.fst,
              entries.foldl
                (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
                popped.snd
            ) := by
  intro hneq
  induction entries generalizing stack with
  | nil =>
      rfl
  | cons entry entries ih =>
      have hkeyFalse : fieldBindingEqBool key entry.fst = false :=
        hneq entry (by simp)
      have htailNe :
          ∀ later, later ∈ entries ->
            fieldBindingEqBool key later.fst = false := by
        intro later hlater
        exact hneq later (by simp [hlater])
      rw [List.foldl_cons]
      rw [ih (pushExpectedFieldSegment entry.fst entry.snd stack) htailNe]
      simp [queue_popFieldResultByBinding_pushExpectedFieldSegment_commute,
        hkeyFalse]

theorem queue_popFieldValuesByBindings_foldl_pushExpectedFieldSegments_normalized
    (entries : List (FieldBinding × List (Result ResponseValue)))
    (stack : CompletionStack)
    : pairKeysNodup (entries.map (fun entry => (entry.fst.responseName, entry.snd)))
      -> popFieldValuesByBindings (entries.map Prod.fst)
            (entries.foldl
              (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
              stack)
          = (entries, normalizeCompletionState stack) := by
  intro hnodup
  induction entries generalizing stack with
  | nil =>
      simp [popFieldValuesByBindings]
  | cons entry entries ih =>
      have hnodup' :
          entry.fst.responseName ∉ entries.map (fun entry => entry.fst.responseName) ∧
            (entries.map (fun entry => entry.fst.responseName)).Nodup := by
        simpa [pairKeysNodup, List.map_map, Function.comp_def] using hnodup
      have hrestNodup :
          pairKeysNodup
            (entries.map (fun entry => (entry.fst.responseName, entry.snd))) := by
        simpa [pairKeysNodup, List.map_map, Function.comp_def] using hnodup'.2
      have hheadAbsent :
          entry.fst.responseName ∉ entries.map (fun entry => entry.fst.responseName) := by
        exact hnodup'.1
      have hheadNe :
          ∀ later, later ∈ entries -> entry.fst.responseName ≠ later.fst.responseName := by
        intro later hlater heq
        apply hheadAbsent
        exact List.mem_map.mpr ⟨later, hlater, by simp [heq]⟩
      have hheadPop :=
        queue_popFieldResultByBinding_foldl_pushExpectedFieldSegments_commute
          entry.fst entries
          (pushExpectedFieldSegment entry.fst entry.snd stack)
          (fun later hlater =>
            queue_fieldBindingEqBool_false_of_responseName_ne
              (hheadNe later hlater))
      have hself :=
        queue_popFieldResultByBinding_pushExpectedFieldSegment_self
          entry.fst entry.snd stack
      simp only [List.map_cons, List.foldl_cons, popFieldValuesByBindings]
      rw [hheadPop]
      let popped :=
        popFieldResultByBinding entry.fst
          (pushExpectedFieldSegment entry.fst entry.snd stack)
      have hpoppedResults : popped.fst = entry.snd := hself.1
      have hpoppedNormalized :
          normalizeCompletionState popped.snd = normalizeCompletionState stack := hself.2
      have htail :=
        ih popped.snd hrestNodup
      change (
        (entry.fst, popped.fst)
        :: (popFieldValuesByBindings (entries.map Prod.fst)
              (entries.foldl
                (fun stack entry =>
                  pushExpectedFieldSegment entry.fst entry.snd stack)
                popped.snd)).fst,
        (popFieldValuesByBindings (entries.map Prod.fst)
          (entries.foldl
            (fun stack entry =>
              pushExpectedFieldSegment entry.fst entry.snd stack)
            popped.snd)).snd
      )
      = (entry :: entries, normalizeCompletionState stack)
      rw [htail, hpoppedResults, hpoppedNormalized]

theorem queue_popFieldValuesByBindings_foldl_pushExpectedFieldSegments
    (entries : List (FieldBinding × List (Result ResponseValue)))
    (stack : CompletionStack)
    : pairKeysNodup (entries.map (fun entry => (entry.fst.responseName, entry.snd)))
      -> completionStackFieldSegmentsNonempty stack
      -> popFieldValuesByBindings (entries.map Prod.fst)
            (entries.foldl
              (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
              stack)
          = (entries, stack) := by
  intro hnodup hstack
  rw [queue_popFieldValuesByBindings_foldl_pushExpectedFieldSegments_normalized
    entries stack hnodup]
  rw [queue_normalizeCompletionState_eq_of_fieldSegmentsNonempty stack hstack]

theorem queue_expectedScheduleSegmentSpecFieldResults_scheduleKeyForFields_singleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType responseName : Name)
    (fields : List ExecutableField)
    (source : ResolverValue ObjectRef) (fuel : Nat)
    : fields ≠ []
      -> expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            (scheduleKeyForFields parentType fields)
            {
              segment :=
                {
                  responseName := responseName
                  sources := [source]
                  childSelectionSet := childSelectionSetForFields fields
                }
              specFuels := [fuel]
            }
          = [singleFieldResultValue responseName
              (GraphQL.Execution.executeField schema resolvers variableValues fuel
                parentType source responseName fields)] := by
  intro hfields
  cases fields with
  | nil =>
      contradiction
  | cons field rest =>
      simp [expectedScheduleSegmentSpecFieldResults,
        expectedScheduleSegmentSpecFieldResultsWithFuels,
        scheduleKeyForFields]
      exact congrArg (singleFieldResultValue responseName)
        (executeField_singleton_scheduleKeyForFields_childSelectionSetForFields_eq
          (ObjectRef := ObjectRef) schema resolvers variableValues
          fuel parentType source responseName field rest)

theorem queue_expectedScheduleScopeEntries_eq_spec
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups
      -> groups.map
            (fun group =>
              (
                bindCollectedGroup parentType group |>.fst,
                expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  (scheduleKeyForFields parentType group.snd)
                  {
                    segment :=
                      {
                        responseName := group.fst
                        sources := [source]
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := [fuel]
                  }
              ))
          = groups.map
              (fun group =>
                (
                  bindCollectedGroup parentType group |>.fst,
                  [singleFieldResultValue group.fst
                    (GraphQL.Execution.executeField schema resolvers variableValues
                      fuel parentType source group.fst group.snd)]
                )) := by
  intro hnonempty
  induction groups with
  | nil =>
      rfl
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hfields : fields ≠ [] := by
        exact hnonempty responseName fields (by simp)
      have htail :
          collectedGroupsNonempty groups := by
        exact collectedGroupsNonempty_tail responseName fields groups hnonempty
      have hhead :=
        queue_expectedScheduleSegmentSpecFieldResults_scheduleKeyForFields_singleton
          (ObjectRef := ObjectRef) schema resolvers variableValues
          parentType responseName fields source fuel hfields
      simp [hhead, ih htail]

theorem queue_nameFieldValueBlocks_specEntries
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (FieldBinding × List ExecutableField))
    : nameFieldValueBlocks
        (groups.map
          (fun group =>
            (
              group.fst,
              [singleFieldResultValue group.fst.responseName
                (GraphQL.Execution.executeField schema resolvers variableValues
                  fuel group.fst.key.parentType source group.fst.responseName group.snd)]
            )))
      = groups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues fuel
              group.fst.key.parentType source group.fst.responseName group.snd]) := by
  induction groups with
  | nil =>
      rfl
  | cons group groups ih =>
      rcases group with ⟨key, fields⟩
      simp [nameFieldValueBlocks, nameFieldValues]
      constructor
      · exact queue_singleFieldResult_executeField_roundtrip
          (ObjectRef := ObjectRef) schema resolvers variableValues
          fuel key.key.parentType source key.responseName fields
      · intro a b hmem
        exact queue_singleFieldResult_executeField_roundtrip
          (ObjectRef := ObjectRef) schema resolvers variableValues
          fuel a.key.parentType source a.responseName b

theorem queue_keyedGroups_executeField_results_eq_groups
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups
      -> (groups.map (bindCollectedGroup parentType)).map
            (fun group =>
              [GraphQL.Execution.executeField schema resolvers variableValues
                fuel group.fst.key.parentType source group.fst.responseName group.snd])
          = groups.map
              (fun group =>
                [GraphQL.Execution.executeField schema resolvers variableValues
                  fuel parentType source group.fst group.snd]) := by
  intro hnonempty
  induction groups with
  | nil =>
      rfl
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hfields : fields ≠ [] := by
        exact hnonempty responseName fields (by simp)
      have htail :
          collectedGroupsNonempty groups := by
        exact collectedGroupsNonempty_tail responseName fields groups hnonempty
      cases fields with
      | nil =>
          contradiction
      | cons field rest =>
          simp [bindCollectedGroup, scheduleKeyForFields]
          intro a b hmem
          have hb : b ≠ [] := htail a b hmem
          cases b with
          | nil =>
              contradiction
          | cons field' rest' =>
              simp

theorem queue_keyedGroups_expectedEntries_eq_spec
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups
      ->  let keyedGroups := groups.map (bindCollectedGroup parentType)
          let expectedEntries :=
            keyedGroups.map
              (fun group =>
                (
                  group.fst,
                  expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := [source]
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := [fuel]
                    }
                ))
          let specEntries :=
            keyedGroups.map
              (fun group =>
                (
                  group.fst,
                  [singleFieldResultValue group.fst.responseName
                    (GraphQL.Execution.executeField schema resolvers variableValues
                      fuel group.fst.key.parentType source group.fst.responseName
                      group.snd)]
                ))
          expectedEntries = specEntries := by
  intro hnonempty
  dsimp
  induction groups with
  | nil =>
      rfl
  | cons group groups ih =>
      rcases group with ⟨responseName, fields⟩
      have hfields : fields ≠ [] := by
        exact hnonempty responseName fields (by simp)
      have htail :
          collectedGroupsNonempty groups := by
        exact collectedGroupsNonempty_tail responseName fields groups hnonempty
      cases fields with
      | nil =>
          contradiction
      | cons field rest =>
          have hhead :
              expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  (scheduleKeyForFields parentType (field :: rest))
                  { segment :=
                      { responseName := responseName
                        sources := [source]
                        childSelectionSet := childSelectionSetForFields (field :: rest) }
                    specFuels := [fuel] } =
                [singleFieldResultValue
                  responseName
                  (GraphQL.Execution.executeField schema resolvers variableValues
                    fuel parentType source
                    responseName
                    (field :: rest))] := by
            simpa [scheduleKeyForFields]
              using
              queue_expectedScheduleSegmentSpecFieldResults_scheduleKeyForFields_singleton
                  (ObjectRef := ObjectRef) schema resolvers variableValues
                  parentType responseName (field :: rest) source fuel hfields
          have hhead' :
              expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  (scheduleKeyForFields parentType (field :: rest))
                  { segment :=
                      { responseName := responseName
                        sources := [source]
                        childSelectionSet := childSelectionSetForFields (field :: rest) }
                    specFuels := [fuel] } =
                [singleFieldResultValue responseName
                  (GraphQL.Execution.executeField schema resolvers variableValues
                    fuel parentType source responseName (field :: rest))] := by
            simpa [scheduleKeyForFields] using hhead
          simp only [List.map_cons, bindCollectedGroup]
          rw [hhead', ih htail]
          simp [scheduleKeyForFields]

theorem queue_expectedEntries_pairKeysNodup
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : pairKeysNodup groups
      ->  let keyedGroups := groups.map (bindCollectedGroup parentType)
          let expectedEntries :=
            keyedGroups.map
              (fun group =>
                (
                  group.fst,
                  expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := [source]
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := [fuel]
                    }
                ))
          pairKeysNodup
            (expectedEntries.map (fun entry => (entry.fst.responseName, entry.snd))) := by
  intro hnodup
  dsimp
  have hmap :
      List.map
          (Prod.fst ∘
            (fun entry => (entry.fst.responseName, entry.snd)) ∘
              (fun group =>
                ( group.fst
                , expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    { segment :=
                        { responseName := group.fst.responseName
                          sources := [source]
                          childSelectionSet := childSelectionSetForFields group.snd }
                      specFuels := [fuel] } )) ∘
                bindCollectedGroup parentType)
          groups =
        groups.map Prod.fst := by
    induction groups with
    | nil =>
        rfl
    | cons group groups ih =>
        rcases group with ⟨responseName, fields⟩
        cases fields with
        | nil =>
            simp [Function.comp, bindCollectedGroup, scheduleKeyForFields]
        | cons head tail =>
            simp [Function.comp, bindCollectedGroup, scheduleKeyForFields]
  unfold pairKeysNodup
  simp
  rw [hmap]
  simpa [pairKeysNodup] using hnodup

theorem queue_combineScopeFieldResults_scheduleExpectedScope_singleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    : let groups :=
        collectFieldsByKey schema variableValues
          work.work.runtimeType work.work.selectionSet
      let keyedGroups :=
        groups.map
          (fun group =>
            bindCollectedGroup work.work.runtimeType group)
      let specEntries :=
        keyedGroups.map
          (fun group =>
            (
              group.fst,
              [singleFieldResultValue group.fst.responseName
                (GraphQL.Execution.executeField schema resolvers variableValues
                  work.specFuel group.fst.key.parentType work.work.source
                  group.fst.responseName group.snd)]
            ))
      combineScopeFieldResults 1 (nameFieldValueBlocks specEntries)
      = [expectedPendingChildWorkSpecResult schema resolvers variableValues work] := by
  let groups :=
    collectFieldsByKey schema variableValues
      work.work.runtimeType work.work.selectionSet
  let keyedGroups :=
    groups.map (bindCollectedGroup work.work.runtimeType)
  let specEntries :=
    keyedGroups.map
      (fun group =>
        ( group.fst
        , [singleFieldResultValue group.fst.responseName
            (GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel group.fst.key.parentType work.work.source
              group.fst.responseName group.snd)] ))
  have hnonempty :
      collectedGroupsNonempty groups := by
    simpa [groups]
      using collectFieldsByKey_collectedGroupsNonempty schema variableValues
        work.work.runtimeType work.work.selectionSet
  have hnamed :
      nameFieldValueBlocks specEntries =
        keyedGroups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel group.fst.key.parentType work.work.source
              group.fst.responseName group.snd]) := by
    simpa [specEntries, keyedGroups]
      using queue_nameFieldValueBlocks_specEntries
        (ObjectRef := ObjectRef) schema resolvers variableValues
        work.work.source work.specFuel keyedGroups
  have hraw :
      keyedGroups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel group.fst.key.parentType work.work.source
              group.fst.responseName group.snd]) =
        groups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel work.work.runtimeType work.work.source
              group.fst group.snd]) := by
    dsimp [keyedGroups]
    exact
      queue_keyedGroups_executeField_results_eq_groups
        (ObjectRef := ObjectRef) schema resolvers variableValues
        work.work.runtimeType work.work.source work.specFuel groups hnonempty
  change combineScopeFieldResults 1 (nameFieldValueBlocks specEntries) =
    [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
  rw [hnamed, hraw]
  simpa [expectedPendingChildWorkSpecResult, groups]
    using (queue_expectedPendingChildWorkSpecResult_eq_scopeSingleton
            (ObjectRef := ObjectRef) schema resolvers variableValues work).symm

theorem queue_completeScopeFrame_scheduleExpectedScope_singleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    (stack : CompletionStack)
    : completionStackFieldSegmentsNonempty stack
      ->  let groups :=
            collectFieldsByKey schema variableValues
              work.work.runtimeType work.work.selectionSet
          let boundGroups := groups.map (bindCollectedGroup work.work.runtimeType)
          let expectedEntries :=
            boundGroups.map
              (fun group =>
                (
                  group.fst,
                  expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := [work.work.source]
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := [work.specFuel]
                    }
                ))
          completeScopeFrame [1] (boundGroups.map Prod.fst)
            (expectedEntries.foldl
              (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
              stack)
          = {
            stack with
              valueStack :=
                [[expectedPendingChildWorkSpecResult schema resolvers variableValues
                    work]]
                ++ stack.valueStack
          } := by
  intro hstack
  let groups :=
    collectFieldsByKey schema variableValues
      work.work.runtimeType work.work.selectionSet
  let boundGroups := groups.map (bindCollectedGroup work.work.runtimeType)
  let expectedEntries :=
    boundGroups.map
      (fun group =>
        ( group.fst
        , expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            group.fst.key
            { segment :=
                { responseName := group.fst.responseName
                  sources := [work.work.source]
                  childSelectionSet := childSelectionSetForFields group.snd }
              specFuels := [work.specFuel] } ))
  have hnodupGroups :
      pairKeysNodup groups := by
    simpa [groups]
      using collectFieldsByKey_pairKeysNodup schema variableValues
        work.work.runtimeType work.work.selectionSet
  have hnodupEntries :
      pairKeysNodup
        (expectedEntries.map (fun entry => (entry.fst.responseName, entry.snd))) := by
    simpa [groups, boundGroups, expectedEntries]
      using queue_expectedEntries_pairKeysNodup
        (ObjectRef := ObjectRef) schema resolvers variableValues
        work.work.runtimeType work.work.source work.specFuel groups hnodupGroups
  have hpop :
      popFieldValuesByBindings (boundGroups.map Prod.fst)
          (expectedEntries.foldl
            (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
            stack) =
        (expectedEntries, stack) := by
    simpa [expectedEntries, List.map_map, Function.comp_def]
      using queue_popFieldValuesByBindings_foldl_pushExpectedFieldSegments
        expectedEntries stack hnodupEntries hstack
  have hcombine :
      combineScopeFieldResults 1 (nameFieldValueBlocks expectedEntries) =
        [expectedPendingChildWorkSpecResult schema resolvers variableValues work] := by
    let specEntries :=
      boundGroups.map
        (fun group =>
          ( group.fst
          , [singleFieldResultValue group.fst.responseName
              (GraphQL.Execution.executeField schema resolvers variableValues
                work.specFuel group.fst.key.parentType work.work.source
                group.fst.responseName group.snd)] ))
    have hentriesSpec : expectedEntries = specEntries := by
      have hnonempty :
          collectedGroupsNonempty groups := by
        simpa [groups]
          using collectFieldsByKey_collectedGroupsNonempty schema variableValues
            work.work.runtimeType work.work.selectionSet
      simpa [groups, boundGroups, expectedEntries, specEntries]
        using queue_keyedGroups_expectedEntries_eq_spec
          (ObjectRef := ObjectRef) schema resolvers variableValues
          work.work.runtimeType work.work.source work.specFuel groups hnonempty
    rw [hentriesSpec]
    simpa [groups, boundGroups, specEntries]
      using queue_combineScopeFieldResults_scheduleExpectedScope_singleton
        (ObjectRef := ObjectRef) schema resolvers variableValues work
  have hframe :=
    queue_completeScopeFrame_eq_of_pop
      [1] (boundGroups.map Prod.fst)
      (expectedEntries.foldl
        (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
        stack)
      stack expectedEntries (nameFieldValueBlocks expectedEntries)
      [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
      hpop rfl hcombine
  simpa [groups, boundGroups, expectedEntries, splitResultsByLengths] using hframe

theorem queue_completeFrames_scheduleExpectedScope_singleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (valueStack : ValueStack)
    : expectedScheduleQueueItemsNonempty queue
      -> completeFrames
            [(scheduleExpectedScope schema variableValues
                work.work.runtimeType [work.work.source] [work.specFuel]
                work.work.selectionSet queue).snd]
            {
              valueStack := valueStack
              fieldStore :=
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (scheduleExpectedScope schema variableValues
                    work.work.runtimeType [work.work.source] [work.specFuel]
                    work.work.selectionSet queue).fst).fieldStore
            }
          = {
            valueStack :=
              [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
              :: valueStack,
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue).fieldStore
          } := by
  intro hqueue
  let groups :=
    collectFieldsByKey schema variableValues
      work.work.runtimeType work.work.selectionSet
  let keyedGroups := groups.map (bindCollectedGroup work.work.runtimeType)
  let expectedEntries :=
    keyedGroups.map
      (fun group =>
        ( group.fst
        , expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            group.fst.key
            { segment :=
                { responseName := group.fst.responseName
                  sources := [work.work.source]
                  childSelectionSet := childSelectionSetForFields group.snd }
              specFuels := [work.specFuel] } ))
  let baseStack : CompletionStack :=
    { valueStack := valueStack
      fieldStore :=
        (expectedScheduleQueueCompletionStack schema resolvers variableValues
          queue).fieldStore }
  have hfold :
      ∀ (stack0 : CompletionStack),
        keyedGroups.foldl
            (fun stack group =>
              pushExpectedFieldSegment group.fst
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  group.fst.key
                  { segment :=
                      { responseName := group.fst.responseName
                        sources := [work.work.source]
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := [work.specFuel] })
                stack)
            stack0 =
          expectedEntries.foldl
            (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
            stack0 := by
    subst expectedEntries
    intro stack0
    induction keyedGroups generalizing stack0 with
    | nil =>
        rfl
    | cons group keyedGroups ih =>
        simp [ih]
  have hfieldStoreFoldIndependent :
      ∀ (groups0 : List (FieldBinding × List ExecutableField))
        (stack0 : CompletionStack),
        (groups0.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst.key
                { segment :=
                    { responseName := group.fst.responseName
                      sources := [work.work.source]
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := [work.specFuel] })
              stack)
          stack0).fieldStore =
        (groups0.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst.key
                { segment :=
                    { responseName := group.fst.responseName
                      sources := [work.work.source]
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := [work.specFuel] })
              stack)
          { valueStack := []
            fieldStore := stack0.fieldStore }).fieldStore := by
    intro groups0
    induction groups0 with
    | nil =>
        intro stack0
        rfl
    | cons group groups0 ih =>
        intro stack0
        simpa [pushExpectedFieldSegment]
          using ih
            {
              valueStack := stack0.valueStack
              fieldStore :=
                pushExpectedFieldSegmentInStore group.fst
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    {
                      segment :=
                        {
                          responseName := group.fst.responseName
                          sources := [work.work.source]
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := [work.specFuel]
                    })
                  stack0.fieldStore
            }
  have hkeyedStore :
      (expectedScheduleQueueCompletionStack schema resolvers variableValues
        (scheduleExpectedScope schema variableValues
          work.work.runtimeType [work.work.source] [work.specFuel]
          work.work.selectionSet queue).fst).fieldStore =
        (keyedGroups.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst.key
                { segment :=
                    { responseName := group.fst.responseName
                      sources := [work.work.source]
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := [work.specFuel] })
              stack)
          { valueStack := []
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue).fieldStore }).fieldStore := by
    have hfull :
        (expectedScheduleQueueCompletionStack schema resolvers variableValues
          (scheduleExpectedScope schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue).fst).fieldStore =
          (keyedGroups.foldl
            (fun stack group =>
              pushExpectedFieldSegment group.fst
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  group.fst.key
                  { segment :=
                      { responseName := group.fst.responseName
                        sources := [work.work.source]
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := [work.specFuel] })
                stack)
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              queue)).fieldStore := by
      simpa [scheduleExpectedScope, groups, keyedGroups]
        using congrArg CompletionState.fieldStore
          (queue_expectedScheduleQueueCompletionStack_scheduleExpectedScopeGroups
            (ObjectRef := ObjectRef) schema resolvers variableValues
            [work.work.source] [work.specFuel] keyedGroups queue)
    exact hfull.trans
      (hfieldStoreFoldIndependent keyedGroups
        (expectedScheduleQueueCompletionStack schema resolvers variableValues queue))
  have hstate :
      { valueStack := valueStack
        fieldStore :=
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            (scheduleExpectedScope schema variableValues
              work.work.runtimeType [work.work.source] [work.specFuel]
              work.work.selectionSet queue).fst).fieldStore } =
        expectedEntries.foldl
          (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
          baseStack := by
    have hnormalizeGeneral :
        ∀ (groups0 : List (FieldBinding × List ExecutableField))
          (stack0 : CompletionStack),
          groups0.foldl
              (fun stack group =>
                pushExpectedFieldSegment group.fst
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst.key
                    { segment :=
                        { responseName := group.fst.responseName
                          sources := [work.work.source]
                          childSelectionSet := childSelectionSetForFields group.snd }
                      specFuels := [work.specFuel] })
                  stack)
              stack0 =
            { valueStack := stack0.valueStack
              fieldStore :=
                (groups0.foldl
                  (fun stack group =>
                    pushExpectedFieldSegment group.fst
                      (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                        group.fst.key
                        { segment :=
                            { responseName := group.fst.responseName
                              sources := [work.work.source]
                              childSelectionSet := childSelectionSetForFields group.snd }
                          specFuels := [work.specFuel] })
                      stack)
                  { valueStack := []
                    fieldStore := stack0.fieldStore }).fieldStore } := by
      intro groups0
      induction groups0 with
      | nil =>
          intro stack0
          rfl
      | cons group groups0 ih =>
          intro stack0
          simpa [pushExpectedFieldSegment]
            using ih
              {
                valueStack := stack0.valueStack
                fieldStore :=
                  pushExpectedFieldSegmentInStore group.fst
                    (expectedScheduleSegmentSpecFieldResults schema resolvers
                      variableValues group.fst.key
                      {
                        segment :=
                          {
                            responseName := group.fst.responseName
                            sources := [work.work.source]
                            childSelectionSet := childSelectionSetForFields group.snd
                          }
                        specFuels := [work.specFuel]
                      })
                    stack0.fieldStore
              }
    have hnormalize := hnormalizeGeneral keyedGroups baseStack
    have hkeyedState :
        { valueStack := valueStack
          fieldStore :=
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              (scheduleExpectedScope schema variableValues
                work.work.runtimeType [work.work.source] [work.specFuel]
                work.work.selectionSet queue).fst).fieldStore } =
          keyedGroups.foldl
            (fun stack group =>
              pushExpectedFieldSegment group.fst
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  group.fst.key
                  { segment :=
                      { responseName := group.fst.responseName
                        sources := [work.work.source]
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := [work.specFuel] })
                stack)
            baseStack := by
      rw [hnormalize]
      have hstateStore :=
        congrArg
          (fun fs => ({ valueStack := valueStack, fieldStore := fs } : CompletionStack))
          hkeyedStore
      simpa [baseStack] using hstateStore
    exact hkeyedState.trans (hfold baseStack)
  have hbaseNonempty :
      completionStackFieldSegmentsNonempty baseStack := by
    simpa [baseStack, completionStackFieldSegmentsNonempty]
      using queue_expectedScheduleQueueCompletionStack_fieldSegmentsNonempty
        (ObjectRef := ObjectRef) schema resolvers variableValues queue hqueue
  rw [hstate]
  simpa [completeFrames, scheduleExpectedScope, groups, keyedGroups, expectedEntries,
    baseStack]
    using queue_completeScopeFrame_scheduleExpectedScope_singleton
      (ObjectRef := ObjectRef) schema resolvers variableValues work baseStack
      hbaseNonempty

theorem queue_completeFrames_scheduleExpectedPendingChildWork_singleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWork ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (valueStack : ValueStack)
    : expectedScheduleQueueItemsNonempty queue
      -> completeFrames
            (scheduleExpectedPendingChildWork schema variableValues [work]
              queue).snd.reverse
            {
              valueStack := valueStack
              fieldStore :=
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (scheduleExpectedPendingChildWork schema variableValues [work]
                    queue).fst).fieldStore
            }
          = {
            valueStack :=
              [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
              :: valueStack
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue).fieldStore
          } := by
  intro hqueue
  simpa [scheduleExpectedPendingChildWork]
    using queue_completeFrames_scheduleExpectedScope_singleton (ObjectRef := ObjectRef)
      schema resolvers variableValues work queue valueStack hqueue

theorem queue_completeFrames_scheduleExpectedPendingChildWork
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    (valueStack : ValueStack)
    : expectedScheduleQueueItemsNonempty queue
      -> completeFrames
            (scheduleExpectedPendingChildWork schema variableValues work
              queue).snd.reverse
            {
              valueStack := valueStack
              fieldStore :=
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (scheduleExpectedPendingChildWork schema variableValues work
                    queue).fst).fieldStore
            }
          = {
            valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers variableValues
                work).valueStack
              ++ valueStack
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue).fieldStore
          } := by
  intro hqueue
  induction work generalizing queue valueStack with
  | nil =>
      rfl
  | cons work rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet queue
      have hheadQueue :
          expectedScheduleQueueItemsNonempty head.fst := by
        simpa [head]
          using scheduleExpectedScope_itemsNonempty
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet queue hqueue
      have htail :=
        ih head.fst valueStack hheadQueue
      have hheadFrame :=
        queue_completeFrames_scheduleExpectedScope_singleton
          (ObjectRef := ObjectRef) schema resolvers variableValues work queue
          ((expectedPendingChildWorkCompletionStack schema resolvers variableValues rest).valueStack ++
            valueStack)
          hqueue
      calc
        completeFrames
              (List.reverse
                (scheduleExpectedPendingChildWork schema variableValues (work :: rest)
                  queue).snd)
              {
                valueStack := valueStack
                fieldStore :=
                  (expectedScheduleQueueCompletionStack schema resolvers variableValues
                    (scheduleExpectedPendingChildWork schema variableValues (work :: rest)
                      queue).fst).fieldStore
              }
            = completeFrames [head.snd]
                {
                  valueStack :=
                    (expectedPendingChildWorkCompletionStack schema resolvers
                      variableValues rest).valueStack
                    ++ valueStack
                  fieldStore :=
                    (expectedScheduleQueueCompletionStack schema resolvers variableValues
                      head.fst).fieldStore
                } := by
          simp [scheduleExpectedPendingChildWork, head, List.reverse_cons,
            queue_completeFrames_append, htail]
        _ = {
            valueStack :=
              (expectedPendingChildWorkCompletionStack schema resolvers variableValues
                (work :: rest)).valueStack
              ++ valueStack
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                queue).fieldStore
          } := by
          simpa [expectedPendingChildWorkCompletionStack,
            expectedPendingChildWorkCompletion]
            using hheadFrame

theorem queue_enqueueExpectedScheduleItems_scheduleExpectedPendingChildWork
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (base queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueItemsNonempty base
      -> expectedScheduleQueueKeysDistinct base
      -> enqueueExpectedScheduleItems queue
            (scheduleExpectedPendingChildWork schema variableValues work base).fst
          = (scheduleExpectedPendingChildWork schema variableValues work
              (enqueueExpectedScheduleItems queue base)).fst := by
  intro hbaseNonempty hbaseDistinct
  induction work generalizing base queue with
  | nil =>
      rfl
  | cons work rest ih =>
      let head :=
        scheduleExpectedScope schema variableValues work.work.runtimeType
          [work.work.source] [work.specFuel] work.work.selectionSet base
      have hheadNonempty :
          expectedScheduleQueueItemsNonempty head.fst := by
        simpa [head]
          using scheduleExpectedScope_itemsNonempty
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet base hbaseNonempty
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct head.fst := by
        simpa [head]
          using scheduleExpectedScope_keysDistinct
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet base hbaseDistinct
      have htail :=
        ih head.fst queue hheadNonempty hheadDistinct
      have hheadReplay :=
        queue_enqueueExpectedScheduleItems_scheduleExpectedScope
          (ObjectRef := ObjectRef) schema variableValues
          work.work.runtimeType [work.work.source] [work.specFuel]
          work.work.selectionSet base queue hbaseNonempty hbaseDistinct
      simp [scheduleExpectedPendingChildWork]
      rw [htail]
      rw [hheadReplay]

theorem queue_enqueueExpectedScheduleItems_scheduleExpectedPendingChildWork_empty
    (schema : Schema) (variableValues : VariableValues)
    (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : enqueueExpectedScheduleItems queue
        (scheduleExpectedPendingChildWork schema variableValues work []).fst
      = (scheduleExpectedPendingChildWork schema variableValues work queue).fst := by
  simpa [enqueueExpectedScheduleItems]
    using queue_enqueueExpectedScheduleItems_scheduleExpectedPendingChildWork
      (ObjectRef := ObjectRef) schema variableValues work
      ([] : ExpectedScheduleQueue ObjectRef) queue
      (by simp [expectedScheduleQueueItemsNonempty])
      (by simp [expectedScheduleQueueKeysDistinct])

theorem
    queue_expectedScheduleQueueCompletionStack_scheduleExpectedPendingChildWork_enqueue_empty
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (work : ExpectedPendingChildWorkList ObjectRef)
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (enqueueExpectedScheduleItems queue
          (scheduleExpectedPendingChildWork schema variableValues work []).fst)
      = {
        valueStack := []
        fieldStore :=
          (expectedScheduleQueueCompletionStack schema resolvers variableValues
            (scheduleExpectedPendingChildWork schema variableValues work
              queue).fst).fieldStore
      } := by
  rw [queue_enqueueExpectedScheduleItems_scheduleExpectedPendingChildWork_empty]
  simp [expectedScheduleQueueCompletionStack]

theorem queue_completeFrames_executeScheduleItem_lookup_some_direct
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemFuelsAligned item
      -> expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item
      -> expectedScheduleQueueItemsNonempty rest
      -> completeFrames
            (executeScheduleItem schema (ResolverMap.fromSpecResolvers resolvers)
              variableValues item.toScheduleItem).snd.reverse
            {
              valueStack := []
              fieldStore :=
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (scheduleExpectedPendingChildWork schema variableValues
                    (expectedPendingChildWorkForItem schema resolvers
                      fieldDefinition.outputType item variableValues)
                    rest).fst).fieldStore
            }
          = expectedScheduleQueueCompletionStack schema resolvers variableValues
              (item :: rest) := by
  intro hlookup haligned hready hrestNonempty
  let work :=
    expectedPendingChildWorkForItem schema resolvers fieldDefinition.outputType item
      variableValues
  let expectedScheduled :=
    scheduleExpectedPendingChildWork schema variableValues work rest
  let resolved :=
    item.toScheduleItem.sources.map (fun source =>
      GraphQL.Execution.coerceAndResolveFieldValue schema resolvers variableValues
        fieldDefinition item.key.parentType item.key.fieldName item.key.arguments
        source)
  let built :=
    buildFieldSlots schema fieldDefinition.outputType item.toScheduleItem.segments
      resolved
  let runtimeScheduled :=
    schedulePendingChildWork schema variableValues built.fst []
  have htoPending :
      expectedPendingChildWorkToPending work = built.fst := by
    simpa [GraphQL.Execution.resolveFieldValueByName, hlookup, work, built, resolved]
      using slots_expectedPendingChildWorkForItem_toPending_eq_buildFieldSlots
        (ObjectRef := ObjectRef) schema resolvers variableValues
        fieldDefinition.outputType item
        haligned hready
  have hframesEmpty :
      (scheduleExpectedPendingChildWork schema variableValues work []).snd =
        runtimeScheduled.snd := by
    have hframes :=
      scope_expectedChildQueueForItem_frames_fromSpecResolvers_lookup_some
        (ObjectRef := ObjectRef) schema resolvers variableValues item
        fieldDefinition hlookup haligned hready
    simpa [expectedChildQueueForItem, hlookup, work, runtimeScheduled, built,
      resolved] using hframes
  have hframesDirect :
      runtimeScheduled.snd = expectedScheduled.snd := by
    have hindependent :=
      scheduleExpectedPendingChildWork_frames_independent
        (ObjectRef := ObjectRef) schema variableValues work [] rest
    exact hframesEmpty.symm.trans hindependent
  have hframesDirect' :
      (schedulePendingChildWork schema variableValues
          (buildFieldSlots schema fieldDefinition.outputType
            item.toScheduleItem.segments
            (item.toScheduleItem.sources.map (fun source =>
              GraphQL.Execution.coerceAndResolveFieldValue schema resolvers variableValues
                fieldDefinition item.toScheduleItem.key.parentType
                item.toScheduleItem.key.fieldName item.toScheduleItem.key.arguments
                source))).fst
          []).snd =
        expectedScheduled.snd := by
    simpa [runtimeScheduled, built, resolved, ExpectedQueueItem.toScheduleItem]
      using hframesDirect
  have hchild :
      completeFrames expectedScheduled.snd.reverse
          { valueStack := []
            fieldStore :=
              (expectedScheduleQueueCompletionStack schema resolvers variableValues
                expectedScheduled.fst).fieldStore } =
        { valueStack :=
            (expectedPendingChildWorkCompletionStack schema resolvers variableValues
              work).valueStack
          fieldStore :=
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              rest).fieldStore } := by
    simpa [expectedScheduled]
      using queue_completeFrames_scheduleExpectedPendingChildWork
        (ObjectRef := ObjectRef) schema resolvers variableValues work rest []
        hrestNonempty
  have hfield :=
    queue_completeFrames_fieldFrame_expectedItem_lookup_some
      (ObjectRef := ObjectRef) schema resolvers variableValues item rest
      fieldDefinition hlookup haligned hready
  rw [scope_executeScheduleItem_fromSpecResolvers_lookup_some
    (ObjectRef := ObjectRef) schema resolvers variableValues item.toScheduleItem
    fieldDefinition hlookup]
  simp [List.reverse_cons, queue_completeFrames_append]
  rw [hframesDirect']
  rw [hchild]
  simpa [work, ExpectedQueueItem.toScheduleItem] using hfield

theorem queue_completeFrames_executeScheduleItem_lookup_some_enqueued
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemFuelsAligned item
      -> expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item
      -> expectedScheduleQueueItemsNonempty rest
      -> completeFrames
            (executeScheduleItem schema (ResolverMap.fromSpecResolvers resolvers)
              variableValues item.toScheduleItem).snd.reverse
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              (enqueueExpectedScheduleItems rest
                (expectedChildQueueForItem schema resolvers variableValues item).fst))
          = expectedScheduleQueueCompletionStack schema resolvers variableValues
              (item :: rest) := by
  intro hlookup haligned hready hrestNonempty
  let work :=
    expectedPendingChildWorkForItem schema resolvers fieldDefinition.outputType item
      variableValues
  have hstack :
      expectedScheduleQueueCompletionStack schema resolvers variableValues
          (enqueueExpectedScheduleItems rest
            (expectedChildQueueForItem schema resolvers variableValues item).fst) =
        { valueStack := []
          fieldStore :=
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              (scheduleExpectedPendingChildWork schema variableValues work rest).fst).fieldStore } := by
    simpa [expectedChildQueueForItem, hlookup, work]
      using
        queue_expectedScheduleQueueCompletionStack_scheduleExpectedPendingChildWork_enqueue_empty
          (ObjectRef := ObjectRef) schema resolvers variableValues work rest
  rw [hstack]
  simpa [work]
    using queue_completeFrames_executeScheduleItem_lookup_some_direct
      (ObjectRef := ObjectRef) schema resolvers variableValues item rest
      fieldDefinition hlookup haligned hready hrestNonempty

theorem queue_expectedDrainStepMatchesSpec_lookup_some
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    (fieldDefinition : FieldDefinition)
    : schema.lookupField item.key.parentType item.key.fieldName = some fieldDefinition
      -> expectedQueueItemFuelsAligned item
      -> expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item
      -> expectedScheduleQueueItemsNonempty rest
      -> expectedDrainStepMatchesSpec schema resolvers variableValues item rest := by
  intro hlookup haligned hready hrestNonempty
  unfold expectedDrainStepMatchesSpec
  constructor
  · exact
      scope_expectedChildQueueForItem_fromSpecResolvers_lookup_some
        (ObjectRef := ObjectRef) schema resolvers variableValues item
        fieldDefinition hlookup haligned hready
  · exact
      queue_completeFrames_executeScheduleItem_lookup_some_enqueued
        (ObjectRef := ObjectRef) schema resolvers variableValues item rest
        fieldDefinition hlookup haligned hready hrestNonempty

theorem queue_expectedDrainStepMatchesSpec_of_ready
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (item : ExpectedQueueItem ObjectRef)
    (rest : ExpectedScheduleQueue ObjectRef)
    : expectedQueueItemFuelsAligned item
      -> expectedScheduleQueueItemsNonempty rest
      -> expectedQueueItemStepFuelReady schema item
      -> expectedDrainStepMatchesSpec schema resolvers variableValues item rest := by
  intro haligned hrestNonempty hready
  unfold expectedQueueItemStepFuelReady at hready
  cases hlookup : schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      exact queue_expectedDrainStepMatchesSpec_lookup_none
        (ObjectRef := ObjectRef) schema resolvers variableValues item rest
        haligned hlookup
  | some fieldDefinition =>
      have hfieldReady :
          expectedQueueItemFieldFuelReadyFor fieldDefinition.outputType item := by
        simpa [hlookup] using hready
      exact queue_expectedDrainStepMatchesSpec_lookup_some
        (ObjectRef := ObjectRef) schema resolvers variableValues item rest
        fieldDefinition hlookup haligned hfieldReady hrestNonempty

theorem queue_drainLoopMatchesExpectedSpec_of_ready
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    : ∀ (breadthFuel : Nat) (queue : ExpectedScheduleQueue ObjectRef),
        expectedDrainQueueReady schema resolvers variableValues breadthFuel queue
        -> drainLoopMatchesExpectedSpec schema resolvers variableValues breadthFuel
            queue := by
  exact queue_drainLoopMatchesExpectedSpec_of_ready_and_stepSound
    (ObjectRef := ObjectRef) schema resolvers variableValues
    (fun item rest haligned _hnonempty _hdistinct hitemReady =>
      let hrestNonempty : expectedScheduleQueueItemsNonempty rest := by
        intro restItem hrestItem
        exact _hnonempty restItem (by simp [hrestItem])
      queue_expectedDrainStepMatchesSpec_of_ready
        (ObjectRef := ObjectRef) schema resolvers variableValues item rest
        (haligned item (by simp)) hrestNonempty hitemReady)

end ExecutionBreadth

end Algorithms

end GraphQL
