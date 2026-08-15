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
    (segmentLengths : List Nat) (fieldKeys : List ScheduleKey)
    (stack stack' : CompletionStack)
    (entries : List (ScheduleKey × List (Result ResponseValue)))
    (fieldResults : ObjectFieldSegments)
    (objectResults : List (Result ResponseValue))
    : popFieldValuesByKeys fieldKeys stack = (entries, stack')
      -> nameFieldValueBlocks entries = fieldResults
      -> combineScopeFieldResults segmentLengths.sum fieldResults = objectResults
      -> completeScopeFrame segmentLengths fieldKeys stack
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
    (source : ResolverValue ObjectRef)
    (responseName : Name) (fields : List ExecutableField)
    : GraphQL.Execution.singleFieldResult responseName
        (singleFieldResultValue responseName
          (GraphQL.Execution.executeField schema resolvers variableValues fuel
            source responseName fields))
      = GraphQL.Execution.executeField schema resolvers variableValues fuel
          source responseName fields := by
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
          cases hlookup : schema.lookupField field.parentType field.fieldName with
          | none =>
              simp [GraphQL.Execution.executeField, hlookup, singleFieldResultValue,
                GraphQL.Execution.singleFieldResult]
          | some fieldDefinition =>
              cases hresolve
                    : GraphQL.Execution.coerceAndResolveFieldValue schema resolvers
                        variableValues fieldDefinition field.parentType field.fieldName
                        field.arguments source with
              | none =>
                  simp [GraphQL.Execution.executeField, hlookup, hresolve,
                    queue_singleFieldResultValue_singleFieldResult]
              | some resolved =>
                  simp [GraphQL.Execution.executeField, hlookup, hresolve,
                    queue_singleFieldResultValue_singleFieldResult]

theorem queue_scheduleKeyEqBool_false_of_responseName_ne {left right : ScheduleKey}
    : left.responseName ≠ right.responseName -> scheduleKeyEqBool left right = false := by
  intro hne
  cases h : scheduleKeyEqBool left right with
  | false =>
      rfl
  | true =>
      have heq : left = right :=
        scheduleKeyEqBool_eq h
      exact False.elim (hne (by simp [heq]))

@[simp]
theorem queue_scheduleKeyForFields_responseName
    (parentType responseName : Name) (fields : List ExecutableField)
    : (scheduleKeyForFields parentType responseName fields).responseName
      = responseName := by
  cases fields <;> rfl

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
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : groups.foldr
        (fun group tail =>
          Result.combine List.append
            (GraphQL.Execution.executeField schema resolvers variableValues fuel source
              group.fst group.snd)
            tail)
        (.ok ([], 0))
      = GraphQL.Execution.executeCollectedFields schema resolvers variableValues
          fuel source groups := by
  induction groups with
  | nil =>
      simp [GraphQL.Execution.executeCollectedFields]
  | cons group groups ih =>
      rw [GraphQL.Execution.executeCollectedFields]
      simp [ih]

theorem queue_combineScopeFieldResults_singleton_executeCollectedFields
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : combineScopeFieldResults 1
        (groups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues fuel source
              group.fst group.snd]))
      = [objectResultFromFields
          (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel source groups)] := by
  calc
    combineScopeFieldResults 1
          (groups.map
            (fun group =>
              [GraphQL.Execution.executeField schema resolvers variableValues fuel source
                group.fst group.snd]))
        = [objectResultFromFields
            ((groups.map
                (fun group =>
                  GraphQL.Execution.executeField schema resolvers variableValues fuel
                    source group.fst group.snd)).foldr
              (fun block tail => Result.combine List.append block tail)
              (.ok ([], 0)))] := by
      have hsingleton :
          groups.map (fun group =>
              List.singleton
                (GraphQL.Execution.executeField schema resolvers
                  variableValues fuel source group.fst group.snd)) =
            groups.map (fun group =>
              [GraphQL.Execution.executeField schema resolvers
                variableValues fuel source group.fst group.snd]) := by
        induction groups with
        | nil =>
            rfl
        | cons group groups ih =>
            simp [List.singleton]
      rw [← hsingleton]
      simpa [List.map_map, Function.comp_def] using
        (queue_combineScopeFieldResults_singleton
          (blocks := groups.map (fun group =>
            GraphQL.Execution.executeField schema resolvers variableValues fuel source
              group.fst group.snd)))
    _ = [objectResultFromFields
          (GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel source groups)] := by
      have hfoldMap :
          (groups.map (fun group =>
            GraphQL.Execution.executeField schema resolvers variableValues fuel source
              group.fst group.snd)).foldr
            (fun block tail => Result.combine List.append block tail)
            (.ok ([], 0)) =
          GraphQL.Execution.executeCollectedFields schema resolvers variableValues
            fuel source groups := by
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
                work.specFuel work.work.source group.fst group.snd])) := by
  simp [expectedPendingChildWorkSpecResult]
  rw [queue_combineScopeFieldResults_singleton_executeCollectedFields
    (ObjectRef := ObjectRef) schema resolvers variableValues work.specFuel
    work.work.source
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
                      singleFieldResultValue key.responseName GraphQL.Execution.outOfFuel =
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
    using
      queue_completeExecutionTrace_singleton_empty_scope

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
    simp [expectedChildQueueForItem, executeScheduleItem, hlookup,
      ExpectedQueueItem.toScheduleItem,
      completeFrames, completeFieldFrame, expectedScheduleQueueCompletionStack,
      expectedQueueItemCompletion]
    constructor
    · simpa [expectedScheduleQueueCompletionStack, enqueueExpectedScheduleItems,
        ExpectedQueueItem.toScheduleItem, ScheduleItem.sources] using
        congrArg (fun completed => completed.snd.valueStack) hstack
    · constructor
      · have hfstack := congrArg Prod.fst hstack
        simp [ExpectedQueueItem.toScheduleItem] at hfstack ⊢
        exact
          Eq.trans
            (congrArg
              (splitResultsByLengths item.toScheduleItem.segmentLengths)
              hfstack)
            (hsegments.trans hexpected.symm)
      · simpa [expectedScheduleQueueCompletionStack, enqueueExpectedScheduleItems,
          ExpectedQueueItem.toScheduleItem, ScheduleItem.sources] using
          congrArg (fun completed => completed.snd.fieldStore) hstack

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
            [.field item.key fieldDefinition.outputType item.toScheduleItem.segmentLengths
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
    simpa [GraphQL.Execution.resolveFieldValueByName, hlookup, blocks, restStack] using
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
  change
    completeFieldFrame item.key fieldDefinition.outputType
        item.toScheduleItem.segmentLengths
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
  simp [hsplit, expectedScheduleQueueCompletionStack, expectedQueueItemCompletion,
    blocks]

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
  simpa [executed, expectedChild, expectedScheduleQueueToQueue] using
    hmid.trans hcomplete

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
      = pushExpectedFieldSegment key
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
          pushExpectedFieldSegmentInStore, hkey, List.map_append, List.reverse_append]
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
            pushExpectedFieldSegment key
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
                  pushExpectedFieldSegment key
                    (expectedScheduleSegmentSpecFieldResults schema resolvers
                      variableValues key segment)
                    stack)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (enqueueExpectedSegment key segment queue)) :=
          ih _
        _ = rest.foldl
              (fun stack segment =>
                pushExpectedFieldSegment key
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    key segment)
                  stack)
              (pushExpectedFieldSegment key
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  key segment)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  queue)) := by
          rw [queue_expectedScheduleQueueCompletionStack_enqueueExpectedSegment_eq_push]
        _ = (segment :: rest).foldl
              (fun stack segment =>
                pushExpectedFieldSegment key
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
                pushExpectedFieldSegment item.key
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
                      pushExpectedFieldSegment item.key
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
                    pushExpectedFieldSegment item.key
                      (expectedScheduleSegmentSpecFieldResults schema resolvers
                        variableValues item.key segment)
                      stack)
                  stack)
              (item.segments.foldl
                (fun stack segment =>
                  pushExpectedFieldSegment item.key
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
                    pushExpectedFieldSegment item.key
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
    (groups : List (ScheduleKey × List ExecutableField))
    (queue : ExpectedScheduleQueue ObjectRef)
    : expectedScheduleQueueCompletionStack schema resolvers variableValues
        (groups.foldl
          (fun queue group =>
            enqueueExpectedSegment group.fst
              {
                segment :=
                  {
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
                group.fst
                {
                  segment :=
                    {
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
      calc
        expectedScheduleQueueCompletionStack schema resolvers variableValues
              (groups.foldl
                (fun queue group =>
                  enqueueExpectedSegment group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    }
                    queue)
                (enqueueExpectedSegment group.fst
                  {
                    segment :=
                      {
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
                      variableValues group.fst
                      {
                        segment :=
                          {
                            sources := sources
                            childSelectionSet := childSelectionSetForFields group.snd
                          }
                        specFuels := specFuels
                      })
                    stack)
                (expectedScheduleQueueCompletionStack schema resolvers variableValues
                  (enqueueExpectedSegment group.fst
                    {
                      segment :=
                        {
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
                    group.fst
                    {
                      segment :=
                        {
                          sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := specFuels
                    })
                  stack)
              (pushExpectedFieldSegment group.fst
                (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  group.fst
                  {
                    segment :=
                      {
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
                    group.fst
                    {
                      segment :=
                        {
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

theorem queue_foldl_enqueueExpectedSegment_nil_eq_map_singletons
    (entries : List (ScheduleKey × ExpectedQueueSegment ObjectRef))
    : (entries.map (fun entry => entry.fst.responseName)).Nodup
      -> entries.foldl
            (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
            ([] : ExpectedScheduleQueue ObjectRef)
          = entries.map
              (fun entry =>
                ({ key := entry.fst, segments := [entry.snd] }
                  : ExpectedQueueItem ObjectRef)) := by
  intro hnodup
  induction entries with
  | nil =>
      rfl
  | cons entry entries ih =>
      have hnodup' :
          entry.fst.responseName ∉
              entries.map (fun entry => entry.fst.responseName) ∧
            (entries.map (fun entry => entry.fst.responseName)).Nodup := by
        simpa using hnodup
      have hheadNotMem :
          entry.fst.responseName ∉
            entries.map (fun entry => entry.fst.responseName) :=
        hnodup'.1
      have htailNodup :
          (entries.map (fun entry => entry.fst.responseName)).Nodup :=
        hnodup'.2
      have habsent :
          ∀ later, later ∈ entries ->
            scheduleKeyEqBool later.fst entry.fst = false := by
        intro later hlater
        have hne : later.fst.responseName ≠ entry.fst.responseName := by
          intro heq
          apply hheadNotMem
          exact List.mem_map.mpr ⟨later, hlater, heq⟩
        exact queue_scheduleKeyEqBool_false_of_responseName_ne hne
      have hcons :=
        queue_foldl_enqueueExpectedSegment_cons_of_absent
          (ObjectRef := ObjectRef) entries
          ({ key := entry.fst, segments := [entry.snd] } :
            ExpectedQueueItem ObjectRef)
          ([] : ExpectedScheduleQueue ObjectRef) habsent
      simp only [List.foldl_cons, List.map_cons]
      rw [show enqueueExpectedSegment entry.fst entry.snd
            ([] : ExpectedScheduleQueue ObjectRef) =
          [({ key := entry.fst, segments := [entry.snd] } :
            ExpectedQueueItem ObjectRef)] by rfl]
      rw [hcons]
      rw [ih htailNodup]

theorem queue_enqueueExpectedScheduleItems_map_singletons
    (entries : List (ScheduleKey × ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : enqueueExpectedScheduleItems queue
        (entries.map
          (fun entry =>
            ({ key := entry.fst, segments := [entry.snd] }
              : ExpectedQueueItem ObjectRef)))
      = entries.foldl
          (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
          queue := by
  induction entries generalizing queue with
  | nil =>
      rfl
  | cons entry entries ih =>
      simp [enqueueExpectedScheduleItems, enqueueExpectedSegments]
      exact ih (enqueueExpectedSegment entry.fst entry.snd queue)

theorem queue_enqueueExpectedScheduleItems_foldl_enqueueExpectedSegment_nil_of_nodup
    (entries : List (ScheduleKey × ExpectedQueueSegment ObjectRef))
    (queue : ExpectedScheduleQueue ObjectRef)
    : (entries.map (fun entry => entry.fst.responseName)).Nodup
      -> enqueueExpectedScheduleItems queue
            (entries.foldl
              (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
              [])
          = entries.foldl
              (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
              queue := by
  intro hnodup
  rw [queue_foldl_enqueueExpectedSegment_nil_eq_map_singletons
    (ObjectRef := ObjectRef) entries hnodup]
  exact queue_enqueueExpectedScheduleItems_map_singletons
    (ObjectRef := ObjectRef) entries queue

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
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let entries : List (ScheduleKey × ExpectedQueueSegment ObjectRef) :=
    groups.map (fun group =>
      ( scheduleKeyForFields parentType group.fst group.snd
      , { segment :=
            { sources := sources
              childSelectionSet := childSelectionSetForFields group.snd }
          specFuels := specFuels } ))
  have hnodup :
      (entries.map (fun entry => entry.fst.responseName)).Nodup := by
    have hmap :
        groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd).responseName) =
          groups.map Prod.fst := by
      induction groups with
      | nil =>
          rfl
      | cons group groups ih =>
          rcases group with ⟨responseName, fields⟩
          have hhead :
              (scheduleKeyForFields parentType responseName fields).responseName =
                responseName := by
            exact queue_scheduleKeyForFields_responseName parentType responseName fields
          simp
    have hentriesMap :
        entries.map (fun entry => entry.fst.responseName) =
          groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd).responseName) := by
      simp [entries]
    rw [hentriesMap, hmap]
    simpa [groups, pairKeysNodup] using
      collectFieldsByKey_pairKeysNodup schema variableValues parentType selectionSet
  have hreplay :=
    queue_enqueueExpectedScheduleItems_foldl_enqueueExpectedSegment_nil_of_nodup
      (ObjectRef := ObjectRef) entries queue hnodup
  have hfold :
      ∀ init,
        entries.foldl
            (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
            init =
          ((groups.map fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd)).foldl
            (fun queue group =>
              enqueueExpectedSegment group.fst
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := specFuels }
                queue)
            init) := by
    intro init
    have hfoldRaw :
        (groups.map (fun group =>
            ( scheduleKeyForFields parentType group.fst group.snd
            , ExpectedQueueSegment.mk
                (ScheduleSegment.mk sources
                  (childSelectionSetForFields group.snd))
                specFuels))).foldl
            (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
            init =
          ((groups.map fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd)).foldl
            (fun queue group =>
              enqueueExpectedSegment group.fst
                { segment :=
                    { sources := sources
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := specFuels }
                queue)
            init) := by
      induction groups generalizing init with
      | nil =>
          rfl
      | cons group groups ih =>
          rcases group with ⟨responseName, fields⟩
          simp [ih]
    simpa [entries] using hfoldRaw
  calc
    enqueueExpectedScheduleItems queue
          (scheduleExpectedScope schema variableValues parentType sources
            specFuels selectionSet []).fst
        = enqueueExpectedScheduleItems queue
            (entries.foldl
              (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
              []) := by
      exact congrArg (enqueueExpectedScheduleItems queue) (hfold []).symm
    _ = entries.foldl
          (fun queue entry => enqueueExpectedSegment entry.fst entry.snd queue)
          queue :=
      hreplay
    _ = (scheduleExpectedScope schema variableValues parentType sources
          specFuels selectionSet queue).fst := by
      exact hfold queue

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
        simpa [enqueueExpectedSegment, enqueueExpectedScheduleItems,
          hkeyFalse] using htail

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
  let keyedGroups :=
    groups.map (fun group =>
      (scheduleKeyForFields parentType group.fst group.snd, group.snd))
  have hfold :
      ∀ (groups0 : List (ScheduleKey × List ExecutableField))
        (base0 : ExpectedScheduleQueue ObjectRef),
        expectedScheduleQueueItemsNonempty base0 ->
        expectedScheduleQueueKeysDistinct base0 ->
          enqueueExpectedScheduleItems queue
              (groups0.foldl
                (fun queue group =>
                  enqueueExpectedSegment group.fst
                    { segment :=
                        { sources := sources
                          childSelectionSet := childSelectionSetForFields group.snd }
                      specFuels := specFuels }
                    queue)
                base0) =
            groups0.foldl
              (fun queue group =>
                enqueueExpectedSegment group.fst
                  { segment :=
                      { sources := sources
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
              { sources := sources
                childSelectionSet := childSelectionSetForFields group.snd }
            specFuels := specFuels }
        have hnextNonempty :
            expectedScheduleQueueItemsNonempty
              (enqueueExpectedSegment group.fst segment base0) :=
          enqueueExpectedSegment_itemsNonempty group.fst segment base0
            hbase0Nonempty
        have hnextDistinct :
            expectedScheduleQueueKeysDistinct
              (enqueueExpectedSegment group.fst segment base0) :=
          enqueueExpectedSegment_keysDistinct group.fst segment base0
            hbase0Distinct
        have htail :=
          ih (enqueueExpectedSegment group.fst segment base0)
            hnextNonempty hnextDistinct
        have hhead :=
          queue_enqueueExpectedScheduleItems_enqueueExpectedSegment
            (ObjectRef := ObjectRef) group.fst segment base0 queue
            hbase0Nonempty hbase0Distinct
        simpa [segment] using htail.trans (congrArg
          (fun q =>
            rest.foldl
              (fun queue group =>
                enqueueExpectedSegment group.fst
                  { segment :=
                      { sources := sources
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := specFuels }
                  queue)
              q)
          hhead)
  simpa [scheduleExpectedScope, groups, keyedGroups] using
    hfold keyedGroups base hbaseNonempty hbaseDistinct

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
      have hitemNonempty : queueItem.segments ≠ [] :=
        hqueue queueItem (by simp)
      have hrest :
          expectedScheduleQueueItemsNonempty rest := by
        intro restItem hrestItem
        exact hqueue restItem (by simp [hrestItem])
      have htail := ih hrest
      simp [expectedScheduleQueueCompletionStack, expectedQueueItemCompletion,
        completionStackFieldSegmentsNonempty]
      constructor
      · intro hsegments
        apply hitemNonempty
        cases hqueueSegments : queueItem.segments with
        | nil =>
            rfl
        | cons _head _tail =>
            simp [hqueueSegments] at hsegments
      · exact htail

theorem queue_pushExpectedFieldSegment_fieldSegmentsNonempty
    (key : ScheduleKey)
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
          by_cases hkey : scheduleKeyEqBool key fieldKey = true
          · simp [pushExpectedFieldSegmentInStore, hkey, fieldStoreSegmentsNonempty,
              hstore.2]
          · have hkeyFalse : scheduleKeyEqBool key fieldKey = false := by
              cases h : scheduleKeyEqBool key fieldKey with
              | false => rfl
              | true => exact False.elim (hkey h)
            have htail : fieldStoreSegmentsNonempty fieldStore := hstore.2
            simp [pushExpectedFieldSegmentInStore, hkeyFalse, fieldStoreSegmentsNonempty,
              hstore.1, ih htail]

theorem queue_popFieldResultByKey_pushExpectedFieldSegment_self
    (key : ScheduleKey)
    (segmentResults : List (Result ResponseValue))
    (stack : CompletionStack)
    : completionStackFieldSegmentsNonempty stack
      -> popFieldResultByKey key (pushExpectedFieldSegment key segmentResults stack)
          = (segmentResults, stack) := by
  cases stack with
  | mk valueStack fieldStore =>
      simp [completionStackFieldSegmentsNonempty, pushExpectedFieldSegment,
        popFieldResultByKey]
      intro hstore
      induction fieldStore with
      | nil =>
          simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore,
            popFieldResultFromSegments, scheduleKeyEqBool_self]
      | cons entry fieldStore ih =>
          rcases entry with ⟨fieldKey, fieldSegments⟩
          by_cases hkey : scheduleKeyEqBool key fieldKey = true
          · have hkeyEq : key = fieldKey := scheduleKeyEqBool_eq hkey
            subst fieldKey
            cases fieldSegments with
            | nil =>
                exact False.elim (hstore.1 rfl)
            | cons head tail =>
                simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore,
                  popFieldResultFromSegments, scheduleKeyEqBool_self]
          · have hkeyFalse : scheduleKeyEqBool key fieldKey = false := by
              cases h : scheduleKeyEqBool key fieldKey with
              | false => rfl
              | true => exact False.elim (hkey h)
            have htail : fieldStoreSegmentsNonempty fieldStore := hstore.2
            simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore, hkeyFalse,
              ih htail]

theorem queue_popFieldResultByKey_pushExpectedFieldSegment_commute
    (key pushedKey : ScheduleKey)
    (segmentResults : List (Result ResponseValue))
    (stack : CompletionStack)
    : scheduleKeyEqBool key pushedKey = false
      -> popFieldResultByKey key (pushExpectedFieldSegment pushedKey segmentResults stack)
          = let popped := popFieldResultByKey key stack
            (
              popped.fst,
              pushExpectedFieldSegment pushedKey segmentResults popped.snd
            ) := by
  cases stack with
  | mk valueStack fieldStore =>
      simp [pushExpectedFieldSegment, popFieldResultByKey]
      intro hneq
      induction fieldStore with
      | nil =>
          simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore, hneq]
      | cons entry fieldStore ih =>
          rcases entry with ⟨fieldKey, fieldSegments⟩
          by_cases hpushed : scheduleKeyEqBool pushedKey fieldKey = true
          · have hfieldEq : pushedKey = fieldKey := scheduleKeyEqBool_eq hpushed
            subst fieldKey
            have hkeyPushed : scheduleKeyEqBool key pushedKey = false := hneq
            simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore, hpushed,
              hkeyPushed]
          · have hpushedFalse : scheduleKeyEqBool pushedKey fieldKey = false := by
              cases h : scheduleKeyEqBool pushedKey fieldKey with
              | false => rfl
              | true => exact False.elim (hpushed h)
            by_cases hkeyField : scheduleKeyEqBool key fieldKey = true
            · cases hpop : popFieldResultFromSegments fieldSegments with
              | mk _popped remaining =>
                  cases remaining <;>
                    simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore,
                      hpushedFalse, hkeyField, hpop]
            · have hkeyFieldFalse : scheduleKeyEqBool key fieldKey = false := by
                cases h : scheduleKeyEqBool key fieldKey with
                | false => rfl
                | true => exact False.elim (hkeyField h)
              simp [pushExpectedFieldSegmentInStore, popFieldResultByKeyFromStore,
                hpushedFalse, hkeyFieldFalse, ih]

theorem queue_popFieldResultByKey_foldl_pushExpectedFieldSegments_commute
    (key : ScheduleKey)
    (entries : List (ScheduleKey × List (Result ResponseValue)))
    (stack : CompletionStack)
    : (∀ entry, entry ∈ entries -> key.responseName ≠ entry.fst.responseName)
      -> popFieldResultByKey key
            (entries.foldl
              (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
              stack)
          = let popped := popFieldResultByKey key stack
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
      have hheadNe : key.responseName ≠ entry.fst.responseName :=
        hneq entry (by simp)
      have hkeyFalse : scheduleKeyEqBool key entry.fst = false :=
        queue_scheduleKeyEqBool_false_of_responseName_ne hheadNe
      have htailNe :
          ∀ later, later ∈ entries -> key.responseName ≠ later.fst.responseName := by
        intro later hlater
        exact hneq later (by simp [hlater])
      rw [List.foldl_cons]
      rw [ih (pushExpectedFieldSegment entry.fst entry.snd stack) htailNe]
      simp [queue_popFieldResultByKey_pushExpectedFieldSegment_commute,
        hkeyFalse]

theorem queue_popFieldValuesByKeys_foldl_pushExpectedFieldSegments
    (entries : List (ScheduleKey × List (Result ResponseValue)))
    (stack : CompletionStack)
    : pairKeysNodup (entries.map (fun entry => (entry.fst.responseName, entry.snd)))
      -> completionStackFieldSegmentsNonempty stack
      -> popFieldValuesByKeys (entries.map Prod.fst)
            (entries.foldl
              (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
              stack)
          = (entries, stack) := by
  intro hnodup hstack
  induction entries generalizing stack with
  | nil =>
      simp [popFieldValuesByKeys]
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
        queue_popFieldResultByKey_foldl_pushExpectedFieldSegments_commute
          entry.fst entries
          (pushExpectedFieldSegment entry.fst entry.snd stack) hheadNe
      have htail :=
        ih stack hrestNodup hstack
      simp [popFieldValuesByKeys, List.foldl_cons]
      rw [hheadPop]
      rw [queue_popFieldResultByKey_pushExpectedFieldSegment_self
        entry.fst entry.snd stack hstack]
      constructor
      · constructor
        · rfl
        · exact congrArg Prod.fst htail
      · exact congrArg Prod.snd htail

theorem queue_expectedScheduleSegmentSpecFieldResults_scheduleKeyForFields_singleton
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType responseName : Name)
    (fields : List ExecutableField)
    (source : ResolverValue ObjectRef) (fuel : Nat)
    : fields ≠ []
      -> expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            (scheduleKeyForFields parentType responseName fields)
            {
              segment :=
                {
                  sources := [source]
                  childSelectionSet := childSelectionSetForFields fields
                }
              specFuels := [fuel]
            }
          = [singleFieldResultValue responseName
              (GraphQL.Execution.executeField schema resolvers variableValues fuel
                source responseName fields)] := by
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
          fuel source responseName field rest)

theorem queue_expectedScheduleScopeEntries_eq_spec
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups
      -> groups.map
            (fun group =>
              (
                scheduleKeyForFields parentType group.fst group.snd,
                expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                  (scheduleKeyForFields parentType group.fst group.snd)
                  {
                    segment :=
                      {
                        sources := [source]
                        childSelectionSet := childSelectionSetForFields group.snd
                      }
                    specFuels := [fuel]
                  }
              ))
          = groups.map
              (fun group =>
                (
                  scheduleKeyForFields parentType group.fst group.snd,
                  [singleFieldResultValue group.fst
                    (GraphQL.Execution.executeField schema resolvers variableValues
                      fuel source group.fst group.snd)]
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
    (groups : List (ScheduleKey × List ExecutableField))
    : nameFieldValueBlocks
        (groups.map
          (fun group =>
            (
              group.fst,
              [singleFieldResultValue group.fst.responseName
                (GraphQL.Execution.executeField schema resolvers variableValues
                  fuel source group.fst.responseName group.snd)]
            )))
      = groups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              fuel source group.fst.responseName group.snd]) := by
  induction groups with
  | nil =>
      rfl
  | cons group groups ih =>
      rcases group with ⟨key, fields⟩
      simp [nameFieldValueBlocks, nameFieldValues]
      constructor
      · exact queue_singleFieldResult_executeField_roundtrip
          (ObjectRef := ObjectRef) schema resolvers variableValues
          fuel source key.responseName fields
      · intro a b hmem
        exact queue_singleFieldResult_executeField_roundtrip
          (ObjectRef := ObjectRef) schema resolvers variableValues
          fuel source a.responseName b

theorem queue_keyedGroups_executeField_results_eq_groups
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : collectedGroupsNonempty groups
      -> (groups.map
            (fun group =>
              (scheduleKeyForFields parentType group.fst group.snd, group.snd))).map
            (fun group =>
              [GraphQL.Execution.executeField schema resolvers variableValues
                fuel source group.fst.responseName group.snd])
          = groups.map
              (fun group =>
                [GraphQL.Execution.executeField schema resolvers variableValues
                  fuel source group.fst group.snd]) := by
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
          simp [scheduleKeyForFields]
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
      ->  let keyedGroups :=
            groups.map
              (fun group =>
                (scheduleKeyForFields parentType group.fst group.snd, group.snd))
          let expectedEntries :=
            keyedGroups.map
              (fun group =>
                (
                  group.fst,
                  expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst
                    {
                      segment :=
                        {
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
                      fuel source group.fst.responseName group.snd)]
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
                  (scheduleKeyForFields parentType responseName (field :: rest))
                  { segment :=
                      { sources := [source]
                        childSelectionSet := childSelectionSetForFields (field :: rest) }
                    specFuels := [fuel] } =
                [singleFieldResultValue
                  (scheduleKeyForFields parentType responseName (field :: rest)).responseName
                  (GraphQL.Execution.executeField schema resolvers variableValues
                    fuel source
                    (scheduleKeyForFields parentType responseName (field :: rest)).responseName
                    (field :: rest))] := by
            simpa [scheduleKeyForFields] using
              queue_expectedScheduleSegmentSpecFieldResults_scheduleKeyForFields_singleton
                (ObjectRef := ObjectRef) schema resolvers variableValues
                parentType responseName (field :: rest) source fuel hfields
          simp only [List.map]
          simp [hhead, ih htail]

theorem queue_expectedEntries_pairKeysNodup
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fuel : Nat)
    (groups : List (Name × List ExecutableField))
    : pairKeysNodup groups
      ->  let keyedGroups :=
            groups.map
              (fun group =>
                (scheduleKeyForFields parentType group.fst group.snd, group.snd))
          let expectedEntries :=
            keyedGroups.map
              (fun group =>
                (
                  group.fst,
                  expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst
                    {
                      segment :=
                        {
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
                    group.fst
                    { segment :=
                        { sources := [source]
                          childSelectionSet := childSelectionSetForFields group.snd }
                      specFuels := [fuel] } )) ∘
                fun group =>
                  (scheduleKeyForFields parentType group.fst group.snd, group.snd))
          groups =
        groups.map Prod.fst := by
    induction groups with
    | nil =>
        rfl
    | cons group groups ih =>
        rcases group with ⟨responseName, fields⟩
        cases fields with
        | nil =>
            simp [Function.comp, scheduleKeyForFields]
            intro a b hmem
            cases b <;> rfl
        | cons head tail =>
            simp [Function.comp, scheduleKeyForFields]
            intro a b hmem
            cases b <;> rfl
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
            (scheduleKeyForFields work.work.runtimeType group.fst group.snd, group.snd))
      let specEntries :=
        keyedGroups.map
          (fun group =>
            (
              group.fst,
              [singleFieldResultValue group.fst.responseName
                (GraphQL.Execution.executeField schema resolvers variableValues
                  work.specFuel work.work.source group.fst.responseName group.snd)]
            ))
      combineScopeFieldResults 1 (nameFieldValueBlocks specEntries)
      = [expectedPendingChildWorkSpecResult schema resolvers variableValues work] := by
  let groups :=
    collectFieldsByKey schema variableValues
      work.work.runtimeType work.work.selectionSet
  let keyedGroups :=
    groups.map (fun group =>
      (scheduleKeyForFields work.work.runtimeType group.fst group.snd, group.snd))
  let specEntries :=
    keyedGroups.map
      (fun group =>
        ( group.fst
        , [singleFieldResultValue group.fst.responseName
            (GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel work.work.source group.fst.responseName group.snd)] ))
  have hnonempty :
      collectedGroupsNonempty groups := by
    simpa [groups] using
      collectFieldsByKey_collectedGroupsNonempty schema variableValues
        work.work.runtimeType work.work.selectionSet
  have hnamed :
      nameFieldValueBlocks specEntries =
        keyedGroups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel work.work.source group.fst.responseName group.snd]) := by
    simpa [specEntries, keyedGroups] using
      queue_nameFieldValueBlocks_specEntries
        (ObjectRef := ObjectRef) schema resolvers variableValues
        work.work.source work.specFuel keyedGroups
  have hraw :
      keyedGroups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel work.work.source group.fst.responseName group.snd]) =
        groups.map
          (fun group =>
            [GraphQL.Execution.executeField schema resolvers variableValues
              work.specFuel work.work.source group.fst group.snd]) := by
    dsimp [keyedGroups]
    exact
      queue_keyedGroups_executeField_results_eq_groups
        (ObjectRef := ObjectRef) schema resolvers variableValues
        work.work.runtimeType work.work.source work.specFuel groups hnonempty
  change combineScopeFieldResults 1 (nameFieldValueBlocks specEntries) =
    [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
  rw [hnamed, hraw]
  simpa [expectedPendingChildWorkSpecResult, groups] using
    (queue_expectedPendingChildWorkSpecResult_eq_scopeSingleton
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
          let keyedGroups :=
            groups.map
              (fun group =>
                (
                  scheduleKeyForFields work.work.runtimeType group.fst group.snd,
                  group.snd
                ))
          let expectedEntries :=
            keyedGroups.map
              (fun group =>
                (
                  group.fst,
                  expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst
                    {
                      segment :=
                        {
                          sources := [work.work.source]
                          childSelectionSet := childSelectionSetForFields group.snd
                        }
                      specFuels := [work.specFuel]
                    }
                ))
          completeScopeFrame [1] (keyedGroups.map Prod.fst)
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
  let keyedGroups :=
    groups.map (fun group =>
      (scheduleKeyForFields work.work.runtimeType group.fst group.snd, group.snd))
  let expectedEntries :=
    keyedGroups.map
      (fun group =>
        ( group.fst
        , expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            group.fst
            { segment :=
                { sources := [work.work.source]
                  childSelectionSet := childSelectionSetForFields group.snd }
              specFuels := [work.specFuel] } ))
  have hnodupGroups :
      pairKeysNodup groups := by
    simpa [groups] using
      collectFieldsByKey_pairKeysNodup schema variableValues
        work.work.runtimeType work.work.selectionSet
  have hnodupEntries :
      pairKeysNodup
        (expectedEntries.map (fun entry => (entry.fst.responseName, entry.snd))) := by
    simpa [groups, keyedGroups, expectedEntries] using
      queue_expectedEntries_pairKeysNodup
        (ObjectRef := ObjectRef) schema resolvers variableValues
        work.work.runtimeType work.work.source work.specFuel groups hnodupGroups
  have hpop :
      popFieldValuesByKeys (keyedGroups.map Prod.fst)
          (expectedEntries.foldl
            (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
            stack) =
        (expectedEntries, stack) := by
    simpa [expectedEntries, List.map_map, Function.comp_def] using
      queue_popFieldValuesByKeys_foldl_pushExpectedFieldSegments
        expectedEntries stack hnodupEntries hstack
  have hcombine :
      combineScopeFieldResults 1 (nameFieldValueBlocks expectedEntries) =
        [expectedPendingChildWorkSpecResult schema resolvers variableValues work] := by
    let specEntries :=
      keyedGroups.map
        (fun group =>
          ( group.fst
          , [singleFieldResultValue group.fst.responseName
              (GraphQL.Execution.executeField schema resolvers variableValues
                work.specFuel work.work.source group.fst.responseName group.snd)] ))
    have hentriesSpec : expectedEntries = specEntries := by
      have hnonempty :
          collectedGroupsNonempty groups := by
        simpa [groups] using
          collectFieldsByKey_collectedGroupsNonempty schema variableValues
            work.work.runtimeType work.work.selectionSet
      simpa [groups, keyedGroups, expectedEntries, specEntries] using
        queue_keyedGroups_expectedEntries_eq_spec
          (ObjectRef := ObjectRef) schema resolvers variableValues
          work.work.runtimeType work.work.source work.specFuel groups hnonempty
    rw [hentriesSpec]
    simpa [groups, keyedGroups, specEntries] using
      queue_combineScopeFieldResults_scheduleExpectedScope_singleton
        (ObjectRef := ObjectRef) schema resolvers variableValues work
  have hframe :=
    queue_completeScopeFrame_eq_of_pop
      [1] (keyedGroups.map Prod.fst)
      (expectedEntries.foldl
        (fun stack entry => pushExpectedFieldSegment entry.fst entry.snd stack)
        stack)
      stack expectedEntries (nameFieldValueBlocks expectedEntries)
      [expectedPendingChildWorkSpecResult schema resolvers variableValues work]
      hpop rfl hcombine
  simpa [groups, keyedGroups, expectedEntries, splitResultsByLengths] using hframe

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
  let keyedGroups :=
    groups.map (fun group =>
      (scheduleKeyForFields work.work.runtimeType group.fst group.snd, group.snd))
  let expectedEntries :=
    keyedGroups.map
      (fun group =>
        ( group.fst
        , expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
            group.fst
            { segment :=
                { sources := [work.work.source]
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
                  group.fst
                  { segment :=
                      { sources := [work.work.source]
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
      ∀ (groups0 : List (ScheduleKey × List ExecutableField))
        (stack0 : CompletionStack),
        (groups0.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst
                { segment :=
                    { sources := [work.work.source]
                      childSelectionSet := childSelectionSetForFields group.snd }
                  specFuels := [work.specFuel] })
              stack)
          stack0).fieldStore =
        (groups0.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst
                { segment :=
                    { sources := [work.work.source]
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
        simpa [pushExpectedFieldSegment] using
          ih
            { valueStack := stack0.valueStack
              fieldStore :=
                pushExpectedFieldSegmentInStore group.fst
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst
                    { segment :=
                        { sources := [work.work.source]
                          childSelectionSet := childSelectionSetForFields group.snd }
                      specFuels := [work.specFuel] })
                  stack0.fieldStore }
  have hkeyedStore :
      (expectedScheduleQueueCompletionStack schema resolvers variableValues
        (scheduleExpectedScope schema variableValues
          work.work.runtimeType [work.work.source] [work.specFuel]
          work.work.selectionSet queue).fst).fieldStore =
        (keyedGroups.foldl
          (fun stack group =>
            pushExpectedFieldSegment group.fst
              (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                group.fst
                { segment :=
                    { sources := [work.work.source]
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
                  group.fst
                  { segment :=
                      { sources := [work.work.source]
                        childSelectionSet := childSelectionSetForFields group.snd }
                    specFuels := [work.specFuel] })
                stack)
            (expectedScheduleQueueCompletionStack schema resolvers variableValues
              queue)).fieldStore := by
      simpa [scheduleExpectedScope, groups, keyedGroups] using
        congrArg CompletionState.fieldStore
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
        ∀ (groups0 : List (ScheduleKey × List ExecutableField))
          (stack0 : CompletionStack),
          groups0.foldl
              (fun stack group =>
                pushExpectedFieldSegment group.fst
                  (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                    group.fst
                    { segment :=
                        { sources := [work.work.source]
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
                        group.fst
                        { segment :=
                            { sources := [work.work.source]
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
          simpa [pushExpectedFieldSegment] using
            ih
              { valueStack := stack0.valueStack
                fieldStore :=
                  pushExpectedFieldSegmentInStore group.fst
                    (expectedScheduleSegmentSpecFieldResults schema resolvers variableValues
                      group.fst
                      { segment :=
                          { sources := [work.work.source]
                            childSelectionSet := childSelectionSetForFields group.snd }
                        specFuels := [work.specFuel] })
                    stack0.fieldStore }
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
                  group.fst
                  { segment :=
                      { sources := [work.work.source]
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
    simpa [baseStack, completionStackFieldSegmentsNonempty] using
      queue_expectedScheduleQueueCompletionStack_fieldSegmentsNonempty
        (ObjectRef := ObjectRef) schema resolvers variableValues queue hqueue
  rw [hstate]
  simpa [completeFrames, scheduleExpectedScope, groups, keyedGroups, expectedEntries, baseStack] using
    queue_completeScopeFrame_scheduleExpectedScope_singleton
      (ObjectRef := ObjectRef) schema resolvers variableValues work baseStack hbaseNonempty

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
  simpa [scheduleExpectedPendingChildWork] using
    queue_completeFrames_scheduleExpectedScope_singleton
      (ObjectRef := ObjectRef) schema resolvers variableValues work queue valueStack hqueue

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
        simpa [head] using
          scheduleExpectedScope_itemsNonempty
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
            expectedPendingChildWorkCompletion] using hheadFrame

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
        simpa [head] using
          scheduleExpectedScope_itemsNonempty
            (ObjectRef := ObjectRef) schema variableValues
            work.work.runtimeType [work.work.source] [work.specFuel]
            work.work.selectionSet base hbaseNonempty
      have hheadDistinct :
          expectedScheduleQueueKeysDistinct head.fst := by
        simpa [head] using
          scheduleExpectedScope_keysDistinct
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
  simpa [enqueueExpectedScheduleItems] using
    queue_enqueueExpectedScheduleItems_scheduleExpectedPendingChildWork
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
      using
      slots_expectedPendingChildWorkForItem_toPending_eq_buildFieldSlots
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
    simpa [runtimeScheduled, built, resolved, ExpectedQueueItem.toScheduleItem] using
      hframesDirect
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
    simpa [expectedScheduled] using
      queue_completeFrames_scheduleExpectedPendingChildWork
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
    simpa [expectedChildQueueForItem, hlookup, work] using
      queue_expectedScheduleQueueCompletionStack_scheduleExpectedPendingChildWork_enqueue_empty
        (ObjectRef := ObjectRef) schema resolvers variableValues work rest
  rw [hstack]
  simpa [work] using
    queue_completeFrames_executeScheduleItem_lookup_some_direct
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
