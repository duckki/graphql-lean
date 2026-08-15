import GraphQL.Algorithms.Common
import GraphQL.Execution
import GraphQL.Theories.NormalForm

/-!
Breadth-first GraphQL query execution algorithm. This module models the core scheduling
idea from `gmac/graphql-breadth-js`.

The spec executor is recursive: after resolving a composite field, it immediately
executes that field's child selection set. Breadth execution separates those steps.
It first resolves pending field batches from a forward queue, schedules any composite
children as later queue work, and records a trace that can rebuild response objects
after the children have completed.

The forward queue is keyed by `ScheduleKey`: parent type, response name, field name,
and arguments. Child selections are not part of the key; they stay on queue segments.
That means one queue item can contain the same field requested from many parent
objects, while still remembering each response position's child continuation.

The model keeps the spec executor's `Response` and `Result` domain. It changes only
the control flow:

* field work is batched when it has the same `ScheduleKey`;
* a batch resolver returns one result per source object;
* composite results create child-scope work in response order;
* compatible child field work can merge again later in the forward queue.

The JavaScript implementation also has planning hooks, async lazy loaders, mutation
root partitioning, and detailed error formatting. Those are outside the current
formalization scope.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

/-!
Name correspondence with `graphql-breadth-js`:

* `ResolverMap` models `src/executor/types.ts`'s `ResolverMap`, but with one
  batch resolver function in place of resolver objects.
* `collectFieldsByKey`, `parentTypeIsPossible`, and `buildExecutionField`
  mirror `ExecutionPlanner` helper names.
* `scheduleScope`, `executeScheduleItem`, `TraceFrame`, and `ValueSlot` mirror the
  `Executor` scheduling, execution, and result-building phases in a pure trace model.
  `drainLoop` models the fixed child-scope priority queue, without lazy queue
  resumption or abort/purge side effects.
-/

-----------------------------------------------------------------------------------------
-- Resolver Interface
-----------------------------------------------------------------------------------------

/-!
Invariant: `resolve` is the only host callback in the breadth model. The batch result
order is expected to match the source order; `executeScheduleItem` turns cardinality
mismatches into field errors.
-/

-- Breadth resolvers receive every source object in a concrete scope and are expected to
-- return one host-language result per source object. A cardinality mismatch is modeled
-- by `executeScheduleItem` as a field error for the current response position. `none` is
-- the same modeled resolver field error used by the spec-facing executor.
structure ResolverMap (ObjectRef : Type := PUnit) where
  resolve
    : Name -> Name -> List Argument -> List (ResolverValue ObjectRef)
      -> List (Option (ResolverValue ObjectRef))
  resolve_argumentsEquivalent
    : ∀ parentType fieldName firstArguments laterArguments sources,
        Argument.argumentsEquivalent firstArguments laterArguments
        -> resolve parentType fieldName firstArguments sources
            = resolve parentType fieldName laterArguments sources

-----------------------------------------------------------------------------------------
-- Shared Result Helpers
-----------------------------------------------------------------------------------------

/-!
Invariant: result helpers preserve list order and centralize error-count accumulation and
null bubbling. They do not inspect schema, resolver, or scheduling state.
-/

def combineListResults : List (Result ResponseValue) -> Result (List ResponseValue)
  | [] => .ok ([], 0)
  | result :: rest =>
      Result.combine List.cons result (combineListResults rest)

def listResultFromItems (itemResults : List (Result ResponseValue))
    : Result ResponseValue :=
  catchBubbleAsNull ResponseValue.list (combineListResults itemResults)

def objectResultFromFields (result : Result (List (Name × ResponseValue)))
    : Result ResponseValue :=
  match result with
  | .error errors => .error errors
  | .ok (fields, errors) => .ok (.object fields, errors)

def zipResultWith {α β γ : Type} (combine : α -> β -> γ)
    : List (Result α) -> List (Result β) -> List (Result γ)
  | [], [] => []
  | left :: lefts, right :: rights =>
      Result.combine combine left right :: zipResultWith combine lefts rights
  | [], _right :: _rights => []
  | _left :: _lefts, [] => []

-----------------------------------------------------------------------------------------
-- Scheduling Keys
-----------------------------------------------------------------------------------------

/-!
Invariant: `ScheduleKey` identifies one resolver-compatible field batch. Child selection
continuations are intentionally excluded and stay on `ScheduleSegment`s.
-/

structure ScheduleKey where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
deriving Repr

def scheduleKeyEqBool (left right : ScheduleKey) : Bool :=
  (left.parentType == right.parentType)
  && (left.responseName == right.responseName)
  && (left.fieldName == right.fieldName)
  && argumentListEqBool left.arguments right.arguments

def scheduleKeyForFields (parentType responseName : Name)
    : List ExecutableField -> ScheduleKey
  | [] =>
      {
        parentType := parentType
        responseName := responseName
        fieldName := ""
        arguments := []
      }
  | field :: _fields =>
      {
        parentType := field.parentType
        responseName := responseName
        fieldName := field.fieldName
        arguments := field.arguments
      }

def ScheduleKey.executableField (key : ScheduleKey) (selectionSet : List Selection)
    : ExecutableField :=
  {
    parentType := key.parentType
    responseName := key.responseName
    fieldName := key.fieldName
    arguments := key.arguments
    selectionSet := selectionSet
  }

-----------------------------------------------------------------------------------------
-- Forward Queue Model
-----------------------------------------------------------------------------------------

/-!
Invariant: every `ScheduleItem` contains only segments with its `ScheduleKey`. Segment
append order is the queue's deterministic tie-breaker, and `ScheduleItem.sources`
flattens segments in that same order for the batch resolver call.
-/

structure ScheduleSegment (ObjectRef : Type) where
  sources : List (ResolverValue ObjectRef)
  childSelectionSet : List Selection
deriving Repr

structure ScheduleItem (ObjectRef : Type) where
  key : ScheduleKey
  segments : List (ScheduleSegment ObjectRef)
deriving Repr

abbrev ScheduleQueue (ObjectRef : Type) :=
  List (ScheduleItem ObjectRef)

def ScheduleSegment.length (segment : ScheduleSegment ObjectRef) : Nat :=
  segment.sources.length

def ScheduleItem.segmentLengths (item : ScheduleItem ObjectRef) : List Nat :=
  item.segments.map ScheduleSegment.length

def ScheduleItem.sources (item : ScheduleItem ObjectRef)
    : List (ResolverValue ObjectRef) :=
  (item.segments.map ScheduleSegment.sources).flatten

def enqueueSegment (key : ScheduleKey) (segment : ScheduleSegment ObjectRef)
    : ScheduleQueue ObjectRef -> ScheduleQueue ObjectRef
  | [] =>
      [{
        key := key
        segments := [segment]
      }]
  | item :: rest =>
      if scheduleKeyEqBool key item.key then
        { item with segments := item.segments ++ [segment] } :: rest
      else
        item :: enqueueSegment key segment rest

def enqueueScheduleItems
    (queue : ScheduleQueue ObjectRef)
    (items : ScheduleQueue ObjectRef)
    : ScheduleQueue ObjectRef :=
  items.foldl
    (fun queue item =>
      item.segments.foldl
        (fun queue segment => enqueueSegment item.key segment queue)
        queue)
    queue

-----------------------------------------------------------------------------------------
-- Trace Model
-----------------------------------------------------------------------------------------

/-!
Invariant: trace frames are positional on the value side and keyed only on the field side.
`ScheduleKey` still routes completed field-value blocks into object scopes, but child
object values are consumed by the next `ValueSlot.child` in trace order. This keeps the
completion VM closer to a stack machine and avoids a second child-completion namespace.
-/

inductive ValueSlot where
  | completed (result : Result ResponseValue)
  | child
  | list (items : List ValueSlot)
deriving Repr

inductive TraceFrame where
  | scope (segmentLengths : List Nat) (fieldKeys : List ScheduleKey)
  | field
    (key : ScheduleKey)
    (fieldType : TypeRef)
    (segmentLengths : List Nat)
    (slots : List ValueSlot)
deriving Repr

abbrev ExecutionTrace := List TraceFrame

abbrev ScopeFrames := List TraceFrame

-----------------------------------------------------------------------------------------
-- Trace Generation
-----------------------------------------------------------------------------------------

/-!
Invariant: trace generation completes only the current field batch. Composite values
become child slots plus pending child work; their fields are scheduled later by the
queue, not recursively completed here.
-/

structure PendingChildWork (ObjectRef : Type) where
  runtimeType : Name
  selectionSet : List Selection
  source : ResolverValue ObjectRef
deriving Repr

abbrev PendingChildWorkList (ObjectRef : Type) :=
  List (PendingChildWork ObjectRef)

def mapAccumList {σ α β : Type} (step : σ -> α -> σ × β) : σ -> List α -> σ × List β
  | state, [] => (state, [])
  | state, value :: values =>
      let (state, mapped) := step state value
      let (state, mappedTail) := mapAccumList step state values
      (state, mapped :: mappedTail)

def buildValueSlot (schema : Schema) (selectionSet : List Selection)
    : TypeRef -> ResolverValue ObjectRef -> PendingChildWorkList ObjectRef
      -> PendingChildWorkList ObjectRef × ValueSlot
  | .nonNull inner, value, state =>
      buildValueSlot schema selectionSet inner value state
  | .list _inner, .null, state =>
      (state, .completed (.ok (.null, 0)))
  | .list inner, .list values, state =>
      let (work, slots) :=
        mapAccumList
          (fun state value => buildValueSlot schema selectionSet inner value state)
          state values
      (work, .list slots)
  | .list _inner, _value, state =>
      (state, .completed (.error 1))
  | .named _typeName, .null, state =>
      (state, .completed (.ok (.null, 0)))
  | .named typeName, .scalar value, state =>
      if (TypeRef.named typeName).isCompositeBool schema then
        (state, .completed (.error 1))
      else
        (state, .completed (.ok (.scalar value, 0)))
  | .named parentType, .object runtimeType ref, state =>
      if schema.typeIncludesObjectBool parentType runtimeType then
        let work :=
          {
            runtimeType := runtimeType
            selectionSet := selectionSet
            source := .object runtimeType ref
          }
        (state ++ [work], .child)
      else
        (state, .completed (.error 1))
  | .named _typeName, .list _values, state =>
      (state, .completed (.error 1))

def buildFieldSlotForResolved
    (schema : Schema) (fieldType : TypeRef) (selectionSet : List Selection)
    : PendingChildWorkList ObjectRef -> Option (ResolverValue ObjectRef)
      -> PendingChildWorkList ObjectRef × ValueSlot
  | state, none =>
      (state, .completed (handleFieldError fieldType))
  | state, some value =>
      buildValueSlot schema selectionSet fieldType value state

def buildFieldSlotsForResolved
    (schema : Schema) (fieldType : TypeRef) (selectionSet : List Selection)
    : List (Option (ResolverValue ObjectRef)) -> PendingChildWorkList ObjectRef
      -> PendingChildWorkList ObjectRef × List ValueSlot :=
  fun resolved state =>
    mapAccumList (buildFieldSlotForResolved schema fieldType selectionSet) state resolved

def splitResolvedBySegments
    : List (ScheduleSegment ObjectRef) -> List (Option (ResolverValue ObjectRef))
      -> List (ScheduleSegment ObjectRef × List (Option (ResolverValue ObjectRef)))
  | [], _resolved => []
  | segment :: segments, resolved =>
      let segmentResolved := resolved.take segment.sources.length
      let restResolved := resolved.drop segment.sources.length
      (segment, segmentResolved) :: splitResolvedBySegments segments restResolved

def buildFieldSlotsForResolvedSegments (schema : Schema) (fieldType : TypeRef)
    : List (ScheduleSegment ObjectRef × List (Option (ResolverValue ObjectRef)))
      -> PendingChildWorkList ObjectRef -> PendingChildWorkList ObjectRef × List ValueSlot
  | [], pending => (pending, [])
  | (segment, segmentResolved) :: rest, pending =>
      let (pending, slots) :=
        buildFieldSlotsForResolved schema fieldType
          segment.childSelectionSet segmentResolved pending
      let (tailPending, tailSlots) :=
        buildFieldSlotsForResolvedSegments schema fieldType rest pending
      (tailPending, slots ++ tailSlots)

def buildFieldSlotsLoop
    (schema : Schema) (fieldType : TypeRef)
    (segments : List (ScheduleSegment ObjectRef))
    (resolved : List (Option (ResolverValue ObjectRef)))
    (pending : PendingChildWorkList ObjectRef)
    : PendingChildWorkList ObjectRef × List ValueSlot :=
  buildFieldSlotsForResolvedSegments schema fieldType
    (splitResolvedBySegments segments resolved) pending

def buildFieldSlots
    (schema : Schema) (fieldType : TypeRef)
    (segments : List (ScheduleSegment ObjectRef))
    (resolved : List (Option (ResolverValue ObjectRef)))
    : PendingChildWorkList ObjectRef × List ValueSlot :=
  buildFieldSlotsLoop schema fieldType segments resolved []

-----------------------------------------------------------------------------------------
-- Execution
-----------------------------------------------------------------------------------------

/-!
Invariant: `scheduleScope` handles one concrete object scope and only enqueues field
groups. `executeScheduleItem` handles one queued field batch: resolve, build value slots,
and enqueue child work discovered from composite results.
-/

-- Spec 6.3.2 collected field entry constructor for concrete breadth scopes.
def buildExecutionField (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    : ExecutableField :=
  {
    parentType := parentType
    responseName := responseName
    fieldName := fieldName
    arguments := arguments
    selectionSet := selectionSet
  }

-- Spec 6.3.2 `DoesFragmentTypeApply` specialized to a concrete execution scope. Breadth
-- scopes are concrete object scopes, so inline fragment applicability is just membership
-- of the concrete parent object in the fragment condition's possible object set.
def parentTypeIsPossible (schema : Schema) (parentType typeCondition : Name) : Bool :=
  schema.typeIncludesObjectBool typeCondition parentType

-- Spec 6.3.2 `CollectFields`, specialized to concrete breadth execution scopes.
mutual
  def collectSelectionByKey (schema : Schema) (variableValues : VariableValues)
      : Name -> Selection -> List (Name × List ExecutableField)
    | parentType, .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [(
            responseName,
            [buildExecutionField parentType responseName fieldName arguments selectionSet]
          )]
        else
          []
    | parentType, .inlineFragment none directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          collectFieldsByKey schema variableValues parentType selectionSet
        else
          []
    | parentType, .inlineFragment (some typeCondition) directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          if parentTypeIsPossible schema parentType typeCondition then
            collectFieldsByKey schema variableValues parentType selectionSet
          else
            []
        else
          []

  def collectFieldsByKey (schema : Schema) (variableValues : VariableValues)
      : Name -> List Selection -> List (Name × List ExecutableField)
    | _parentType, [] => []
    | parentType, selection :: rest =>
        mergeExecutableGroups
          (collectSelectionByKey schema variableValues parentType selection)
          (collectFieldsByKey schema variableValues parentType rest)
end

def childSelectionSetForFields (fields : List ExecutableField) : List Selection :=
  (fields.map (fun field => field.selectionSet)).flatten

def scheduleScope
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (sources : List (ResolverValue ObjectRef))
    (selectionSet : List Selection) (queue : ScheduleQueue ObjectRef)
    : ScheduleQueue ObjectRef × TraceFrame :=
  let groups := collectFieldsByKey schema variableValues parentType selectionSet
  let keyedGroups :=
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
  (queue, .scope [sources.length] fieldKeys)

def schedulePendingChildWork (schema : Schema) (variableValues : VariableValues)
    : PendingChildWorkList ObjectRef -> ScheduleQueue ObjectRef
      -> ScheduleQueue ObjectRef × ScopeFrames
  | [], queue => (queue, [])
  | work :: rest, queue =>
      let (queue, frame) :=
        scheduleScope schema variableValues work.runtimeType
          [work.source] work.selectionSet queue
      let (queue, frames) := schedulePendingChildWork schema variableValues rest queue
      (queue, frame :: frames)

def executeScheduleItem
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues)
    (item : ScheduleItem ObjectRef)
    : ScheduleQueue ObjectRef × ExecutionTrace :=
  let sources := item.sources
  match schema.lookupField item.key.parentType item.key.fieldName with
  | none =>
      (
        [],
        [.field item.key (.named "") item.segmentLengths
          (List.replicate sources.length (.completed (.error 1)))]
      )
  | some fieldDefinition =>
      let resolved :=
        resolvers.resolve item.key.parentType item.key.fieldName item.key.arguments
          sources
      if !(resolved.length == sources.length) then
        (
          [],
          [.field item.key fieldDefinition.outputType item.segmentLengths
            (List.replicate sources.length
              (.completed (handleFieldError fieldDefinition.outputType)))]
        )
      else
        let (pendingChildWork, slots) :=
          buildFieldSlots schema fieldDefinition.outputType item.segments resolved
        let (queue, scopeFrames) :=
          schedulePendingChildWork schema variableValues pendingChildWork []
        (
          queue,
          .field item.key fieldDefinition.outputType item.segmentLengths slots
          :: scopeFrames
        )

-----------------------------------------------------------------------------------------
-- Out-Of-Fuel Trace Generation
-----------------------------------------------------------------------------------------

/-!
Invariant: fuel exhaustion does not discard queued work. It emits field frames filled with
`outOfFuel` slots so reverse completion still constructs a deterministic response.
-/

def outOfFuelScheduleTrace (schema : Schema) (item : ScheduleItem ObjectRef)
    : ExecutionTrace :=
  let fieldType :=
    match schema.lookupField item.key.parentType item.key.fieldName with
    | some fieldDefinition => fieldDefinition.outputType
    | none => .named ""
  [.field item.key fieldType item.segmentLengths
    (List.replicate item.sources.length (.completed outOfFuel))]

def outOfFuelQueueTrace (schema : Schema) : ScheduleQueue ObjectRef -> ExecutionTrace
  | [] => []
  | item :: rest =>
      outOfFuelScheduleTrace schema item ++ outOfFuelQueueTrace schema rest

-----------------------------------------------------------------------------------------
-- Main loop
-----------------------------------------------------------------------------------------

/-!
Invariant: the drain loop processes scheduled field batches in queue order. Newly
discovered child batches are merged back into the remaining queue by `ScheduleKey`, so
matching cousin fields can share a later resolver call.

* `ScheduleKey` is the forward scheduling key: concrete resolver parent type, response
  name, field name, and syntactic arguments.  The child selection set is deliberately
  stored on each segment, so cousins with the same resolver call but different
  continuations can still share one batch.
* `ScheduleItem` is one batched resolver call; `ScheduleSegment` records each
  parent-scope contribution to that batch.
* `PendingChildWork` is emitted by field completion for one resolved composite response
  position. Scheduling reads its runtime type and selection-set continuation, preserving
  the original slot order.
* `TraceFrame.scope` lists the field schedule keys an object scope will consume during
  reverse completion. Field completions are keyed by `ScheduleKey`; object completions
  are positional stack values consumed by `ValueSlot.child`.
-/

def drainLoop
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues)
    : Nat -> ScheduleQueue ObjectRef -> ExecutionTrace
  | _fuel, [] => []
  | 0, queue => outOfFuelQueueTrace schema queue
  | fuel + 1, item :: rest =>
      let (scheduled, trace) := executeScheduleItem schema resolvers variableValues item
      trace
      ++ drainLoop schema resolvers variableValues
          fuel (enqueueScheduleItems rest scheduled)

-----------------------------------------------------------------------------------------
-- Reverse Completion
-----------------------------------------------------------------------------------------

/-!
Invariant: reverse completion consumes trace frames from newest to oldest. Field frames
push field-value blocks keyed by `ScheduleKey`; scope frames pop those blocks and push
object results onto a positional value stack. Child value slots consume the next completed
object value in this stack-machine order.
-/

abbrev Segments (α : Type) := List (List α)

abbrev ResponseValueSegments := Segments (Result ResponseValue)

abbrev ObjectFieldSegments :=
  Segments (Result (List (Name × ResponseValue)))

abbrev ValueStack := ResponseValueSegments

abbrev FieldStore := List (ScheduleKey × ResponseValueSegments)

structure CompletionState where
  valueStack : ValueStack
  fieldStore : FieldStore
deriving Repr

abbrev CompletionStack := CompletionState

instance : EmptyCollection CompletionState where
  emptyCollection := { valueStack := [], fieldStore := [] }

def popHeadFromSegment {α : Type} (fallback : α) : List α -> α × List α
  | [] => (fallback, [])
  | value :: values => (value, values)

def popHeadFromSegments {α : Type} (fallback : α) : Segments α -> α × Segments α
  | [] => (fallback, [])
  | segment :: segments =>
      let (popped, segment') := popHeadFromSegment fallback segment
      (
        popped,
        match segment' with
        | [] => segments
        | segment' => segment' :: segments
      )

def popValueResultFromSegments
    : ResponseValueSegments -> Result ResponseValue × ResponseValueSegments :=
  popHeadFromSegments (.error 1)

def popValueResult : CompletionStack -> Result ResponseValue × CompletionStack
  | state =>
      let (popped, valueStack') := popValueResultFromSegments state.valueStack
      (popped, { state with valueStack := valueStack' })

def popFieldResultFromSegments
    : ResponseValueSegments -> List (Result ResponseValue) × ResponseValueSegments
  | [] => ([], [])
  | segment :: segments => (segment, segments)

def popFieldResultByKeyFromStore (key : ScheduleKey)
    : FieldStore -> List (Result ResponseValue) × FieldStore
  | [] => ([], [])
  | (itemKey, segments) :: store =>
      if scheduleKeyEqBool key itemKey then
        let (popped, segments') := popFieldResultFromSegments segments
        let store' :=
          match segments' with
          | [] => store
          | _ => (itemKey, segments') :: store
        (popped, store')
      else
        let (popped, store') := popFieldResultByKeyFromStore key store
        (popped, (itemKey, segments) :: store')

def popFieldResultByKey (key : ScheduleKey)
    : CompletionStack -> List (Result ResponseValue) × CompletionStack
  | state =>
      let popped := popFieldResultByKeyFromStore key state.fieldStore
      (popped.fst, { state with fieldStore := popped.snd })

def popFieldValuesByKeys
    : List ScheduleKey -> CompletionStack
      -> List (ScheduleKey × List (Result ResponseValue)) × CompletionStack
  | [], stack => ([], stack)
  | key :: keys, stack =>
      let head := popFieldResultByKey key stack
      let tail := popFieldValuesByKeys keys head.snd
      ((key, head.fst) :: tail.fst, tail.snd)

def nameFieldValues (key : ScheduleKey) (values : List (Result ResponseValue))
    : List (Result (List (Name × ResponseValue))) :=
  values.map (singleFieldResult key.responseName)

def nameFieldValueBlocks (blocks : List (ScheduleKey × List (Result ResponseValue)))
    : ObjectFieldSegments :=
  blocks.map (fun block => nameFieldValues block.fst block.snd)

mutual
  def completeSlot
      : TypeRef -> ValueSlot -> CompletionStack -> Result ResponseValue × CompletionStack
    | .nonNull inner, slot, stack =>
        let completed := completeSlot inner slot stack
        (nonNullCompletion completed.fst, completed.snd)
    | .list inner, .list items, stack =>
        let completed := completeSlotList inner items stack
        (listResultFromItems completed.fst, completed.snd)
    | .list _inner, .completed result, stack =>
        (result, stack)
    | .list _inner, _slot, stack =>
        (.error 1, stack)
    | .named _typeName, .child, stack =>
        let popped := popValueResult stack
        (catchBubbleAsNull id popped.fst, popped.snd)
    | .named _typeName, .completed result, stack =>
        (result, stack)
    | .named _typeName, .list _items, stack =>
        (.error 1, stack)

  def completeSlotList
      : TypeRef -> List ValueSlot -> CompletionStack
        -> List (Result ResponseValue) × CompletionStack
    | _inner, [], stack => ([], stack)
    | inner, slot :: slots, stack =>
        let head := completeSlot inner slot stack
        let tail := completeSlotList inner slots head.snd
        (head.fst :: tail.fst, tail.snd)
end

def splitResultsByLengths {α : Type} : List Nat -> List α -> Segments α
  | [], _results => []
  | length :: lengths, results =>
      results.take length :: splitResultsByLengths lengths (results.drop length)

-- A field frame completes the value slots for one resolver batch and pushes
-- segment-aligned values for later scope completion.
def completeFieldFrame
    (key : ScheduleKey) (fieldType : TypeRef)
    (segmentLengths : List Nat) (slots : List ValueSlot)
    (stack : CompletionStack)
    : CompletionStack :=
  let completed := completeSlotList fieldType slots stack
  let segments := splitResultsByLengths segmentLengths completed.fst
  { completed.snd with fieldStore := (key, segments.reverse) :: completed.snd.fieldStore }

def combineScopeFieldResults (sourceCount : Nat) (fieldResults : ObjectFieldSegments)
    : List (Result ResponseValue) :=
  let emptyFields : List (Result (List (Name × ResponseValue))) :=
    List.replicate sourceCount (.ok ([], 0))
  let combined :=
    fieldResults.foldr
      (fun fields tail =>
        zipResultWith (fun left right => left ++ right) fields tail)
      emptyFields
  combined.map
    (fun result =>
      match result with
      | .error errors => .error errors
      | .ok (fields, errors) => .ok (.object fields, errors))

-- A scope frame consumes field-value blocks in its collected field order and pushes the
-- completed object values expected by its parent value slots.
def completeScopeFrame
    (segmentLengths : List Nat) (fieldKeys : List ScheduleKey)
    (stack : CompletionStack)
    : CompletionStack :=
  let popped := popFieldValuesByKeys fieldKeys stack
  let fieldResults := nameFieldValueBlocks popped.fst
  let objectResults := combineScopeFieldResults segmentLengths.sum fieldResults
  let segments := splitResultsByLengths segmentLengths objectResults
  { popped.snd with valueStack := segments.reverse ++ popped.snd.valueStack }

def completeFrames : ExecutionTrace -> CompletionStack -> CompletionStack
  | [], stack => stack
  | .field key fieldType segmentLengths slots :: frames, stack =>
      completeFrames frames (completeFieldFrame key fieldType segmentLengths slots stack)
  | .scope segmentLengths fieldKeys :: frames, stack =>
      completeFrames frames (completeScopeFrame segmentLengths fieldKeys stack)

def completeExecutionTrace (trace : ExecutionTrace)
    : Result (List (Name × ResponseValue)) :=
  match completeFrames trace.reverse ∅ with
  | { valueStack := [[rootResult]], fieldStore := [] } =>
      match rootResult with
      | .error errors => .error errors
      | .ok (.object fields, errors) => .ok (fields, errors)
      | .ok (_value, errors) => .error (errors + 1)
  | _ => .error 1

-----------------------------------------------------------------------------------------
-- Public Query Entry Points
-----------------------------------------------------------------------------------------

/-!
Invariant: public query execution schedules the root object scope once, drains the breadth
queue with explicit fuel, and accepts only a single completed root object result.
-/

-- Spec 6.3.1 `ExecuteRootSelectionSet`, breadth scope version.
def executeRootSelectionSet
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Result (List (Name × ResponseValue)) :=
  let (queue, rootFrame) :=
    scheduleScope schema variableValues parentType [source] selectionSet []
  let trace := rootFrame :: drainLoop schema resolvers variableValues fuel queue
  completeExecutionTrace trace

-- Spec 6.2.1 `ExecuteQuery` / 7.1 response envelope at an explicit recursion fuel.
def executeQueryWithFuel
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : Response :=
  let coercedVariableValues :=
    GraphQL.Execution.coerceVariableValues operation variableValues
  if rootSourceAppliesBool schema operation source then
    let result :=
      executeRootSelectionSet schema resolvers coercedVariableValues
        fuel (operation.rootType schema) source operation.selectionSet
    match result with
    | .error errors => { data := .null, errors := errors }
    | .ok (fields, errors) => { data := .object fields, errors := errors }
  else
    { data := .null, errors := 1 }

def executeQuery
    (schema : Schema) (resolvers : ResolverMap ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  executeQueryWithFuel schema resolvers variableValues operation
    (executeQueryFuelBound operation) source

-----------------------------------------------------------------------------------------
-- Spec Resolver Adapter
-----------------------------------------------------------------------------------------

/-!
Invariant: the spec adapter preserves unary resolver behavior by mapping the spec
resolver across batch sources in order. It is the only resolver relation covered by the
public preservation statement.
-/

namespace ResolverMap

def fromSpecResolvers (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    : ResolverMap ObjectRef :=
  {
    resolve :=
      fun parentType fieldName arguments sources =>
        sources.map
          (fun source =>
            resolvers.resolve parentType fieldName arguments source)
    resolve_argumentsEquivalent := by
      intro parentType fieldName firstArguments laterArguments sources hargs
      induction sources with
      | nil => rfl
      | cons source rest ih =>
          have hhead :=
            resolvers.resolve_argumentsEquivalent
              parentType fieldName firstArguments laterArguments source hargs
          simp [hhead, ih]
  }

end ResolverMap

def executeQueryWithSpecResolvers
    (schema : Schema) (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (variableValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : Response :=
  executeQuery schema (ResolverMap.fromSpecResolvers resolvers)
    variableValues operation source

-----------------------------------------------------------------------------------------
-- Correctness theorem: breadthExecutionPreservesSpecExecution
-----------------------------------------------------------------------------------------

/-!
Invariant: the public proposition compares response envelopes at one shared preservation
fuel bound. It intentionally does not state all-fuel equality.
-/

-- Spec executor fuel bound used by the preservation statement. Each syntactic selection
-- step can spend one `executeField` tick plus the deepest schema output wrapper that
-- `completeValue` may recursively peel before reaching a child scope.
def typeRefCompleteValueFuelBound : TypeRef -> Nat
  | .named _typeName => 1
  | .list inner => typeRefCompleteValueFuelBound inner + 1
  | .nonNull inner => typeRefCompleteValueFuelBound inner

def fieldDefinitionsCompleteValueFuelBound (fields : List FieldDefinition) : Nat :=
  fields.foldl
    (fun bound fieldDefinition =>
      max bound (typeRefCompleteValueFuelBound fieldDefinition.outputType))
    0

def typeDefinitionCompleteValueFuelBound : TypeDefinition -> Nat
  | .object objectType =>
      fieldDefinitionsCompleteValueFuelBound objectType.fields
  | .interface interfaceType =>
      fieldDefinitionsCompleteValueFuelBound interfaceType.fields
  | _ => 0

def schemaCompleteValueFuelBound (schema : Schema) : Nat :=
  schema.types.foldl
    (fun bound typeDefinition =>
      max bound (typeDefinitionCompleteValueFuelBound typeDefinition))
    0

def specQueryFuelBound (schema : Schema) (operation : Operation) : Nat :=
  operation.size * (schemaCompleteValueFuelBound schema + 1)
  + schemaCompleteValueFuelBound schema
  + 1

-- Recursive scheduler weight used by the breadth preservation fuel bound. A field costs
-- one queue item at the current layer plus a conservative fanout allowance for scheduling
-- composite child work at the next layer. Inline fragments do not add a queue item by
-- themselves; they contribute only their child selection-set work.
mutual
  def selectionBreadthWeight (schema : Schema) : Selection -> Nat
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        1
        + (schema.objectTypes.length + 1) * selectionSetBreadthWeight schema selectionSet
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetBreadthWeight schema selectionSet

  def selectionSetBreadthWeight (schema : Schema) : List Selection -> Nat
    | [] => 0
    | selection :: rest =>
        selectionBreadthWeight schema selection + selectionSetBreadthWeight schema rest
end

-- Breadth executor fuel bound used by the preservation statement. Breadth fuel counts
-- processed queue items, so this intentionally uses a separate scheduler-oriented bound.
-- The first term preserves the broad operation-size frontier/drain bound used by the
-- queue invariant; the recursive weight accounts for nested composite child work where
-- every child layer can fan out across the schema's concrete object types before cousin
-- scopes merge in the queue.
def breadthQueryFuelBound (schema : Schema) (operation : Operation) : Nat :=
  operation.size * (schema.objectTypes.length + 1) * (schema.objectTypes.length + 1)
  + selectionSetBreadthWeight schema operation.selectionSet
    * (schema.objectTypes.length + 1)
  + 1

-- Fuel bound for comparing both executors at the same explicit fuel.
def preservationFuelBound (schema : Schema) (operation : Operation) : Nat :=
  max (specQueryFuelBound schema operation) (breadthQueryFuelBound schema operation)

-- Correctness statement for breadth execution at the shared preservation fuel bound.
-- The all-fuel version is intentionally not used to avoid fuel bounds compatibility
-- proofs across the two execution models: breadth fuel counts scheduler queue steps,
-- while the spec executor fuel counts recursive value-completion depth.
-- Proof witness: `breadthExecutionPreservesSpecExecution_proof` in
-- `Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Final`.
def breadthExecutionPreservesSpecExecution (schema : Schema) (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ {ObjectRef : Type} (resolvers : GraphQL.Execution.Resolvers ObjectRef)
        variableValues (source : ResolverValue ObjectRef),
      NormalForm.operationBoolVarsComplete operation
        (GraphQL.Execution.coerceVariableValues operation variableValues)
      -> executeQueryWithFuel schema (ResolverMap.fromSpecResolvers resolvers)
            variableValues operation (preservationFuelBound schema operation) source
          = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
              operation (preservationFuelBound schema operation) source

end ExecutionBreadth

end Algorithms

end GraphQL
