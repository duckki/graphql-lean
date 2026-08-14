# Breadth Execution As A Runtime

This note explains `GraphQL.Algorithms.ExecutionBreadth` for software engineers
who need to understand the algorithm or port it to another language. It uses a
programming-language analogy:

- the forward queue is the scheduler,
- the trace is an instruction stream,
- `ValueSlot`s are deferred value operands, and
- reverse completion is a small stack machine that executes the trace.

The Lean model is pure and deterministic. It intentionally avoids the mutable
object references used by `gmac/graphql-breadth-js`; instead, it records enough
trace information to rebuild the same response after the breadth-first pass has
finished.

## Mental Model

Spec GraphQL execution is recursive:

1. collect fields for one object,
2. resolve a field,
3. complete the resolved value,
4. recursively execute child selections for object values.

Breadth execution splits that into two phases:

1. A forward pass resolves scheduled field batches in breadth-first order and
   emits a trace.
2. A reverse pass completes the trace from newest frame to oldest frame and
   builds response values.

The split is the key idea. During the forward pass, an object result is not
completed immediately. Instead, the algorithm emits a `ValueSlot.child` that
says: "the value for this field will be the completed object for this child
scope." The child scope is scheduled for later. When the reverse pass runs, that
child scope has already been completed and can be popped from the completion
stack.

This also means sibling cancellation is not naturally an executor-level feature
of this model. Sibling field work may already be part of one vectorized resolver
call, possibly mixed with positions from other parent scopes. A resolver or
runtime scheduler could choose a cancellation policy, but the pure breadth model
records and completes the scheduled work after it has run.

## Runtime Data Structures

### `ScheduleKey`

`ScheduleKey` is the forward queue key:

```lean
structure ScheduleKey where
  parentType : Name
  responseName : Name
  fieldName : Name
  arguments : List Argument
```

It identifies one resolver-compatible field batch. The child selection set is
not part of the key. That is deliberate: two cousin fields with the same
resolver call can share a batch even when their child continuations differ.

The key retains executable argument syntax for collection and scheduling. It is
not the resolver argument value: `executeScheduleItem` coerces it against the
looked-up field definition immediately before invoking the batch resolver.

In an implementation language like Rust, this is the natural hash or equality
key for queue coalescing.

### `ScheduleSegment`

`ScheduleSegment` is one contribution to a scheduled field batch:

```lean
structure ScheduleSegment where
  sources : List (ResolverValue ObjectRef)
  childSelectionSet : List Selection
```

Segments preserve the decomposition of the batch. A `ScheduleItem` flattens all
segment sources before calling the resolver, but `segmentLengths` later split the
flat result list back into segment-aligned groups.

### `ScheduleItem`

`ScheduleItem` is one queued resolver call:

```lean
structure ScheduleItem where
  key : ScheduleKey
  segments : List ScheduleSegment
```

`item.sources` is `item.segments.flatMap(_.sources)`. The resolver is called
once with that flattened source list and must return one result per source.
Cardinality mismatch is modeled as field errors for the current batch.

### `PendingChildWork`

`PendingChildWork` is one concrete object continuation discovered while
building value slots:

```lean
structure PendingChildWork where
  runtimeType : Name
  selectionSet : List Selection
  source : ResolverValue ObjectRef
```

It is deliberately not keyed or grouped. Each pending scope corresponds to one
response position and is kept in the same order as the `ValueSlot.child` that
will later consume it.

The forward queue still performs batching. When pending child work items are
scheduled, their child fields are merged into `ScheduleItem`s by `ScheduleKey`.
This gives the model two separate responsibilities:

- pending child work preserves positional completion order,
- scheduled field work coalesces resolver calls.

### `ValueSlot`

`ValueSlot` is a value operand in the trace:

```lean
inductive ValueSlot where
  | completed (result : Result ResponseValue)
  | child
  | list (items : List ValueSlot)
```

Interpretation:

- `completed result`: the value is already known.
- `child`: pop the next completed child object value from the completion stack.
- `list items`: complete each item slot and wrap the results as a list.

This is the main replacement for JavaScript object-reference mutation. Instead
of storing a pointer and filling it later, the model stores a slot that will know
where to find the child result during reverse completion.

### `TraceFrame`

The trace has two instruction forms:

```lean
inductive TraceFrame where
  | scope
      (segmentLengths : List Nat)
      (fieldKeys : List ScheduleKey)
  | field
      (key : ScheduleKey)
      (fieldType : TypeRef)
      (segmentLengths : List Nat)
      (slots : List ValueSlot)
```

Think of these as bytecode instructions:

- `field`: complete field value slots and push field-value blocks.
- `scope`: pop field-value blocks, name them, combine them into object values, and push
  object-result blocks.

The forward pass emits frames in execution order. The VM executes them in
reverse order.

## Forward Pass

### Compiling A Scope

`scheduleScope` handles one concrete object scope. It does not resolve fields.
It only collects fields and appends scheduled field work to the queue.

Pseudocode:

```text
scheduleScope(parentType, sources, selectionSet, queue):
  groups = collectFieldsByKey(parentType, selectionSet)
  fieldKeys = []

  for (responseName, fields) in groups:
    key = scheduleKeyForFields(parentType, responseName, fields)
    segment = {
      sources,
      childSelectionSet = childSelectionSetForFields(fields)
    }
    queue = enqueueSegment(key, segment, queue)
    fieldKeys.push(key)

  frame = TraceFrame.scope([sources.length], fieldKeys)
  return (queue, frame)
```

This is analogous to compiling one object scope into a scope instruction plus
future field instructions.

The scope frame does not store `sources` themselves. It stores
`segmentLengths`. In the current model, `scheduleScope` is called with one source
list, so the scope frame uses `[sources.length]`. The length says how many object
results this scope frame must produce and how to package them back into stack
segments.

The source list may contain the same runtime object reference more than once. For
example, a resolver may return the same object ref in two list positions. The
completion runtime treats those as two response positions, not one shared object.
That is why the frame records positions by count instead of by object identity.

### Executing A Queue Item

`executeScheduleItem` handles one scheduled resolver batch.

Pseudocode:

```text
executeScheduleItem(item):
  sources = flatten(item.segments.sources)
  fieldDefinition = schema.lookupField(item.key.parentType, item.key.fieldName)

  if fieldDefinition is missing:
    slots = one error slot per source
    frame = TraceFrame.field(item.key, Named(""), item.segmentLengths, slots)
    return ([], [frame])

  arguments = coerceArgumentValues(schema,
                                   variableValues,
                                   fieldDefinition.arguments,
                                   item.key.arguments)
  resolved = resolver.resolve(item.key.parentType,
                              item.key.fieldName,
                              arguments,
                              sources)

  if resolved.length != sources.length:
    slots = one field-error slot per source
    frame = TraceFrame.field(item.key, fieldDefinition.outputType,
                             item.segmentLengths, slots)
    return ([], [frame])

  (pendingChildWork, slots) =
    buildFieldSlots(item.segments, resolved)

  (childQueue, childScopeFrames) =
    schedulePendingChildWork(pendingChildWork)

  frame = TraceFrame.field(item.key, fieldDefinition.outputType,
                           item.segmentLengths, slots)

  return (childQueue, [frame] ++ childScopeFrames)
```

There are three products here:

- `slots`: a flat list with one `ValueSlot` per source in
  `flatten(item.segments.sources)`;
- a `TraceFrame.field`: the instruction that will later complete those slots;
- `pendingChildWork`: the child object work discovered while building the
  slots.

The field frame is deliberately small:

```text
TraceFrame.field(
  key = item.key,
  fieldType = fieldDefinition.outputType,
  segmentLengths = item.segmentLengths,
  slots = slots
)
```

It does not contain resolved values directly. Resolved values have already been
compiled into `ValueSlot`s. The frame keeps only the information the reverse VM
needs to turn those slots into field results:

- `key.responseName` says which response property to produce;
- `fieldType` says how to apply list and non-null completion;
- `segmentLengths` says how to split the flat completed values back into the
  original schedule segments;
- `slots` says where each completed value comes from.

This is the bytecode analogy: `executeScheduleItem` resolves host values, but it
does not finish the response. Instead, it emits a field instruction whose
operands are the slots.

`buildFieldSlots` is where resolved values become `ValueSlot`s:

- scalar and null values become `ValueSlot.completed`,
- invalid runtime shapes become `ValueSlot.completed (.error 1)`,
- list values become `ValueSlot.list`,
- object values become `ValueSlot.child` and add a `PendingChildWork`.

The important alignment invariant is:

```text
resolved[i] corresponds to slots[i]
```

where `resolved` is the flat resolver output for `item.sources`. Segment
boundaries are not lost, because the field frame keeps `item.segmentLengths`.
For example:

```text
segments:
  A.sources = [a1, a2]
  B.sources = [b1]

flattened resolver input:
  [a1, a2, b1]

resolver output:
  [ra1, ra2, rb1]

slots:
  [slot(ra1), slot(ra2), slot(rb1)]

segmentLengths:
  [2, 1]
```

During reverse completion, the field frame first completes all three slots, then
splits the three field results into `[[result(a1), result(a2)], [result(b1)]]`.
That split is how the VM routes results back to the scopes that contributed the
segments.

Pending child work items are an ordered list. They are not grouped before
scheduling. This is the main simplification in the current model: the trace uses
fixed scheduling order to match parent child slots with completed child objects.

For an object result, `buildValueSlot` does two things at the same time:

```text
work = {
  runtimeType = resolved.runtimeType,
  selectionSet = segment.childSelectionSet,
  source = resolvedObject
}

slot = ValueSlot.child
pendingChildWork.append(work)
```

The slot remains in the parent field frame. The pending child work is scheduled
as future work. Later, reverse completion uses stack order to pop the completed
object value produced by that child scope.

This also explains why duplicate source objects are not a special case. If two
positions resolve to the same object ref, the pending child list contains two
work items:

```text
pendingChildWork = [
  { source = object(ref=7), ... },
  { source = object(ref=7), ... }
]
```

Those are two response positions. They may still have their child fields
coalesced into one queued resolver batch, but completion keeps two scope frames.
The two parent `ValueSlot.child` slots consume the two completed object values
in source order. No object identity deduplication is implied.

The invariant is:

```text
childSlotsInTrace == pendingChildWork in the same left-to-right order
```

This includes child slots nested inside list slots. A list of two object values
emits a `ValueSlot.list [child, child]` and two pending child work items in the same
order.

### Draining The Queue

`drainLoop` repeatedly executes the head queue item:

```text
drainLoop(fuel, queue):
  if queue is empty:
    return []

  if fuel == 0:
    return outOfFuelQueueTrace(queue)

  item = queue.pop_front()
  (childQueue, trace) = executeScheduleItem(item)
  queue = enqueueScheduleItems(queue, childQueue)

  return trace ++ drainLoop(fuel - 1, queue)
```

The queue merge is still keyed only by `ScheduleKey`. New child work can merge
with remaining cousin work that has the same resolver-compatible key.

## Reverse Completion VM

The trace is completed by:

```lean
completeFrames trace.reverse ∅
```

This is why the model can be read as a VM. The forward pass emits an instruction
stream; the reverse pass evaluates it with a stack.

### Completion State

The reverse VM state is:

```text
CompletionState {
  valueStack : List (List (Result ResponseValue))
  fieldStore : List (ScheduleKey × List (List (Result ResponseValue))))
}
```

`valueStack` contains completed child object values. It is purely positional.
`ValueSlot.child` always consumes the next value from the head of this stack.

`fieldStore` contains completed field-value blocks keyed by `ScheduleKey`.
`TraceFrame.scope` consumes these blocks by key. The response name is not stored
in every value; it is recovered from the `ScheduleKey` when a scope frame pops
the field block.

Both components store `segments : List (List result)`. The outer list
represents segment groups. The inner lists preserve source order within a
segment. The reverse pass uses destructive-pop behavior functionally:

- `popValueResult` pops from `valueStack`,
- `popFieldResultByKey` pops from the matching `fieldStore` entry,
- everything else in the state is preserved.

### Executing A Field Frame

`completeFieldFrame key fieldType segmentLengths slots stack`:

1. Run `completeSlotList fieldType slots stack`.
2. Split the flat completed-value list by `segmentLengths`.
3. Push a keyed field block into `fieldStore`.

Conceptually:

```text
field frame:
  completedValues = complete slots, possibly popping child values
  segments = splitBy(segmentLengths, completedValues).reverse
  state.fieldStore = (key, segments) :: state.fieldStore
```

The reverse of `segments` is important because frames are executed from newest
to oldest while stack popping consumes from the front.

### Executing A Scope Frame

`completeScopeFrame segmentLengths fieldKeys stack`:

1. Pop field-value segments for each collected field key.
2. Wrap each value with its field key's response name.
3. Combine field results in collected-field order.
4. Split the flat object-result list by `segmentLengths`.
5. Push positional object values into `valueStack`.

Conceptually:

```text
scope frame:
  fieldBlocks = fieldKeys.map(key =>
    pop fields by ScheduleKey and map(singleFieldResult(key.responseName)))
  objectResults = combineScopeFieldResults(sourceCount, fieldBlocks)
  segments = splitBy(segmentLengths, objectResults).reverse
  push values(segments)
```

This is where an object scope becomes a response object value.

### Completing A Slot

`completeSlot` is the expression evaluator for `ValueSlot`:

```text
completed result:
  return result

child:
  result = pop next values entry
  return catchBubbleAsNull(result)

list items:
  itemResults = complete each item slot
  return listResultFromItems(itemResults)

nonNull type wrapper:
  complete inner slot
  apply nonNullCompletion
```

The stack effect matters. A child slot consumes one value from the next
positional value entry. This is how parent field completion receives the child
object that was scheduled and completed later in the forward pass.

## Why Reverse Order Works

Use a query with sibling composite fields:

```graphql
query {
  me {
    bestFriend {
      name
    }
    friends {
      name
    }
  }
}
```

Assume `me`, `bestFriend`, and each element of `friends` all have concrete
runtime type `User`, and assume `friends` returns two users.

The forward trace shape is roughly:

```text
scope(root)
field(Query.me)                  -- one ValueSlot.child
scope(User me)                   -- fields: bestFriend, friends
field(User.bestFriend)           -- one ValueSlot.child
scope(User bestFriend)           -- field: name
field(User.friends)              -- ValueSlot.list [child, child]
scope(User friend[0])            -- field: name
scope(User friend[1])            -- field: name
field(User.name)                 -- scalar slots, segments [bestFriend, friend[0], friend[1]]
```

The VM executes the reverse. The state shown below is top-first. Field frames
push their segment lists reversed into `fieldStore`, so the newest scope frame
can consume the first segment at the head of the stored block.

```text
start
  valueStack = []
  fieldStore = []

field(User.name)
  push fieldStore entry (User.name, [
    [name(friend[1])],
    [name(friend[0])],
    [name(bestFriend)]
  ])

  valueStack = []
  fieldStore = [
    (User.name, [[name(friend[1])], [name(friend[0])], [name(bestFriend)]])
  ]

scope(User friend[1])
  pop fields by key User.name, taking the first segment [name(friend[1])]
  prepend [[object(friend[1])]] to valueStack

  valueStack = [[object(friend[1])]]
  fieldStore = [
    (User.name, [[name(friend[0])], [name(bestFriend)]])
  ]

scope(User friend[0])
  pop fields by key User.name, taking the first remaining segment [name(friend[0])]
  prepend [[object(friend[0])]] to valueStack

  valueStack = [[object(friend[0])], [object(friend[1])]]
  fieldStore = [
    (User.name, [[name(bestFriend)]])
  ]

field(User.friends)
  complete ValueSlot.list [child, child]
  child pop #1 takes `object(friend[0])` from the first segment in valueStack
  child pop #2 takes `object(friend[1])` from the next segment in valueStack
  push fieldStore entry
    (User.friends, [[friends([object(friend[0]), object(friend[1])])]])

  valueStack = []
  fieldStore = [
    (User.friends, [[friends([object(friend[0]), object(friend[1])])]]),
    (User.name, [[name(bestFriend)]])
  ]

scope(User bestFriend)
  pop fields by key User.name, taking [name(bestFriend)]
  prepend [[object(bestFriend)]] to valueStack

  valueStack = [[object(bestFriend)]]
  fieldStore = [
    (User.friends, [[friends([object(friend[0]), object(friend[1])])]])
  ]

field(User.bestFriend)
  child pop takes `object(bestFriend)` from the first valueStack segment
  push fieldStore entry (User.bestFriend, [[bestFriend(object(bestFriend))]])

  valueStack = []
  fieldStore = [
    (User.bestFriend, [[bestFriend(object(bestFriend))]]),
    (User.friends, [[friends([object(friend[0]), object(friend[1])])]])
  ]

scope(User me)
  pop fields by key User.bestFriend, taking [bestFriend(object(bestFriend))]
  pop fields by key User.friends, taking [friends([object(friend[0]), object(friend[1])])]
  prepend [[object(me)]] to valueStack

  valueStack = [[object(me)]]
  fieldStore = []

field(Query.me)
  child pop takes `object(me)` from the first valueStack segment
  push fieldStore entry (Query.me, [[me(object(me))]])

  valueStack = []
  fieldStore = [
    (Query.me, [[me(object(me))]])
  ]

scope(root)
  pop fields by key Query.me, taking [me(object(me))]
  prepend [[object(root)]] to valueStack

  valueStack = [[object(root)]]
  fieldStore = []
```

The scalar `name` values are not the interesting part: they are already
`ValueSlot.completed` operands in the `User.name` field frame. The important
part is that sibling composite fields can schedule their `User.name` work
together, while reverse completion still rebuilds child objects in the exact
order that parent `ValueSlot.child` operands will consume them.

There are two different pop modes:

- `ValueSlot.child` uses positional popping. It scans from the top for the next
  `valueStack` segment, takes the first value from the first segment, and drops
  the segment when no values remain.
- `TraceFrame.scope` uses keyed popping. For each collected `ScheduleKey`, it
  scans `fieldStore` for a matching `(key, segments)` entry, takes the first
  segment, and leaves any remaining segments under the same key.

That keyed field pop is not how a conventional bytecode VM would usually address
its stack; a normal VM would more likely use offsets or a fixed frame layout.
The keyed form is intentional in this model because it keeps field routing
explicit and proof-friendly while the forward queue coalesces work by
`ScheduleKey`.

This is the same dependency order a recursive executor would follow, but it is
derived from a breadth-first trace rather than recursive calls.

## Segment Lengths

`segmentLengths` are the runtime shape metadata that make batching reversible.

They are used in two places:

- A field frame splits a flat resolver result list back into the original
  schedule segments.
- A scope frame splits a flat object-result list back into the original parent
  scope segments.

Without segment lengths, a batched resolver call could produce correct values
but the VM would not know how to route them back to parent scopes.

## End-To-End Root Execution

`executeRootSelectionSet` does four things:

```text
(queue, rootFrame) = scheduleScope(rootType, [source], selectionSet, [])
trace = [rootFrame] ++ drainLoop(fuel, queue)
state = completeFrames(reverse(trace), emptyState)
extract exactly one root object result from state
```

The final state is expected to be exactly:

```text
CompletionState {
  valueStack = [[rootObjectResult]]
  fieldStore = []
}
```

Anything else is treated as an execution error in this proof-facing model.

## Porting Notes

For a Rust implementation, the direct translation is:

- `ScheduleKey` as a hashable struct for forward field batching.
- `PendingChildWork` as an ordered work item, not a hash key.
- `ScheduleQueue` as a `VecDeque<ScheduleItem>` or `Vec<ScheduleItem>` with
  stable append and linear coalescing, depending on expected queue sizes.
- `TraceFrame` and `ValueSlot` as enums.
- `CompletionState` as a struct with `valueStack` and `fieldStore`.
- `segmentLengths` as `Vec<usize>`.
- `ResolverMap.resolve` as a batch function returning `Vec<Option<Value>>`.

Important implementation details:

- Preserve source order within every segment.
- Preserve segment order within every schedule item.
- Store child selection sets on segments, not on `ScheduleKey`.
- Preserve pending child work order exactly; do not pre-group pending child work
  before emitting scope frames.
- Let the forward queue regroup the field work by `ScheduleKey`.
- Treat resolver cardinality mismatch as a field-level error for every source in
  the batch.
- Complete the trace in reverse order.
- Pop value completions positionally and update the residual segment lists
  predictably.

The model uses linear lookup on lists because it is proof-friendly. A real
implementation can use maps for keyed field lookup, but it must preserve the
same observable ordering rules:

- queue order determines resolver-call order,
- segment order determines result routing,
- collected field order determines object field order,
- child slot order determines positional value consumption order.

## Relationship To JavaScript Object References

The JavaScript implementation can keep object references and fill objects as
children complete. The Lean model avoids that because mutable aliasing is hard
to reason about. The trace/VM design is the pure replacement:

- a `ValueSlot.child` is a promise to read the next future child object result,
- a `TraceFrame.scope` is the instruction that creates that child object result,
- the completion stack is the store where completed child objects live until a
  parent slot consumes them.

This is why the trace can feel like bytecode. It is bytecode for a small
completion VM whose only job is to rebuild the response envelope after the
breadth-first resolver scheduler has finished.

## Debugging Checklist

When the result shape is wrong, check these in order:

1. Did `scheduleScope` collect the expected field groups?
2. Did `enqueueSegment` merge only matching `ScheduleKey`s?
3. Did each `ScheduleSegment` carry the correct `childSelectionSet`?
4. Did `executeScheduleItem` preserve resolver result cardinality?
5. Did `buildValueSlot` emit `ValueSlot.child` only for valid composite object
   values?
6. Did `schedulePendingChildWork` preserve pending child work order?
7. Did field frames use the same `segmentLengths` as the source segments?
8. Did scope frames pop field keys in collected-field order?
9. Did reverse completion run on `trace.reverse`, not the forward trace?

Most bugs in ports are routing bugs: a value is resolved correctly but routed to
the wrong segment, field key, or child position. The trace model is designed to
make those routing decisions explicit.
