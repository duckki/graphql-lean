# Algorithm Proof Status

This document records project execution algorithms and their current proof
status against the spec-facing execution model. These algorithms are not
additional GraphQL specification features; they are implementation strategies
with public correctness statements where stated.

## Sibling-Canceling Spec Execution

`GraphQL.Algorithms.ExecutionCancelingSiblings` uses the spec executor's field
collection, grouping, resolver calls, and value completion. When a collected
field result bubbles through the active selection set, it returns immediately
instead of executing the remaining sibling response positions. Nested nullable
completion catches that bubble as `null` in the same way as `GraphQL.Execution`.

The public statement
`GraphQL.Algorithms.ExecutionCancelingSiblings.siblingCancelingExecutionPreservesSpecExecution`
is resolver-parametric and applies to every schema, operation, variable
assignment, explicit fuel value, and source value. It says the canceling and
spec-facing responses have equal data and agree on whether any execution error
is present. Exact error counts may differ because the spec-facing executor
continues through siblings that the canceling executor skips.

Its proof witness is
`GraphQL.Algorithms.ExecutionCancelingSiblings.siblingCancelingExecutionPreservesSpecExecution_proof`
in
`Proofs/GraphQL/Algorithms/ExecutionCancelingSiblings/Semantics.lean`.

## Ungrouped Execution

`GraphQL.Algorithms.ExecutionUngrouped` is a syntax-order query execution
algorithm for the same scoped fragment as `GraphQL.Execution`. The spec-facing
executor collects fields by response name before executing each response
position. Ungrouped execution visits selections directly and merges response
slices as it walks the selection list.

The algorithm is aimed at synchronous execution. It can be lighter in CPU and
memory usage because it avoids constructing the full collected-fields map, keeps
only field-level state for response positions, and stops walking sibling
selections when null bubbling determines the enclosing result.

The internal state is a `FieldCacheValue`. A first visit to a response position
calls the resolver and completes the value into that state. A later compatible
visit to the same response position consults the field state, not the public
output response. Final nulls, scalars, and lists of leaf values are returned
directly. Composite objects and lists store the raw resolver source, so later
compatible subselections can descend with that source instead of invoking the
parent field resolver again. Public response data is produced by the `output`
projection, which drops the extra state.

If a composite field has completed to `null`, for example because null bubbling
from a subfield produced an error null, later visits to the same response
position reuse that null and skip subfields under that revisit. When a visited
field returns a bubbling error, `visitSubfields` cancels the remaining sibling
selections in that selection set. Its intended correctness relation is data
preservation plus preservation of error presence, allowing fewer counted
execution errors than collected execution.

The main public correctness statement is
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionPreservesSpecExecution`.
It is resolver-parametric: for every resolver environment, variable assignment,
explicit fuel value, and source value, a well-formed schema and valid operation
give equivalent ungrouped and spec-facing executions, assuming
`NormalForm.operationBoolVarsComplete operation (Execution.coerceVariableValues
operation variableValues)`. Both public executors materialize operation defaults
before field collection.

The equivalence relation is `responseDataAndErrorPresenceEquivalent`, not exact
response equality:

- response data is equal,
- if the spec-facing execution has zero execution errors, ungrouped execution
  also has zero execution errors, and
- if the spec-facing execution has at least one execution error, ungrouped
  execution also has at least one execution error.

Exact `Nat` error counts are intentionally not part of the statement. The
property is data preservation plus preservation of error presence, not
preservation of detailed error counts.

A second public statement,
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionEquivalentToCancelingSiblingsExecution`,
gives the same data-and-error-presence equivalence between ungrouped execution
and `GraphQL.Algorithms.ExecutionCancelingSiblings`.

The proof witnesses are
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionPreservesSpecExecution_proof`
and
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof`
in
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/CachedRefinement/Final.lean`. The
refinement proof tracks cached composite sources recursively by collected
response-name group, proves cached execution erases exactly to the uncached
specialization for valid operations, and then reuses the uncached correctness
witnesses. Its prerequisite modules separate cache invariants, local
erasure, resolver-source soundness, and recursive cache-tree soundness under
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/CachedRefinement/`.

## Uncached Ungrouped Execution

`GraphQL.Algorithms.ExecutionUngroupedUncached` is a specialized ungrouped
algorithm with the same syntax-order traversal and sibling-canceling behavior.
It does not store resolver source values in the field state. Later compatible
composite selections reuse the previous completed response value as the
accumulator, then call the resolver again to recover the source value needed for
additional subselections.

This specialization is useful when calling a resolver is as cheap as caching its
returned source value. Its public preservation statement is
`GraphQL.Algorithms.ExecutionUngroupedUncached.ungroupedExecutionPreservesSpecExecution`,
with proof witness
`GraphQL.Algorithms.ExecutionUngroupedUncached.ungroupedExecutionPreservesSpecExecution_proof`
in
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.

The sibling-canceling equivalence statement is
`GraphQL.Algorithms.ExecutionUngroupedUncached.ungroupedExecutionEquivalentToCancelingSiblingsExecution`.
It uses the same `responseDataAndErrorPresenceEquivalent` relation. Its proof
witness is
`GraphQL.Algorithms.ExecutionUngroupedUncached.ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof`
in
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.

This relation cannot in general be strengthened to exact `Nat` error-count
equality. Field collection groups later occurrences of a response name with
the first occurrence. If a bubbling sibling is interleaved between those
occurrences, the collected sibling-canceling executor may count errors from
the later occurrence before reaching the bubble, while syntax-order ungrouped
execution cancels that occurrence.

The regression
`GraphQL.Tests.ExecutionCancelingSiblings.interleavedDuplicateErrorCountsDifferSmoke`
in `Tests/GraphQL/Algorithms/ExecutionCancelingSiblings.lean` demonstrates
this case concretely. Its selections are `hero { name }`, a bubbling `stop`
field, and then `hero { age }`. Ungrouped execution reaches `stop` in syntax
order and cancels the later `hero`, producing one error. Collected
sibling-canceling execution groups both `hero` occurrences before `stop`,
producing two errors. Both responses have the same `null` data and contain
execution errors.

As a proof utility,
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/Eager.lean` defines an eager
variant for the uncached semantics that does not cancel siblings after an error,
which bridges the spec executor and the canceling uncached ungrouped executor.

## Breadth Execution

`GraphQL.Algorithms.ExecutionBreadth` models the concrete-scope breadth-first
execution strategy used by `gmac/graphql-breadth-js`. The Lean names intentionally
track the TypeScript executor names while keeping the pure model deterministic:
`ResolverMap`, `collectFieldsByKey`, `parentTypeIsPossible`, `scheduleScope`,
`executeScheduleItem`, `drainLoop`, `ExecutionTrace`, `TraceFrame`, and
`ValueSlot`.

A scope has one concrete parent type and a list of source objects. Field
collection runs once for that concrete type, and each grouped response name is
resolved across the whole source list with a batch resolver that returns one
result per source.

Composite values are recorded as child slots during the resolution pass. Child
source lists are grouped by runtime object type and child selection set before
the child selections execute. This captures the core scheduling idea from the
TypeScript implementation: a field at one selection level sees the whole breadth
of that level, and abstract positions are expanded into concrete child work only
after runtime type resolution.

The Lean model uses a two-phase algorithm instead of JavaScript-style mutable
result objects. `drainLoop` starts at the root queue and emits a forward
breadth-first trace. Queue items are grouped by `ScheduleKey`: concrete resolver
parent type, response name, field name, and arguments. The child selection set is
kept on each `ScheduleSegment`, so cousin fields with the same resolver call can
share a batch even when their continuations differ. Composite results become
`PendingChildWork`, which is later scheduled by runtime object type and child
selection continuation.

The reverse completion pass, `completeExecutionTrace`, consumes `TraceFrame`s
from the end of the trace. Field frames complete value slots and push
segment-aligned field-result blocks keyed by `ScheduleKey`; scope frames consume
those field blocks from the field store and push completed object values onto
the positional value stack.

The Lean model intentionally omits JavaScript-specific concerns such as planning
hooks, lazy promise queues, mutation root partitioning, and detailed formatted
error maps. It also does not model lazy field resumption or the JavaScript
abort/purge side effects used to skip queued work after non-null propagation;
null propagation is applied during reverse completion with the proof-facing
`Execution.Result`.

`ResolverMap` does not require a proof that the resolver returns one result per
source. Cardinality mismatch is modeled as field errors for the current scope, a
coarse analogue of the JavaScript `ResultCountMismatchError` path without
formatted error details.

The public preservation statement is
`GraphQL.Algorithms.ExecutionBreadth.breadthExecutionPreservesSpecExecution`.
It states exact response-envelope equality against the spec-facing executor when
the breadth `ResolverMap` is `ResolverMap.fromSpecResolvers` and both executors
are run with `preservationFuelBound schema operation`, the max of the spec
depth-oriented fuel bound and the breadth scheduler-oriented fuel bound. The
proof modules under `Proofs/GraphQL/Algorithms/ExecutionBreadth/Semantics/`
prove the collection, resolver, slot, scope, queue, and final query-envelope
layers.

The theorem intentionally avoids all-fuel equality. The spec executor spends
fuel as recursive completion depth, while breadth execution spends fuel as
scheduler queue steps, so low-fuel executions can diverge even when both report
the same execution-error count.
