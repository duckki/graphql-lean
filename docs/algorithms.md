# Verified Algorithms

This document records project algorithms that are verified against the
spec-facing execution model. These algorithms are not additional GraphQL
specification features; they are implementation strategies proved equivalent to
the modeled semantics under stated assumptions.

## Sibling-Canceling Spec Execution

`GraphQL.Algorithms.ExecutionCancelingSiblings` retains the spec executor's
field collection, grouping, resolver calls, and value completion. When a
collected field result bubbles through the current selection set, it returns
immediately instead of executing the remaining sibling response positions.
Nested nullable completion still catches that bubble as `null` in the same way
as `GraphQL.Execution`.

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

`GraphQL.Algorithms.ExecutionUngrouped` is an alternative query execution
algorithm for the same scoped fragment as `GraphQL.Execution`. The spec-facing
execution model collects fields by response name before executing each response
position. Ungrouped execution visits selections directly and merges response
slices as it goes.

The design goal is to avoid the memory cost of building the complete collected
field map. Ungrouped execution traverses the query in syntax order. A first
visit to a response position calls the resolver and completes the value. A later
visit to the same response position reuses the previous response value instead
of calling the resolver again: for composite values it descends into the
subselection set and merges any newly visited child response slices; for final
scalar, enum, or null values it moves on to the next selection.

This also explains the theorem's error-count caveat. If a composite field has
already completed to `null`, for example because null bubbling from a subfield
produced an error null, later visits to the same response position reuse that
null and skip sibling subfields under that revisit. Those skipped subfields may
have produced additional execution errors in the spec-facing collected
execution. In addition, when a visited field returns a bubbling error, `visitSubfields`
cancels the remaining sibling selections in that selection set. Ungrouped execution
therefore preserves response data and whether errors are present, but it may under-count
execution errors.

The main public statement is
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionPreservesSpecExecution`.
Its proof witness is
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionPreservesSpecExecution_proof`
in `Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.

The theorem is resolver-parametric: for every resolver environment, variable
assignment, explicit fuel value, and source value, a well-formed schema and
valid operation give equivalent ungrouped and spec-facing executions, assuming
`NormalForm.operationBoolVarsComplete operation
(Execution.coerceVariableValues operation variableValues)`. Both public
executors materialize operation defaults before field collection.

The equivalence relation is `responseDataAndErrorPresenceEquivalent`, not exact
response equality:

- response data is equal,
- if the spec-facing execution has zero execution errors, ungrouped execution
  also has zero execution errors, and
- if the spec-facing execution has at least one execution error, ungrouped
  execution also has at least one execution error.

Exact `Nat` error counts are intentionally not part of the theorem. The
verified property is data preservation plus preservation of error presence, not
preservation of detailed error counts.

A second public statement,
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionEquivalentToCancelingSiblingsExecution`,
gives the same data-and-error-presence equivalence between ungrouped execution
and `GraphQL.Algorithms.ExecutionCancelingSiblings`. Its proof witness is
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionEquivalentToCancelingSiblingsExecution_proof`
in `Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`. The
proof composes both algorithms' semantic-preservation theorems through
`GraphQL.Execution`.

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
producing two errors. Both responses still have the same `null` data and
contain execution errors.

As a proof utility,
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/Eager.lean` defines an eager
variant that does not cancel siblings after an error, which bridges the spec
executor and the canceling ungrouped executor.
