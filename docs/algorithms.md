# Verified Algorithms

This document records project algorithms that are verified against the
spec-facing execution model. These algorithms are not additional GraphQL
specification features; they are implementation strategies proved equivalent to
the modeled semantics under stated assumptions.

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
execution. Ungrouped execution therefore preserves response data and whether
errors are present, but it may under-count execution errors.

The main public statement is
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionPreservesSpecExecution`.
Its proof witness is
`GraphQL.Algorithms.ExecutionUngrouped.ungroupedExecutionPreservesSpecExecution_proof`
in `Proofs/GraphQL/Algorithms/ExecutionUngrouped/Semantics/Final.lean`.

The theorem is resolver-parametric: for every resolver environment, variable
assignment, explicit fuel value, and source value, a well-formed schema and
valid operation give equivalent ungrouped and spec-facing executions, assuming
`NormalForm.operationBoolVarsComplete operation variableValues`.

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
