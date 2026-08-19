# Condition Trees

`GraphQL.Theories.ConditionTree` constructs the Boolean/type control-flow shape
used by static operation analyses. It is a project theory, not part of the
GraphQL specification. The underlying condition algebra and tree-free field
extraction live in `GraphQL.Theories.SelectionConditions` and are shared with
query inclusion.

This theory is intentionally narrower than a GraphQL operation normal form.
The top-level module owns tree construction, the tree-shape predicate, and the
tree-extraction correctness statement. `ConditionTree.Execution` owns runtime
semantics and its soundness predicates. `ConditionTree.Reduce` owns reduction
from input selections to condition-tree-based selections and its semantic
preservation predicate.

## Conditions

Each tree node has one cumulative `Condition`:

```text
(possible object types, Boolean literals)
```

The possible-type component starts at the possible objects of the root or
parent field's named type. A type-conditioned inline fragment intersects that
list with the fragment type's possible objects. Intersection preserves the
parent list's order, so semantically equal intersections have equal keys even
when their source type-condition paths differ.

The Boolean component is a canonical conjunction:

- `positive x` represents `@include(if: $x)`;
- `negative x` represents `@skip(if: $x)`;
- the empty list represents true; and
- contradictory polarities make a path infeasible.

Constant no-op directives contribute no literal. Constant-false or unsupported
conditional arguments make the governed path infeasible.

Boolean literals are global across a response-field boundary. Scoped extraction
accepts the parent field's inherited Boolean condition. A matching literal is
removed from the local condition rather than repeated, while its complement
makes that path infeasible.

## Single-Condition Branches

Each entry in `Tree.branches` is a `Branch` with exactly one
`BranchCondition` and one subtree:

- `typeCondition T`; or
- `booleanLiteral literal`.

An inline fragment is expanded deterministically before insertion. Its optional
type condition comes first, followed by its Boolean literals in directive
syntax order. A field contributes its Boolean literals in the same way, but has
no type-condition branch. For example:

```graphql
... on Dog @skip(if: $y) @include(if: $x) {
  name
}
```

becomes the branch path:

```text
typeCondition Dog
└── booleanLiteral (negative y)
    └── booleanLiteral (positive x)
        └── field name
```

The cumulative `Condition` stored at each node still canonicalizes Boolean
literals, so branch order is deterministic without making conjunction order
semantically significant.

## Tree Extraction

`ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet`
creates a root node and walks the source selections. `ofSelectionSet` is the
root-boundary specialization with no inherited literals:

1. Each inline fragment expands into a type branch followed by Boolean-literal
   branches in syntax order; each field expands its directives into
   Boolean-literal branches.
2. Those branches extend the current cumulative condition one at a time.
3. Infeasible paths are omitted.
4. Every feasible field is inserted at the node for its cumulative type and
   Boolean condition, with its directive list cleared.
5. Fields at the node are collected by response name. The first occurrence
   fixes group order and later occurrences append to that group.
6. When the condition already exists, its field is added to that node's group.
7. Otherwise, source-derived branches are greedily removed while
   the remaining path still reaches the same cumulative condition.
8. If retained abstract type conditions intersect to the singleton possible
   object `{X}`, they are replaced by one `typeCondition X` branch.
9. Repeated cumulative states are removed from the retained path.

Canonical extraction is variable independent. The request-aware
`ofSelectionSetInScopeWithKnownFalsePruning` entry point accepts already-coerced values.
TreeSummary's operation entry points apply supplied values and operation defaults before
using it at each selection-set boundary. This path removes a field or inline-fragment
subtree only when a modeled directive is known not to receive its required Boolean value:

- `@include(if: $x)` requires `x = true`;
- `@skip(if: $x)` requires `x = false`;
- matching, missing, and unavailable values retain the edge.

In particular, a known-active edge is not collapsed. Keeping it preserves the canonical
condition grouping seen by Syntactic summaries, including analyses with signed transfers
or non-idempotent `join`. Inline fragments are pruned recursively in their current
boundary; field children are pruned when their own condition tree is extracted.

The core `Operation` syntax is fragment-free. Named fragment spreads are inlined by the
separate `GraphQL.NamedFragment` layer before this extractor receives the resulting field
and inline-fragment selections, so no distinct fragment-spread extraction case exists
here.

`KnownFalsePruningSound` is the proof-facing fixed-request correctness statement. It
and `BooleanValuesMatchForPruning` live with their witness,
`ConditionTree.knownFalsePruning_sound`, which proves that the pruned tree and
`collectFields` contain the same runtime field occurrences whenever every Boolean known
by the pruning environment agrees with the execution environment. The proof also lifts
to runtime response-name groups. Canonical `ExtractionSound` remains unchanged.

The result contains each cumulative condition at most once. Equivalent source
paths therefore share fields at one node, and partially redundant source paths
retain only the individual branches needed to reach that node.

The singleton-object rewrite deliberately chooses the concrete object as the
node's syntactic parent. For example, an intersection represented by `on I; on
J` with possible objects `{X}` becomes `on X`. A later `... on X { a }` can
therefore merge into that node. Keeping the abstract sequence would put the
node under `J`, where inserting a field selected only under `X` may not be
syntactically valid. In the reverse direction, a field selected under an
abstract condition may be merged into the `X` node. Such a field could make the
result invalid if it is unavailable on `X`; this is the benign direction, since
validity assumptions on the input are expected to exclude that case.

Collected field groups and their selections keep source order within their
node. `FieldGroup` has an explicit head and tail, so empty groups are
unrepresentable. Its stored `Field` type contains only the field name,
arguments, and child selection set: directives and non-field selections are
unrepresentable as well. Field directives become Boolean tree branches, and
contradictory field conditions are omitted during extraction.

Nested field selection sets are independent boundaries. A consumer such as
tree summarization merges a collected response-name group's child
selection sets and calls `ofSelectionSetInScope` recursively with that field's
named output type and inherited global Boolean condition.

## Reduction

`GraphQL.Theories.ConditionTree.Reduce` reduces an input selection set to
condition-tree-based selection syntax. `reduce` first extracts the current tree
with `ofSelectionSetInScope`. It then reduces the tree's field groups and
condition branches. For each field group it selects one representative field,
constructs a child tree from `group.mergedSelectionSet`, and recursively reduces
that child tree. Schema lookup supplies the child's named output type, while the
current cumulative Boolean condition becomes its inherited condition.
`reduceOperation` starts this traversal at the operation root.

Reduction serializes field-derived Boolean branches as directive-bearing inline
fragments around the field. The field selection itself remains condition-free.

This is the same tree-of-trees recursion shape as execution. Their shared
response-depth definitions and extraction bound live in
`ConditionTree.Termination`. Reduction terminates lexicographically: traversal
inside one extracted tree decreases structural size, while a child tree
constructed from a merged field group has strictly lower response depth. If
schema lookup fails, reduction preserves the group's condition-free field
occurrences.

`ReductionSound` states semantic preservation between the input selection set
and `reduce` output for every resolver environment, variable assignment,
explicit fuel, and applicable object source. It assumes an object execution
boundary, a well-formed schema, selection validity, and `FieldsInSetCanMerge`;
without merge validity, an alias collision can make source order and tree
preorder choose different representative fields. Extraction and validation may
use an abstract static parent; execution is quantified over each concrete
runtime object admitted by that parent.

`ReduceOperationSound` is the operation-level counterpart for
`reduceOperation`. It assumes a well-formed schema and a valid source operation,
then compares execution of the source and reduced operations at every shared
explicit fuel value. `Proofs.GraphQL.Theories.ConditionTree.Reduce` proves these
statements as `reduction_sound` and `reduceOperation_sound`. Its mutual proof
follows execution through grouped fields, object completion, and list completion
using runtime bundles that retain each reduced representative together with all
of its source fields and recursively reduced child boundaries. The proof is split
between `Reduce.RuntimeBundles`, `Reduce.Semantics`, and the small public witness
module.

## Runtime Coverage

`GraphQL.Theories.ConditionTree.Execution` gives conditions their runtime
meaning for a variable environment and concrete object type. A tree field is
selected exactly when its cumulative node condition allows it. Tree execution
does not re-evaluate field directives because extracted fields are
condition-free. Consequently `Tree.collectRuntimeFields` needs only variable
values plus the execution and runtime object type; schema and source values are
used by source collection, not by interpretation of an already extracted tree.
The same module owns source/tree coverage and whole-operation
execution-equivalence predicates.

`ExtractionSound` compares those selected tree fields with the actual
result of `Execution.collectFields`. Because execution groups fields by
response name, `flattenCollectedFields` forgets only that grouping before the
comparison. The statement assumes that:

- the inherited Boolean condition is true at the selection-set boundary; and
- the concrete runtime object type is one of the parent type's possible
  objects.

Under those boundary assumptions, every executable field is a member of the
tree interpretation exactly when it is a member of the flattened execution
collection. This covers field directives, nested inline fragments, type
conditions, contradictory Boolean paths, equivalent/minimized condition paths,
and the response-name grouping performed by execution.

`Proofs.GraphQL.Theories.ConditionTree.Soundness` proves
`extraction_sound`, which establishes this property for
`ofSelectionSetInScope`. The result is independent of any particular downstream
consumer.

`RuntimeFieldGroupsEquivalent` strengthens that membership result to grouped
runtime collection. It preserves the set of response-name keys and the set of
executable fields while ignoring group order and repeated identical source
occurrences. This set-like public relation is useful for extensional coverage;
the execution-equivalence proof strengthens it internally to a permutation of
all executable occurrences. The theorem `extraction_groups_equivalent` proves
`ExtractionGroupsEquivalent` for every extracted boundary.

## Tree Execution

`GraphQL.Theories.ConditionTree.Execution` traverses active tree fields in the
same preorder used by tree summarization: the current node's field groups
first, then condition children in tree order. A node stores only its local
fields; parent fields are not copied into its children.

GraphQL must resolve each response name once even when several active
conditions contribute selections to it. `groupExecutableFields` therefore
folds the tree-ordered field stream into one global response-name map. The
first occurrence fixes execution order. A matching field at a descendant is
merged into that existing group and is excluded from becoming a second child
visit.

`RuntimeFieldGroupsExact` records both relevant invariants:

- executable response-name keys are `Nodup`; and
- flattening the groups is a permutation of the active field stream.

`Proofs.GraphQL.Theories.ConditionTree.Execution` proves the generic
`groupExecutableFields_exact` theorem and its
`Tree.collectRuntimeFieldGroups_exact` specialization. Consequently grouping
neither loses nor duplicates a contributing field occurrence.

`executeSelectionSet` is a genuinely recursive tree-based selection-set evaluator. At
each boundary it extracts the condition tree internally. When object completion reaches
a merged child selection set, it calls `executeSelectionSet` again with that selection
set. The extracted `Tree` is not part of the execution API. Execution never delegates
nested work to `Execution.executeCollectedFields` or another specification-executor
entry point.

Termination is proved lexicographically. Nested object completion strictly
decreases response-selection depth; within one boundary, traversal phase and
structural list/type/value size decrease. There is no execution-fuel argument
and no out-of-fuel result in tree semantics. `executeQuery` adds
variable coercion and the same root-source applicability check as the
specification-facing operation executor.

`ExecutionEquivalent`, declared in
`GraphQL.Theories.ConditionTree.Execution`, states that total tree execution
and the public query executor produce semantically equivalent responses,
allowing object field reordering while preserving values and execution-error
counts.

`Proofs.GraphQL.Theories.ConditionTree.RuntimeExtraction` proves the shared
occurrence-preserving extraction and runtime-group permutation layer. It is
usable independently by condition-tree reduction and tree-summary soundness
proofs.

`Proofs.GraphQL.Theories.ConditionTree.ExecutionEquivalence` imports that layer
and proves the statement as
`ConditionTree.ExecutionEquivalence.execution_equivalent`. The remaining proof
follows field execution and value completion recursively.
Nested object completion decreases response-selection depth; list and non-null
completion are handled by the same mutual correspondence proof. The final
operation wrapper uses the schema-aware `Execution.executeQueryFuelBound` for
the public query executor and transports the selection-set result through
response canonicalization.

The same semantic proof is exposed at arbitrary sufficient fuel as
`execution_equivalent_of_sufficient_fuel`. Separately, the proof-side theorem
`Execution.doesNotExhaustFuel` shows that `Execution.executeQueryFuelBound`
covers the executor's structural response-depth fuel requirement. It is a
numeric proof from response depth to operation size and does not mention
response equivalence.

## Well-Formedness Predicate

`tree.WellFormed schema inheritedBooleanCondition` states:

- the preorder list of all cumulative `Condition` keys is globally `Nodup`;
- every condition has a nonempty possible-type intersection and a satisfiable
  conjunction with the inherited Boolean condition;
- no node repeats a literal already present in the inherited condition;
- every stored branch edge is the transition computed from its parent condition;
- collected response names are `Nodup` at every node.

Field groups are nonempty and stored fields are condition-free by type, so
`Tree.WellFormed` no longer restates or recursively proves those structural
facts.

`Proofs.GraphQL.Theories.ConditionTree.ExtractionCoherence` proves preservation
of the branch-edge invariant, and
`Proofs.GraphQL.Theories.ConditionTree.Extraction` proves `extraction_correct`,
the witness for the public `ExtractionCorrect` statement,
as well as the direct `ofSelectionSetInScope_wellFormed` theorem. The statement
assumes the parent type has at least one possible object and the inherited
Boolean condition is feasible. Root-selection and operation wrappers specialize
this result; a well-formed schema discharges the operation root's nonemptiness
automatically.

## Public Surface

- `Condition`, `BranchCondition`, `Branch`, `Field`, `FieldGroup`, and `Tree`
  are the representation types. `NamedField` is used only while inserting a
  field before its response name becomes owned by a group. Only `Branch`
  carries an incoming condition; the root `Tree` does not.
- `rootCondition` constructs a boundary root.
- `ofSelectionSetInScope` extracts a boundary relative to inherited literals.
- `ofSelectionSet` extracts one selection-set tree.
- `ofOperation` extracts the operation-root tree.
- `Tree.WellFormed` is the public invariant predicate.
- `ExtractionCorrect` states that scoped extraction produces a well-formed tree
  from a feasible parent boundary.
- `Condition.allows` and `Tree.collectRuntimeFields` interpret an extracted
  tree at runtime.
- `groupExecutableFields` and `Tree.collectRuntimeFieldGroups` produce one
  tree-ordered executable group per response name.
- `RuntimeFieldGroupsExact` states that grouping is duplicate-free and retains
  every active field occurrence exactly once.
- `executeSelectionSet` and `executeQuery` are the fuel-free recursive
  condition-tree execution surface; `executeSelectionSet` accepts selection syntax and
  keeps extracted trees internal.
- `ExecutionEquivalent` in the execution module states preservation against the
  specification-facing query executor.
- `RuntimeFieldGroupsEquivalent` and `ExtractionGroupsEquivalent` state
  duplicate- and order-insensitive equivalence with spec field collection.
- `ExtractionSound` states execution-facing field-collection coverage.
- `flattenCollectedFields` exposes membership in execution's collected groups.
- `reduce` extracts the input selection set, follows the same
  tree/group/child-tree decomposition as execution, and recursively reduces
  merged field-group children; `reduceOperation` applies it from the operation
  root. `ReductionSound` and `ReduceOperationSound` state selection-set and
  operation-level semantic preservation, respectively.

The construction is executable and fuel-free. Its invariant and runtime
coverage proofs do not make abstract analyses depend on an unfinished
whole-operation normal form.
