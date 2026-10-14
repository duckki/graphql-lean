# Query inclusion

The talk uses two definition modules:

- `GraphQL.Theories.QueryInclusion`: condition-variable extraction, selected-path
  inclusion, an exhaustive reference checker, and its correctness propositions.
- `GraphQL.Theories.ResponsePath`: Boolean assignment support and selected response
  paths built from field collection.

The prepared exercise baseline contains definitions, concrete regression tests, and a
focused proof scaffold. Soundness and completeness remain the final exercise statements;
the scaffold supplies the Boolean-enumeration and selected-path bridges used to prove
them. Execution-semantic inclusion and its additional assumptions are outside scope.

## Selected-path contract

`QueryInclusion.includes schema left right` requires both:

1. Shared variable definitions have equal raw types and syntactically equivalent
   defaults, disregarding declaration order. One-sided declarations are unrestricted.
2. Under every Boolean assignment complete for the condition variables used by either
   operation, every path selected by `right` is also selected by `left`.

A path records concrete parent object types, response names, field names, argument
syntax up to reordering, and output types. It is richer than a list of field names.
`ResponsePath.operationSelectsPath` uses field collection and merged subselections;
empty paths are not selected.

## Reference implementation

`includesBoolReference` first checks equal root types and shared-variable compatibility.
It enumerates every Boolean assignment over the union of both operations' condition
variables, then calls `selectionSetIncludesBoolWithFuel` with `right.size + 1` fuel.
For each possible runtime object type, it collects active fields, matches right-hand
response groups to left-hand groups, checks resolver-call identity and arguments, and
recurses over merged composite children and their possible runtime types.

Every condition variable is explicitly assigned, so omitted variable defaults cannot
change field collection in these enumerated cases. The checker is total on raw syntax;
it does not validate its arguments. Enumeration can be exponential in the number of
condition variables, so keep talk and porting examples small.

## Correctness statements and exercise

`IncludesBoolReferenceSound schema left right` states:

- the schema is well-formed;
- the left and right operations are valid;
- the checker returns `true`;
- therefore `QueryInclusion.includes schema left right`.

Proving this proposition by composing the supplied bridges is the exercise.
`IncludesBoolReferenceComplete` uses the same schema and validity assumptions and states
the reverse implication, from inclusion to checker acceptance. The proposition
definitions alone are not proofs; the exercise baseline omits their final witnesses.
Do not infer universal correctness from the concrete tests. The supporting lemmas are
exposed by [`QueryInclusion.Support`](../../Proofs/GraphQL/Theories/QueryInclusion/Support.lean).

## Scope of the result

The contract compares selected paths in this Lean model. It does not state inclusion of
executed responses or establish a production cache-reuse guarantee. The retained tests
cover aliases and resolver-call identity, arguments and shared variable definitions,
conditional selection, merged child fields, and possible runtime types.

A Rust port requires separate evidence of agreement, such as differential fuzzing;
concrete test agreement does not prove universal equivalence.
See the [porting guide](query-inclusion-porting.md) for the executable dependency map,
native representation choices, and comparison requirements.
