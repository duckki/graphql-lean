# Query Execution

This guide documents the specification-facing
[`GraphQL.Execution`](../GraphQL/Execution.lean) model and its shared input and
response abstractions. The target is the
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).
See the [conformance summary](spec-conformance.md) for coverage and exclusions,
and [algorithms](algorithms.md) for alternative executors.

## Resolver and response boundary

Execution is parameterized by abstract resolver functions. Runtime object values
carry a GraphQL object type and an optional resolver-owned opaque reference;
final responses contain neither object identity nor detailed error metadata.
Semantic equivalence can therefore quantify over resolver environments, variable
values, explicit fuel values, and source values.

Execution collects fields by response name, resolves a grouped field, completes
its value, and accumulates counted errors. `Response` is a data/errors envelope;
`Result` distinguishes completed data from an error bubbling through a non-null
position. The explicit fuel parameter bounds recursive completion, with
`Execution.outOfFuel` represented by `.error 1`.

## Inputs and defaults

Supplied variable values and operation defaults are assumed already coerced and
type-conformant. The model implements the default-value branch of spec 6.1.2:
an omitted supplied variable receives its operation default, including an explicit
`null` default. Any supplied value, including supplied `null`, takes precedence.

Before a resolver is invoked, `coerceArgumentValues` removes variable syntax and
materializes schema argument defaults and nested input-object field defaults.
Omitted values and undefined variables activate defaults; explicit `null` does
not. Schema well-formedness rejects input-object default-expansion cycles.
Execution remains bounded for permissive raw schemas; this does not impose a
bound on finite, user-supplied recursive inputs through nullable or list fields.

Defaulting happens before directive evaluation. The `if` argument of `@skip`
and `@include` has type `Boolean!`, but spec 5.8.5 permits a nullable Boolean
variable at that location when its operation definition has a non-null default.
An omitted variable uses that default during field collection.

## Specification correspondence

`GraphQL.Execution` follows the September 2025 execution algorithm names where
practical:

- `coerceVariableValues` models the default-value portion of spec 6.1.2 before
  query execution and therefore before `@skip` / `@include` evaluation.
- `collectFields` / `collectSubfields` model spec 6.3.2 field collection with
  ordered list-backed response-name groups. `@skip` / `@include` conditions are
  evaluated dynamically during collection with the spec's literal "is true"
  test and never raise errors: a condition that does not resolve to a Boolean
  (an undefined variable, an explicit `null`, or a non-Boolean binding) behaves
  like `false` for both directives, so `@skip` keeps the selection and
  `@include` drops it. Spec validation (5.8.5) makes the undefined-variable
  case unreachable for valid documents; the explicit-`null` case is reachable
  through a nullable variable with a non-null default. Note that graphql-js
  deviates from the spec algorithm here: it coerces directive arguments at the
  evaluation point and raises a located error for `null` conditions. The model
  follows the spec text.
- `executeRootSelectionSet`, `executeCollectedFields`, `executeField`,
  `completeValue`, and `completeValueList` model the spec 6.3/6.4 execution
  ladder at an explicit recursion-fuel bound.
- `executeField` performs the schema lookup once and passes the resulting
  `FieldDefinition` to `resolveFieldValue`; resolver argument coercion reuses that
  definition instead of repeating the lookup.
- `Result` carries the spec 6.4.4 null-bubbling control flow. `.error n` means
  an execution error has bubbled through a non-null response position;
  `.ok (value, n)` means completion produced data and accumulated `n` execution
  errors below it.
- `Response` models the spec 7.1 execution result as `data` plus a `Nat` count
  standing in for the detailed non-empty `errors` list.
- Resolver failure is modeled as `none` and handled like a field execution
  error. Schema lookup misses, empty collected field groups, invalid root source
  values, fuel exhaustion, and runtime/type-shape mismatches are counted errors
  in this partial executable model; validation and store well-typedness
  assumptions rule out the invalid-operation cases used by semantic proofs.
- `executeCollectedFields` combines the ordered response field lists with
  `List.append`, matching the spec's ordered collection behavior directly.
- Scalar/enum result coercion and abstract `ResolveAbstractType` are abstracted:
  scalar results are represented as strings, and object runtime type is carried
  by `ResolverValue.object`.

## Named-fragment execution

[`GraphQL.NamedFragment`](../GraphQL/NamedFragment/) provides separate
fragment-aware operation syntax, validation, direct execution, and static inlining
into the core operation model. Direct collection threads the spec's
`visitedFragments` context and filters repeated spreads. The execution bridge
shows that the repeated fields retained by static inlining are absorbed during
execution.

The all-variables-used check follows fragment spreads transitively and does not
count uses in unreferenced fragments. Core validation also includes recursive
input-object checks, variable/input-type compatibility with the nullable-variable
default exception, non-empty root/composite selection sets, and response-name
merge compatibility. These remain assumptions separate from permissive raw syntax.

## Conformance fixtures

The graphql-js oracle compares ordered response data and `errors.length` for
the core and named-fragment executors. Messages, paths, locations, extensions,
asynchronous scheduling, and resolver information metadata are projected away.
The fixtures include omitted nullable Boolean variables with non-null defaults
used by `@skip` and `@include`.

Generation, build, and oracle commands live in the
[fixture guide](../conformance/graphql-js/README.md).
