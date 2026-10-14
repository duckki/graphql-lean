# Query Execution

This guide documents the specification-facing
[`GraphQL.Execution`](../GraphQL/Execution.lean) model and its shared input and
response abstractions. The target is the
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).
See the [conformance summary](spec-conformance.md) for coverage and exclusions, and
[query inclusion](theories/query-inclusion.md) for the selected-path comparison built
on this model's field collection.

## Resolver and response boundary

Execution is parameterized by abstract resolver functions. Runtime object values
carry a GraphQL object type and a resolver-owned opaque reference;
final responses contain neither object identity nor detailed error metadata.
The resolver reference type and resolver functions are parameters of execution, so
the model is independent of a particular database or host object representation.
Resolvers must return equal results for equivalent coerced argument maps.

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
  through a nullable variable with a non-null default. This describes the model's
  behavior on permissive syntax; valid-input guarantees require the separate
  validation and input assumptions.
- `executeRootSelectionSet`, `executeCollectedFields`, `executeField`,
  `completeValue`, and `completeValueList` model the spec 6.3/6.4 execution
  ladder at an explicit recursion-fuel bound.
- `executeField` looks up the `FieldDefinition`, uses its argument definitions to
  prepare a coerced argument map, and passes that map to `resolveFieldValue`. The
  same field definition supplies the output type used for completion.
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
  assumptions are separate from this behavior on raw inputs.
- `executeCollectedFields` combines the ordered response field lists with
  `List.append`, matching the spec's ordered collection behavior directly.
- Scalar/enum result coercion and abstract `ResolveAbstractType` are abstracted:
  scalar results are represented as strings, and object runtime type is carried
  by `ResolverValue.object`.

## Validation stays separate

Schema well-formedness and operation validity are propositions over permissive raw
syntax. Core validation includes recursive input-object checks, variable/input-type
compatibility with the nullable-variable default exception, non-empty root/composite
selection sets, inline-fragment applicability, and response-name merge compatibility.
The executor does not establish those premises for its caller.

This branch retains the core fields and inline-fragment model. Named fragments,
incremental delivery, and external graphql-js conformance tooling are outside the
branch's scope.

## Connection to query inclusion

`ResponsePath.operationSelectsPath` uses `collectFields` with a synthetic object
source. Its recursive path predicate uses `collectSubfields` to merge the children
of an entire response-name group. These functions inspect an object source's runtime
type, so a unit resolver reference is sufficient for describing selection.

Selected paths record field identity, arguments up to syntactic reordering, concrete
parent objects, and output types. They describe the selected-field footprint without
running resolvers, completing values, or constructing a response. The reference
inclusion checker uses the same collection functions, which is why execution is useful
background for the proof exercise even though that exercise proves a syntactic relation.

The retained regression tests exercise the query-inclusion checker. A successful
checker test or selected-path theorem is not a proof of an external executor's behavior.
