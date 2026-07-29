# Spec Conformance Plan

This document records the current plain GraphQL scope and proof plan. The
canonical spec target is the GraphQL September 2025 Edition.

The immediate priority is spec conformance for a query-only executable fragment
large enough to state validation and resolver-parametric execution semantics.

## Goals

The current conformance target includes:

- query operation execution semantics,
- object, interface, union, enum, scalar, input object, list, and non-null type
  references as represented in `GraphQL.Schema`,
- schema well-formedness predicates separated from raw schema syntax, including
  default-value validity, non-empty type member/field lists, and
  object/interface implementation compatibility,
- field selection validation, argument name validation, required argument
  presence, all declared variables used in operation scope, variable-use
  compatibility at input locations, leaf and composite selection shape,
  non-empty operation and composite selection sets,
  inline-fragment applicability, and field merge compatibility,
- inline fragments,
- named fragment definitions and fragment spreads in the separate
  `GraphQL.NamedFragment` public layer, with theorem bridges under
  `Proofs.GraphQL.NamedFragment`,
- variables, operation variable defaults, and the built-in executable
  directives `@skip` and `@include`,
- possible-object semantics for abstract types,
- execution field errors as resolver failure counts in the query response
  envelope,
- response null bubbling through non-null output wrappers.

## Explicitly Skipped

These are out of scope for the current conformance pass:

- mutation execution,
- subscription execution,
- custom directives and directive definitions beyond modeled `@skip` and
  `@include`,
- full input coercion and result coercion beyond materializing operation variable
  defaults,
- scalar and enum literal coercion details; validation records structural
  input-object and variable/input-type compatibility, while assuming values are
  already coerced where scalar semantics would matter,
- introspection and meta-fields,
- request errors, detailed execution error maps, `extensions`, error paths,
  and error locations,
- serialization details,

The working assumption is that supplied variable values and operation defaults
entering execution are already coerced and type-conformant. Execution models the
default-value branch of spec 6.1.2 `CoerceVariableValues`: a missing supplied
variable receives its operation default, including an explicit `null` default,
while any supplied value, including supplied `null`, takes precedence. The model
does not yet perform type coercion or produce request errors for missing/null
required variables.

This defaulting step is observable for the modeled directives. Their `if`
argument has type `Boolean!`, while spec 5.8.5 permits a nullable `Boolean`
variable at that location when its operation definition has a non-null default.
When the request omits that variable, spec 6.1.2 materializes the default before
field collection, so `@skip` and `@include` evaluate the defaulted Boolean.

## Execution Alignment Notes

`GraphQL.Execution` follows the September 2025 execution algorithm names where
practical:

- `coerceVariableValues` models the default-value portion of spec 6.1.2 before
  query execution and therefore before `@skip` / `@include` evaluation.
- `collectFields` / `collectSubfields` model spec 6.3.2 field collection with
  ordered list-backed response-name groups.
- `executeRootSelectionSet`, `executeCollectedFields`, `executeField`,
  `completeValue`, and `completeValueList` model the spec 6.3/6.4 execution
  ladder at an explicit recursion-fuel bound.
- `outOfFuel` is the shared polymorphic internal truncation result. It returns
  `.error 1`, so fuel exhaustion behaves like an execution error at the current
  response position instead of fabricating partial response data.
- `Result` carries the spec 6.4.4 null-bubbling control flow. `.error n`
  means an execution error has bubbled through a non-null response position;
  `.ok (value, n)` means completion produced data and accumulated `n`
  execution errors below it.
- `Response` models the spec 7.1 execution result as `data` plus a `Nat`
  count standing in for the detailed non-empty `errors` list. The model does
  not distinguish error paths, locations, messages, or extensions.
- Resolver failure is modeled as `none` and handled like a field execution
  error. Schema lookup misses, empty collected field groups, invalid root
  source values, fuel exhaustion, and runtime/type-shape mismatches are
  counted errors in this partial executable model; validation and store
  well-typedness rule out the invalid-operation cases used by semantic proofs.
- `executeCollectedFields` combines the ordered response field lists with
  `List.append`, matching the spec's ordered collection behavior directly.
- Scalar/enum result coercion and abstract `ResolveAbstractType` are abstracted:
  scalar results are represented as strings, and object runtime type is carried
  by `ResolverValue.object`.

## Current Status

The main modules are:

- `GraphQL.Schema`: raw schema syntax, type references, type categories, lookup,
  possible-object helpers, constant default-value validation, and output subtype
  helpers for interface implementation checks.
- `GraphQL.SchemaWellFormedness`: schema well-formedness predicates for the
  scoped fragment, including uniqueness, non-empty definition/member lists,
  valid type references/defaults, query root existence, and object/interface
  implementation compatibility.
- `GraphQL.Operation`: operation syntax, variables, inline fragments, and
  modeled directive applications.
- `GraphQL.Validation`: operation validity predicates for the current fragment,
  including recursive input-object validation, the spec 5.8.4
  all-variables-used rule, and spec-style variable-use compatibility with the
  nullable-variable default exception, plus required non-empty root/composite
  selection sets and same-response-name merge compatibility checks.
- `GraphQL.Execution`: bounded resolver-based execution with compatibility data
  projection, operation-variable default materialization, response null
  bubbling through non-null output wrappers, and a query response envelope
  containing data plus a `Nat` execution-error count.
- `GraphQL.NamedFragment`: separate fragment-aware public operation syntax,
  validation, direct fragment-aware execution, and inlining support for
  equivalence proofs under `Proofs.GraphQL.NamedFragment`. Its
  all-variables-used check follows fragment spreads transitively and does not
  count uses in unreferenced fragments.

Conformance testing now includes graphql-js execution projections under
`conformance/graphql-js/`. The fixtures intentionally compare only the behavior
represented by `GraphQL.Execution` and `GraphQL.NamedFragment.Execution`:
ordered response data and execution-error count. The graphql-js oracle script
projects `errors.length` and drops messages, paths, locations, extensions,
async scheduling details, and resolver info metadata. Generated Lean tests for
the fragment-free execution model live under `Tests/Conformance/Execution/`.
They include omitted nullable Boolean variables with non-null defaults used by
both `@skip` and `@include`. The tests are regenerated with:

```sh
npm --prefix conformance run gen:graphql-js
lake build Tests.Conformance.Execution
```

Named-fragment fixtures live under `conformance/graphql-js/named-fragment-cases/`
and are regenerated with:

```sh
npm --prefix conformance run gen:graphql-js:named-fragment
lake build Tests.Conformance.NamedFragment
```

When a local graphql-js package or checkout is available, the same fixtures can
be checked against graphql-js with:

```sh
GRAPHQL_JS_MODULE=graphql npm --prefix conformance run oracle:graphql-js
```

The named-fragment oracle can be checked with:

```sh
npm --prefix conformance run oracle:graphql-js:named-fragment
```

## Related Documentation

- `docs/overview.md`: project structure and module dependency map.
- `docs/references.md`: GraphCoQL notes and proof strategy references.
- `docs/normal-form.md`: project-specific normal forms and their correctness
  properties.
- `docs/algorithms.md`: verified project algorithms outside the GraphQL spec.
- `README.md`: build, lint, and entry-point information.
- `conformance/graphql-js/README.md`: graphql-js fixture and oracle workflow.
