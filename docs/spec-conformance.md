# Spec Conformance Summary

This document records the GraphQL spec-conformance work completed in this repo
and the boundaries of the modeled fragment. It is descriptive: it captures what
the Lean model, proof modules, and conformance fixtures cover, plus the features
that are intentionally out of scope.

The canonical spec target is the GraphQL September 2025 Edition.

## Implemented Scope

The modeled fragment covers query execution for a plain GraphQL subset.

### Schema And Type System

The schema layer includes object, interface, union, enum, scalar, input object,
list, and non-null type references as represented in `GraphQL.Schema`.

Schema well-formedness predicates are separated from raw schema syntax. They
cover type-name uniqueness, field/member non-emptiness, valid type references,
default-value validity, query root existence, possible-object semantics for
abstract types, and object/interface implementation compatibility.

### Operations And Validation

The core operation layer includes query operations with one root selection set,
variables, operation variable defaults, inline fragments, and the built-in
executable directives `@skip` and `@include`.

Operation validation covers field selection validity, argument name validity,
required argument presence, all declared variables used in operation scope,
variable-use compatibility at input locations, leaf and composite selection
shape, non-empty operation and composite selection sets, inline-fragment
applicability, and same-response-name field merge compatibility.

The working assumption is that supplied variable values and operation defaults
entering execution are already coerced and type-conformant. Execution models the
default-value branch of spec 6.1.2 `CoerceVariableValues`: a missing supplied
variable receives its operation default, including an explicit `null` default,
while any supplied value, including supplied `null`, takes precedence.

The `GraphQL.Execution.Resolvers` boundary receives the schema-derived argument map.
Before it is invoked, `coerceArgumentValues` removes variable syntax and materializes
schema argument defaults plus nested input-object field defaults. An omitted value or
undefined variable activates a default; explicit `null` does not. Recursive default
expansion is bounded while raw schema default cycles remain outside schema
well-formedness.

This defaulting step is observable for the modeled directives. Their `if`
argument has type `Boolean!`, while spec 5.8.5 permits a nullable `Boolean`
variable at that location when its operation definition has a non-null default.
When the request omits that variable, spec 6.1.2 materializes the default before
field collection, so `@skip` and `@include` evaluate the defaulted Boolean.

### Named Fragments

Named fragment definitions and fragment spreads live in the separate
`GraphQL.NamedFragment` public layer. Proof bridges connect that fragment-aware layer to
the core operation model.

### Execution

Execution is resolver-parametric over opaque object references. The model covers
field collection, grouped field execution, completion for nullable/non-null/list
wrappers, execution field errors as resolver failure counts in the query
response envelope, and response null bubbling through non-null output wrappers.

## Execution Model

`GraphQL.Execution` follows the September 2025 execution algorithm names where
practical:

- `coerceVariableValues` models the default-value portion of spec 6.1.2 before
  query execution and therefore before `@skip` / `@include` evaluation.
- `collectFields` / `collectSubfields` model spec 6.3.2 field collection with
  ordered list-backed response-name groups.
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

## Module Summary

The main public modules are:

- `GraphQL.Schema`: raw schema syntax, type references, type categories, lookup,
  possible-object helpers, constant default-value validation, and output subtype
  helpers for interface implementation checks.
- `GraphQL.SchemaWellFormedness`: schema well-formedness predicates for the
  scoped fragment, including uniqueness, non-empty definition/member lists,
  valid type references/defaults, query root existence, and object/interface
  implementation compatibility.
- `GraphQL.Operation`: core operation syntax, variables, inline fragments, and
  modeled directive applications.
- `GraphQL.Validation`: operation validity predicates for the current fragment,
  including recursive input-object validation, the spec 5.8.4 all-variables-used
  rule, and spec-style variable-use compatibility with the nullable-variable
  default exception, plus required non-empty root/composite selection sets and
  same-response-name merge compatibility checks.
- `GraphQL.Execution`: bounded resolver-based execution with compatibility data
  projection, operation-variable default materialization, schema-aware resolver
  argument materialization, response null bubbling through non-null output wrappers,
  and a query response envelope containing data plus a `Nat` execution-error count.
- `GraphQL.NamedFragment`: fragment-aware public operation syntax, validation, direct
  fragment-aware execution, and static inlining with equivalence proofs. Direct field
  collection threads the spec `visitedFragments` context and filters repeated spreads. The
  general execution bridge proves that the repeated fields retained by static inlining are
  absorbed during execution. Its all-variables-used check follows fragment spreads
  transitively and does not count uses in unreferenced fragments.

The non-spec algorithms and proof-status details, including ungrouped execution
and normal-form work, are documented separately in `docs/algorithms.md` and
`docs/normal-form.md`.

## Conformance Fixtures

Conformance testing includes graphql-js execution projections under
`conformance/graphql-js/`. The fixtures intentionally compare only the behavior
represented by `GraphQL.Execution` and `GraphQL.NamedFragment.Execution`:
ordered response data and execution-error count. The graphql-js oracle script
projects `errors.length` and drops messages, paths, locations, extensions, async
scheduling details, and resolver info metadata.

Generated Lean tests for the fragment-free execution model live under
`Tests/Conformance/Execution/`. They include omitted nullable Boolean variables
with non-null defaults used by both `@skip` and `@include`. The tests are
regenerated with:

```sh
npm --prefix conformance run gen:graphql-js
lake build Tests.Conformance.Execution
```

Named-fragment fixtures live under
`conformance/graphql-js/named-fragment-cases/` and are regenerated with:

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

## Out Of Scope

These GraphQL features and runtime details are intentionally not modeled:

- mutation execution;
- subscription execution;
- custom directives and directive definitions beyond modeled `@skip` and
  `@include`;
- scalar/enum parsing and coercion details for supplied inputs, plus result coercion;
  supplied values are still assumed type-conformant, while argument/default
  materialization is modeled;
- introspection and meta-fields;
- request errors;
- detailed execution error maps, `extensions`, error paths, error locations,
  and messages;
- response serialization details;
- async execution, resolver scheduling, resolver context, and resolver info
  metadata;
- transport and HTTP behavior;
- schema extensions and type-system extension syntax;

Validation records structural input-object and variable/input-type
compatibility, while assuming values are already coerced where scalar semantics
would matter. Execution does not produce request errors for missing/null
required variables; those cases are outside the executable model and are ruled
out by validity assumptions where needed.

## Related Documentation

- `docs/overview.md`: project structure and module dependency map.
- `docs/references.md`: GraphCoQL notes and proof strategy references.
- `README.md`: build, lint, and entry-point information.
- `conformance/graphql-js/README.md`: graphql-js fixture and oracle workflow.
