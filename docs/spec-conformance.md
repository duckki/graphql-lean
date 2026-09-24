# Spec Conformance Summary

The main model targets the
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).
A separate incremental-delivery model targets
[PR #1110, revision 045e193](https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec).

This page records coverage and exclusions, not full-spec conformance or proof
completion. Representation details and specification mappings are documented in
[execution](execution.md) and [incremental delivery](incremental-delivery.md).

## Main model: covered

- **Schema and types:** objects, interfaces, unions, enums, scalars, input objects,
  lists, and non-null types; schema well-formedness for names, members, references,
  defaults, input-object cycles, root types, and interface implementation.
- **Query operations:** fields, aliases, arguments, variables and defaults, inline
  fragments, runtime type conditions, and `@skip` / `@include`.
- **Operation validation:** field and argument validity, required arguments,
  variable uses and input-type compatibility, selection shape and non-emptiness,
  fragment applicability, and same-response-name merge compatibility.
- **Named fragments:** a separate fragment-aware layer with syntax, validation,
  execution, and inlining.
- **Input preparation:** operation-variable defaults, argument materialization,
  schema argument defaults, and nested input-object defaults.
- **Execution:** resolver-parametric field collection and grouped execution,
  nullable/non-null/list completion, null bubbling, ordered response data, and
  execution-error counts.

## Main model: assumptions and exclusions

Input values are assumed already coerced and type-conformant where scalar
semantics matter. Default materialization is covered; full input coercion and
request-error handling are not. Execution is a finite, pure model with bounded
recursion. Errors are represented by counts rather than detailed error objects.

Not covered:

- Mutation and subscription execution.
- Custom directives and directive definitions beyond the modeled built-ins.
- Scalar/enum parsing and coercion details, including result coercion.
- Introspection and meta-fields.
- Request errors, detailed execution errors, messages, paths, locations, and
  response `extensions`.
- Response serialization, transport, and HTTP behavior.
- Asynchronous resolver effects, host scheduling, resolver context, and resolver
  information metadata.
- Schema extensions and type-system extension syntax.

## Incremental-delivery draft: covered

The separate draft model shares the main schema, input, resolver, and response
abstractions. It covers:

- Inline-fragment `@defer`, field `@stream`, directive conditions and labels,
  aliases, runtime type conditions, and overlapping deferred selections.
- Deferred field grouping and shared work, initial list prefixes, subsequent
  streamed items, and zero-item stream lifecycles at exhausted initial boundaries.
- Initial and subsequent responses, pending IDs, patches, completion notices,
  batching, counted errors, and modeled failure/cancellation.
- Alternative finite work schedules, interrupted observations, and completed runs,
  under an explicit model-supplied scheduler contract.

The draft leaves scheduler behavior underspecified. The additional scheduler
contract is a proposed model contribution, not a claim of literal specification
coverage.

## Incremental-delivery draft: assumptions and exclusions

The main model's exclusions also apply. In addition:

- Incremental validation and named-fragment delivery are not implemented.
- Directive placement/types, non-repeatability, literal unique labels, and
  non-overlapping streamed field selections are assumed valid.
- Stream execution includes a model extension for steps absent from the pinned draft.
- Effectful resolvers, infinite sources, real-time availability, fairness, host
  future termination, and external transport cancellation are not modeled.
- Optional coalescing of later updates into the initial response is not modeled.
- Optional ignoring of active incremental directives is not modeled.

## Conformance checks: coverage boundary

graphql-js fixtures compare the main and named-fragment models' ordered response
data and execution-error counts. They do not compare detailed errors, transport,
or asynchronous behavior, and do not establish universal correctness of the
incremental model. The [fixture guide](../conformance/graphql-js/README.md)
documents the test workflow.
