# Spec Conformance Summary

The main model targets the
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).

This page records coverage and exclusions, not full-spec conformance or proof
completion. Representation details and specification mappings are documented in
[execution](execution.md).

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

## Conformance checks: coverage boundary

graphql-js fixtures compare the main and named-fragment models' ordered response
data and execution-error counts. They do not compare detailed errors, transport,
or asynchronous behavior, and do not establish universal correctness of the
incremental model. The [fixture guide](../conformance/graphql-js/README.md)
documents the test workflow.
