# Project Overview

`graphql-lean` is a Lean formalization of a scoped GraphQL model. It provides a
precise account of query execution and a foundation for proving properties of
query transformations, execution strategies, and static analyses.

This is a formalization workspace, not a production GraphQL server. The
[conformance summary](spec-conformance.md) describes which parts of GraphQL are
covered and which are outside the model.

## How the model fits together

The specification-facing model connects three things:

1. **Syntax:** schemas and operations describe the inputs.
2. **Validity:** separate predicates state the assumptions on those inputs.
3. **Execution:** abstract resolvers give meaning to operations and produce responses.

Raw syntax stays permissive. Validation and well-formedness supply the invariants
used by later proofs, rather than making invalid inputs impossible to represent.
Resolvers are parameters, so semantic claims can apply across data sources rather
than only to a particular database or fixture.

Project algorithms and theories build on that model. Their correctness statements
relate alternative executions, transformed queries, or analysis results back to
the specification-facing execution semantics. Each theorem has its own assumptions;
a public correctness statement is not itself a proof.

## Main areas

- **Core GraphQL:** schema and operation syntax, validity, field collection, value
  completion, null bubbling, and modeled execution errors.
  See [execution](execution.md) for the representation and specification mapping.
  [Execution-readiness checking](theories/execution-readiness.md) covers argument
  defaults and composite-output inhabitance after validation.
- **Named fragments:** fragment-aware syntax, validation, execution, and translation
  to the core operation model.
- **Alternative execution strategies:** algorithms whose behavior is compared with
  the specification-facing executor. See [algorithms](algorithms.md).
- **Query transformations and comparisons:** [normal forms](theories/normal-form.md)
  and [query inclusion](theories/query-inclusion.md) support reasoning about
  equivalence and inclusion. Query inclusion checks selected response paths;
  separate semantic bridges relate it to error-free annotated executions.
- **Static analyses:** [condition trees](theories/condition-tree.md) and
  [tree summaries](theories/tree-summary.md) support analyses such as response-size
  bounds and [static cost](theories/static-cost.md).

The project-specific theories and algorithms are not additions to the GraphQL
specification. They use the formal model as their semantic reference.

## Repository organization

Code is separated by role, with proof and test paths mirroring the public definitions:

- `GraphQL/`: public model, algorithm, and theory definitions.
- `Proofs/GraphQL/`: theorems and proof-facing helpers.
- `Tests/GraphQL/`: ordinary definition and proof regressions.
- `Tests/Conformance/`: generated or fixture-driven conformance checks.
- `Lint/`: repository tooling.

The root import files aggregate these areas. Public definitions do not depend on
proof modules. The [Lean module organization section](development.md#lean-module-organization)
describes the conventions for adding or moving code.

## Reading and contributing

Start with the [conformance summary](spec-conformance.md) for scope, then follow
the topic guides above for definitions, assumptions, and proof status. Detailed
proof arguments belong with their topics rather than in this introduction.

The [development guide](development.md) covers build, formatting, and lint commands.
The [conformance fixture guide](../conformance/graphql-js/README.md) explains the
graphql-js comparison workflow. [References](references.md) provides background
on related formalizations.
