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

This talk branch focuses on query inclusion: a syntactic relation between selected
response paths, together with an exhaustive reference checker and supporting proofs.
The executor remains as background for the field-collection semantics used by those
paths. Each correctness statement has its own assumptions; defining a proposition
is not itself a proof.

## Main areas

- **Core GraphQL:** schema and operation syntax, validity, field collection, value
  completion, null bubbling, and counted execution errors.
  See [execution](execution.md) for the representation and specification mapping.
- **Selected response paths:** `GraphQL.Theories.ResponsePath` describes the fields
  selected under a Boolean assignment, including runtime object types, aliases,
  resolver-call identity, arguments, and output types.
- **Query inclusion:** `GraphQL.Theories.QueryInclusion` compares those footprints
  under every relevant Boolean assignment. Its reference checker enumerates assignments
  and possible runtime types. See [query inclusion](theories/query-inclusion.md) for
  the contract, algorithm, assumptions, and proof exercise.
- **Proof scaffold:** supporting lemmas connect Boolean enumeration, field collection,
  and recursive checker results to the selected-path specification.

Query inclusion is a project theory built on the GraphQL model, not an additional
GraphQL specification rule. The selected-path relation does not by itself establish
inclusion of executed responses or a production cache-reuse guarantee.

## Repository organization

Code is separated by role, with proof and test paths mirroring the public definitions:

- `GraphQL/`: public model and query-inclusion definitions.
- `Proofs/GraphQL/`: theorems and proof-facing helpers.
- `Tests/GraphQL/`: ordinary definition and proof regressions.
- `Lint/`: repository tooling.

The root import files aggregate these areas. Public definitions do not depend on
proof modules. The [Lean module organization section](development.md#lean-module-organization)
describes the conventions for adding or moving code.

## Reading and contributing

Start with the [conformance summary](spec-conformance.md) for scope, then follow
the topic guides above for definitions, assumptions, and proof status. Detailed
proof arguments belong with their topics rather than in this introduction.

The [development guide](development.md) covers build, formatting, and lint commands.
[References](references.md) provides background on related formalizations, particularly
GraphCoQL and its separation of syntax, validation, and execution.
