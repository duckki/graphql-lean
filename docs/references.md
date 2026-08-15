# References

This file records external GraphQL formalization references for the Lean development.

## IBM GraphQL Cost Directives

- Specification: <https://ibm.github.io/graphql-specs/cost-spec.html>
- Status used here: working draft for `@cost`, `@listSize`, Static Query Analysis,
  and Query Response Analysis.

`GraphQL.Theories.TreeSummary.StaticCost` follows this specification's separate type
and field costs, default weights, signed input adjustments, abstract-type maximum, and
list-size precedence. The Lean model uses integral weights and requires a configured
finite fallback where the IBM specification would leave a list unbounded. See
[`static-cost.md`](theories/static-cost.md) for the exact scoped boundary.

## GraphCoQL

- Repository: <https://github.com/imfd/GraphCoQL>
- Paper: "A Mechanized Formalization of GraphQL", CPP 2020, Tomas Diaz, Federico Olmedo, and Eric Tanter.
- Paper page: <https://popl20.sigplan.org/details/CPP-2020-papers/12/A-Mechanized-Formalization-of-GraphQL>
- PDF: <https://users.dcc.uchile.cl/~folmedo/pubs/2020.CPP.pdf>
- Language/toolchain: Coq 8.9.1, Equations 1.2+8.9, Mathematical Components 1.9.0, Ssreflect. GitHub now labels `.v` files as Rocq Prover.
- Reviewed source revision: GitHub `master` tree SHA `681edcdcdf982151f4d1f74bb2a42f15b527317c`.

GraphCoQL is the closest known mechanized reference for this project. It formalizes a substantial executable fragment of the June 2018 GraphQL specification over a graph data model, rather than modeling execution by arbitrary host-language resolvers. That choice makes query semantics concrete enough to prove validation, normalization, and semantic-preservation results.

## Source Structure

GraphCoQL separates executable definitions from proof-heavy theory files:

- `lib/`: local helpers for quoted strings, sequences, tactics, and arithmetic proof automation.
- `src/Value.v`: scalar and list values used in arguments, node properties, and responses.
- `src/Schema.v`: core schema AST: names, named/list type references, field arguments, fields, scalar/object/interface/union/enum definitions, and schema root query type.
- `src/SchemaAux.v`: schema lookup and classification helpers.
- `src/SchemaWellFormedness.v`: boolean schema well-formedness predicates and `wfGraphQLSchema`, a schema bundled with a proof of well-formedness.
- `src/Graph.v`: graph data model with typed nodes, labeled properties, labeled edges, and a root node.
- `src/GraphConformance.v`: graph conformance to a well-formed schema, parameterized by scalar validation.
- `src/Query.v`: query AST: field selections, aliased fields, nested fields, nested aliased fields, inline fragments, optional query name, and selection set.
- `src/QueryAux.v`: selection sizes, response names, filtering, merging, and selection helper functions.
- `src/QueryConformance.v`: query validation against a schema, including
  argument conformance, selection consistency, field compatibility, and field
  merging/renaming consistency.
- `src/QueryNormalForm.v`: ground-typed normal form, non-redundancy, and query normalization.
- `src/Response.v`: response values and GraphQL responses.
- `src/QuerySemantics.v`: executable query semantics and simplified semantics for normalized queries.
- `src/theory/*.v`: lemmas for schema, graph, query auxiliary functions, conformance, normal form, and semantics.
- `src/examples/*.v`: Hartig/Perez, GraphQL specification validation examples, GraphQL.js Star Wars examples, GoodBois, and other examples.

The `_CoqProject` build order is a useful dependency map: values and schema first, then schema well-formedness, query syntax and query helpers, query conformance and normal form, graph and graph conformance, response, semantics, then examples.

## Supported GraphQL Fragment

GraphCoQL supports:

- query operations,
- schema definitions,
- scalar, object, interface, union, enum, and list types,
- fields, arguments, aliases, nested selections, and inline fragments,
- type-system validation and query validation,
- graph data conformance,
- query execution over a graph model,
- ground-typed normal form and normalization,
- examples drawn from Hartig/Perez, the GraphQL specification, and GraphQL.js.

GraphCoQL intentionally does not support, at least in the documented version:

- mutation or subscription,
- named fragment spreads,
- variables,
- directives,
- input object types,
- non-null types,
- descriptions,
- directive definitions,
- introspection,
- execution errors.

These exclusions are important for fidelity. When this Lean development adds a feature GraphCoQL skipped, it should be documented as an intentional extension, not assumed to be covered by the existing reference proof strategy.

## Modeling Choices To Learn From

GraphCoQL keeps raw syntax separate from well-formed objects. For schemas, `graphQLSchema` is just data, while `wfGraphQLSchema` packages a schema with a boolean well-formedness proof. This is a good pattern to mirror in Lean: keep syntax constructors permissive, then define validation predicates and bundled validated structures where proofs need invariants.

The schema model treats type references as either `NamedType name` or `ListType ty`. Non-null is absent. The schema type definitions are scalar, object with implemented interfaces and fields, interface with fields, union with members, and enum with members.

The query AST avoids a mutually inductive `Selection`/`SelectionSet`; a selection set is a sequence/list of selections. The selection constructors distinguish leaf fields, aliased leaf fields, nested fields, aliased nested fields, and inline fragments. This makes recursion and executable functions direct, but requires custom induction principles and explicit size measures for nested recursive functions.

Validation is mostly boolean and executable. It decomposes into:

- argument conformance against field argument definitions,
- per-selection consistency in a type scope,
- compatibility of same-response-name selections,
- renaming consistency for fields that may merge,
- top-level selection-set conformance under the query root type.

Execution follows GraphQL's selection execution shape but targets a graph model:

- leaf fields read node properties by a label made from field name and arguments,
- nested fields traverse graph edges with the same label structure,
- list return types map over all matching neighbors,
- object return types use the first matching neighbor,
- inline fragments execute only when the fragment type applies,
- repeated fields with the same response name are collected/merged by helper functions,
- missing fields or invalid scalar completion currently collapse to null or skip behavior rather than a modeled error channel.

GraphCoQL also defines a simplified semantics for normalized queries. The important theorem direction for future Lean work is not just "normalization produces normal form", but "normalization preserves query semantics".

## Normal Form Relevance

GraphCoQL's normal form work is the most relevant bridge to this repo's
operation-transformation goals.

Ground-typed normal form specializes selections under abstract types into concrete object-type cases. Non-redundancy removes duplicate response names and duplicate inline fragments. Normalization performs two operations:

- merging repeated fields with the same response name, using selection-set collection similar to GraphQL `CollectFields` and `MergeSelectionSets`,
- grounding abstract object/interface/union contexts by wrapping or lifting selections under concrete object-type inline fragments.

For this Lean project, GraphCoQL suggests a proof ladder:

1. Define syntax and schema-independent structural measures.
2. Define schema lookup and possible-type semantics for object/interface/union types.
3. Define validation as executable booleans or propositions, with explicit links between both if both are needed.
4. Define response shape and concrete execution semantics separately.
5. Define normalization candidates using structural measures.
6. Prove generated candidates are valid or preserve validation assumptions.
7. Prove semantic preservation.

## Lean Porting Notes

Lean does not need to copy GraphCoQL's Coq-specific encodings. In particular:

- MathComp `seq`/`eqType` patterns can usually become Lean `List`, `BEq`, `DecidableEq`, and explicit finite lookup functions.
- Coq `Record`-with-boolean-proof wrappers translate naturally to Lean structures with proof fields, or to predicates when bundling would add friction.
- Equations-based recursive definitions can become structurally recursive functions when possible, or well-founded recursion using explicit size measures when selection-list recursion recurses through filtered, merged, or appended lists.
- GraphCoQL's custom induction principle for selections is a warning sign: nested lists inside an inductive selection type will need carefully chosen recursors or helper lemmas in Lean too.
- Keep executable booleans close to their specification predicates when
  practical. If the Lean development prefers `Prop` validation first, add
  boolean decision procedures only when needed for examples.

## Fidelity Targets For This Repo

Use GraphCoQL as the baseline for plain GraphQL fidelity:

- model the same core schema categories,
- keep schema well-formedness separate from raw schema syntax,
- support possible-object semantics for abstract types,
- validate field selection, argument names/types, leaf/non-leaf selection shape, inline fragment applicability, and field merge compatibility,
- define execution semantics precisely enough to state preservation theorems,
- include examples analogous to Hartig/Perez, GraphQL spec validation examples, and GraphQL.js Star Wars queries,
- state unsupported features explicitly whenever a module only covers the GraphCoQL fragment.

GraphCoQL should not be treated as the final target. It is a strong lower bound
for the plain GraphQL layer. This project intentionally keeps named fragment
definitions and fragment spreads out of scope, matching GraphCoQL's query
language boundary and avoiding a separate fragment-expansion operation layer.
Other extensions, such as directives, non-null types, variables, input objects,
and counted execution errors, are intentional departures from GraphCoQL's
smaller fragment and should stay documented with their Lean-specific proof
invariants.
