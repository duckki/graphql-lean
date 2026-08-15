# graphql-lean

`graphql-lean` is a GraphQL formalization in Lean, based on the [GraphQL September
2025 Edition](https://spec.graphql.org/September2025/).

Compared with prior theorem-prover formalizations such as
[GraphCoQL](https://github.com/imfd/GraphCoQL), this development fills important gaps in
the formal treatment of GraphQL. Notably, it models `@skip` / `@include` directives, null
bubbling, execution errors up to error counts, and named fragments. It also includes
verified algorithmic alternatives to the spec executor and a directive-aware normalization
theory.

## Highlights

- [GraphQL/](GraphQL/) contains the public formal model of the scoped GraphQL
  2025 spec: schema syntax and well-formedness, operation syntax, validation,
  execution, named fragments, execution algorithms, and public theory
  definitions.
- [ExecutionCancelingSiblings](GraphQL/Algorithms/ExecutionCancelingSiblings.lean)
  verifies a spec-style executor that cancels sibling response positions after
  null bubbling.
- [ExecutionUngrouped](GraphQL/Algorithms/ExecutionUngrouped.lean) models a
  lightweight syntax-order execution that avoids building the collected
  field map, caches field results and retained composite sources by response
  position, and has checked preservation witnesses. Its
  [uncached specialization](GraphQL/Algorithms/ExecutionUngroupedUncached.lean)
  is also verified for resolvers that are cheap to call repeatedly.
- [ExecutionBreadth](GraphQL/Algorithms/ExecutionBreadth.lean) verifies a
  breadth-first execution model with vectorized resolver calls, inspired by
  [gmac/graphql-breadth-js](https://github.com/gmac/graphql-breadth-js),
  against the spec-facing executor.
- [NormalForm](GraphQL/Theories/NormalForm.lean) provides ground-type and complete
  normalization.
  Complete normalization supports modeled `@skip` / `@include` directives,
  unlike the earlier paper/Coq normalizers, and its canonicity theorems prove
  that semantic equivalence of operations can be reduced to comparison of normal
  forms.
- [QueryInclusion](GraphQL/Theories/QueryInclusion.lean) provides a verified,
  condition-aware decision procedure for recursive response inclusion that preserves
  resolver-call provenance.

## GraphQL Layout

The public model is rooted at [GraphQL.lean](GraphQL.lean), which imports the
definition surfaces below.

- [GraphQL/Schema.lean](GraphQL/Schema.lean): GraphQL type-system syntax, type
  references, lookup, possible-object helpers, default-value validity, and
  interface implementation compatibility helpers.
- [GraphQL/SchemaWellFormedness.lean](GraphQL/SchemaWellFormedness.lean): schema
  well-formedness predicates for the modeled fragment.
- [GraphQL/Operation.lean](GraphQL/Operation.lean): core operation syntax,
  variable definitions, selections, inline fragments, and modeled directive
  applications.
- [GraphQL/Validation.lean](GraphQL/Validation.lean): operation validation
  predicates, including field validity, argument validity, variable-use checks,
  selection-shape checks, fragment applicability, and merge compatibility.
- [GraphQL/Execution.lean](GraphQL/Execution.lean): resolver-parametric
  spec-compliant execution with operation-variable defaults, schema-derived resolver
  argument maps, field collection, completion, null bubbling, and response envelopes
  containing data plus execution-error counts.
- [GraphQL/NamedFragment/](GraphQL/NamedFragment/): fragment-aware operation
  syntax, validation, execution, translation, and inlining support.
- [GraphQL/Algorithms/](GraphQL/Algorithms/): non-spec execution algorithms,
  including sibling-canceling execution, source-caching and uncached ungrouped
  execution, and breadth-first execution.
- [GraphQL/Theories/](GraphQL/Theories/): public project theories, currently
  including normal forms, annotated execution, selection-condition extraction, and
  query inclusion.

Proof witnesses are under [Proofs/](Proofs/). Ordinary tests are under
[Tests/GraphQL/](Tests/GraphQL/), and generated or fixture-driven conformance
tests are under [Tests/Conformance/](Tests/Conformance/).

## Build

```sh
lake build
```

## Documentation

- [docs/overview.md](docs/overview.md): module map and architecture overview.
- [docs/spec-conformance.md](docs/spec-conformance.md): implemented
  spec-conformance scope and out-of-scope boundaries.
- [docs/algorithms.md](docs/algorithms.md): algorithmic alternatives to the
  spec-facing executor and their proof status.
- [docs/theories/query-inclusion.md](docs/theories/query-inclusion.md): query-inclusion
  semantics, correctness domain, checker design, and proof structure.
- [docs/theories/normal-form.md](docs/theories/normal-form.md): normal-form definitions and
  preservation theorems.
- [docs/theories/normal-form-uniqueness.md](docs/theories/normal-form-uniqueness.md): canonicity
  and semantic-equivalence results for normal forms.
- [docs/development.md](docs/development.md): developer guide.
