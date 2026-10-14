# GraphQL query inclusion in Lean

This talk and exercise branch keeps the definitions and regression tests needed for
query inclusion. It uses `GraphQL.QueryInclusion.includesBoolReference`, an exhaustive
Boolean checker. A focused proof scaffold supports the hands-on exercise. Unrelated
GraphQL theories, benchmarks, and conformance tooling remain outside this branch.

## Reading order

Start with the [overview](docs/overview.md) for the model's structure and
[execution](docs/execution.md) for field collection, resolver values, completion, and
error handling. The [conformance summary](docs/spec-conformance.md) describes the scoped
GraphQL fragment; [references](docs/references.md) gives related formalization background.

1. [QueryInclusion](GraphQL/Theories/QueryInclusion.lean): condition-variable extraction,
   selected-path specification, reference implementation, and correctness statements.
2. [ResponsePath](GraphQL/Theories/ResponsePath.lean): Boolean assignments and the selected
   paths compared by the specification.

These are the only modules under `GraphQL/Theories/`. Schema, operation, validation,
schema well-formedness, and execution definitions support the checker. The model is a
scoped fragment of GraphQL: fields, inline fragments, and `@skip` / `@include`, with
already-coerced inputs and opaque resolver objects. Named fragments, incremental
execution, mutations, subscriptions, and execution-semantic inclusion are outside this
talk branch's scope.

## Proof exercise

Prove this statement without changing the specification, checker, or assumptions:

```lean
import Proofs.GraphQL.Theories.QueryInclusion.Support

namespace GraphQL.QueryInclusion

theorem includesBoolReference_sound {schema : Schema} {left right : Operation}
    : IncludesBoolReferenceSound schema left right := by
  -- Supply the proof here.
```

`IncludesBoolReferenceSound` says that, for a well-formed schema and valid left and right
operations, checker acceptance implies `includes schema left right`. Inclusion is
oriented from right to left: every selected right-hand path must also be selected on the
left, and shared variable definitions must agree syntactically.

Put the completed theorem in `Proofs/GraphQL/Theories/QueryInclusion/Soundness.lean`,
close the namespace, and check it with `lake env lean` after `lake build`. The prepared
exercise baseline contains the target propositions and proved supporting lemmas, without
final theorem witnesses or `sorry` placeholders. `IncludesBoolReferenceComplete` is an
optional stretch exercise. The supporting lemmas are exposed by
[`QueryInclusion.Support`](Proofs/GraphQL/Theories/QueryInclusion/Support.lean).

## Checks

```sh
lake build
lake build Tests
lake lint
./scripts/fmt-changed.sh --allow-dirty --check
```

The tests check concrete behavior; they do not replace the exercise's universal proof.
See [query inclusion](docs/theories/query-inclusion.md) for the contract and boundaries,
and [development](docs/development.md) for tooling and module conventions.
