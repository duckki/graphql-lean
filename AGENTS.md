# Repo Agent Memory

This repo is a Lean formalization workspace for a scoped plain GraphQL fragment.

## Spec Conformance Status

Spec conformance is summarized in `docs/spec-conformance.md`.

Explicit skips include:

- mutation,
- subscription,
- custom directives beyond modeled `@skip` and `@include`,
- coercion, assuming values are already coerced and type-conformant,
- introspection and meta-fields,
- request errors, detailed execution error maps, response `extensions`, error
  paths, and error locations,
- response-shape analysis,
- minimization,
- federation.

## Current Status

`GraphQL.Execution` is the spec-facing execution model used by proof modules.
Runtime object values are parameterized by opaque resolver-owned refs, and
operation equivalence is stated over all resolver environments, variable
values, explicit fuel values, and source values. Execution returns a response
envelope with `data` plus a `Nat` execution-error count, and null bubbling
through non-null wrappers is modeled with `Execution.Result`.

The ground-type normalizer has no fuel parameter; it terminates by structural
descent on selection-set size while merging fields and grounding abstract
returns. Public normal-form predicates belong in top-level
`GraphQL/Theories/NormalForm.lean`; proof work belongs under
`Proofs/GraphQL/Theories/NormalForm/`,
with directive-free ground-type proof modules under
`Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/`.

Repo organization is:

- `GraphQL/`: public GraphQL and project-theory definitions only.
- `GraphQL/Theories/`: public project-theory definitions such as normal forms.
- `Proofs/GraphQL/`: theorem modules and proof-facing helper definitions,
  mirroring the public definition areas.
- `Tests/GraphQL/`: ordinary tests, mirroring the `GraphQL`/`Proofs` layout.
- `Tests/Conformance/`: generated or fixture-driven conformance tests.
- `Lint/`: project tooling such as import-closure checks.

The latest successful checks were:

```sh
lake build
lake lint
```

## Where To Look

- `docs/spec-conformance.md`: implemented spec-conformance scope,
  out-of-scope boundaries, module summary, and conformance fixture workflow.
- `docs/lean-organization.md`: module organization rules for keeping
  top-level Lean files definition-only and theorem files topic-specific.
- `docs/overview.md`: module map and architecture overview.
- `docs/theories/normal-form.md`: public normal-form statements and proof-witness map.
- `docs/theories/normal-form-uniqueness.md`: ground and complete uniqueness proof plan.
- `docs/theories/query-inclusion.md`: query-inclusion semantics, checker, and proof domain.
- `docs/algorithms.md`: verified non-spec algorithms.
- `docs/references.md`: GraphCoQL reference notes and proof-strategy context.
- `GraphQL/Theories/NormalForm.lean`: public normal-form definitions and
  correctness propositions.
- `GraphQL/Execution.lean`: resolver-parametric execution model.
- `GraphQL/Validation.lean`: current operation validity assumptions.
- `Tests/GraphQL.lean`: ordinary GraphQL test aggregator.
- `Tests/Conformance.lean`: conformance test aggregator.

## Development Notes

Keep raw syntax permissive and put invariants in validation or well-formedness
predicates. Prefer small, proof-friendly definitions over feature expansion.
When changing spec scope, update `docs/spec-conformance.md`.

Keep `GraphQL/` files definition-only. Put ordinary theorems in topic-specific
`Proofs/GraphQL/` modules, following `docs/lean-organization.md`.
Put ordinary tests under `Tests/GraphQL/` and conformance/generated fixture
tests under `Tests/Conformance/`; keep top-level `Tests/*.lean` files to
aggregators only.

Review workflow: do not commit before review. Prepare one reviewable slice at a
time, run the relevant checks, summarize the diff, and wait for the user to ask
for the commit. After committing, stop again for review before continuing to the
next proof or implementation slice, unless the user explicitly asks to continue
past that review boundary.
