# Repo Agent Memory

This repo is a Lean formalization workspace for a scoped plain GraphQL fragment.

## Current Priority

Spec conformance is the current priority, following
`docs/spec-conformance-plan.md`.

Current explicit skips:

- mutation,
- subscription,
- named fragment definitions and fragment spreads,
- custom directives beyond modeled `@skip` and `@include`,
- coercion, assuming values are already coerced and type-conformant,
- introspection and meta-fields,
- request errors, detailed execution error maps, response `extensions`, error
  paths, and error locations,
- response-shape analysis,
- minimization,
- federation.

The immediate proof goal is to formalize schema, operation validation,
resolver-parametric execution, and ground normal form enough to support later
semantic operation transformation algorithms.

## Current Status

`GraphQL.Execution` is the proof-facing execution model. Runtime object values
are parameterized by opaque resolver-owned refs, and operation equivalence is
stated over all resolver environments, variable values, explicit fuel values,
and source values. Execution returns a response envelope with `data` plus a
`Nat` execution-error count, and null bubbling through non-null wrappers is
modeled with `Execution.Result`.

The ground-type normalizer has no fuel parameter; it terminates by structural
descent on selection-set size while merging fields and grounding abstract
returns. Public normal-form predicates belong in top-level
`GraphQL/Theories/NormalForm.lean`; proof work belongs under
`Proofs/GraphQL/Theories/NormalForm/`,
with directive-free ground-type proof modules under
`Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/`.

The latest successful checks were:

```sh
lake build
lake lint
```

## Where To Look

- `docs/spec-conformance-plan.md`: current goals, skips, status, and proof status.
- `docs/lean-organization.md`: module organization rules for keeping
  top-level Lean files definition-only and theorem files topic-specific.
- `docs/ground-type-normal-form-proof.md`: summary of the completed
  directive-free ground-type normal form correctness proof.
- `docs/overview.md`: module map and architecture overview.
- `docs/references.md`: GraphCoQL reference notes and proof-strategy context.
- `GraphQL/Theories/NormalForm.lean`: ground normal form scaffold.
- `GraphQL/Execution.lean`: resolver-parametric execution model.
- `GraphQL/Validation.lean`: current operation validity assumptions.

## Development Notes

Keep raw syntax permissive and put invariants in validation or well-formedness
predicates. Prefer small, proof-friendly definitions over feature expansion.
When adding scope, update `docs/spec-conformance-plan.md` first.

Keep `GraphQL/` files definition-only. Put ordinary theorems in topic-specific
`Proofs/GraphQL/` modules, following `docs/lean-organization.md`.

Review workflow: do not commit before review. Prepare one reviewable slice at a
time, run the relevant checks, summarize the diff, and wait for the user to ask
for the commit. After committing, stop again for review before continuing to the
next proof or implementation slice, unless the user explicitly asks to continue
past that review boundary.
