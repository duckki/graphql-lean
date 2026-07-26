# graphql-lean

Lean models for GraphQL.

Canonical GraphQL specification reference:
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).

For the project structure, dependency diagram, and module overview, see
[docs/overview.md](docs/overview.md).

For the current spec-conformance scope and proof plan, see
[docs/spec-conformance-plan.md](docs/spec-conformance-plan.md).

For project-specific normal forms and verified algorithms, see
[docs/normal-form.md](docs/normal-form.md) and
[docs/algorithms.md](docs/algorithms.md).

## Build

Build all Lean targets:

```sh
lake build
```

Run linting:

```sh
lake lint
```

Check that every tracked Lean file is reachable from the public roots:

```sh
lake exe import-closure
```

This package uses LeanFmt from
[duckki/LeanFmt](https://github.com/duckki/LeanFmt) as a Lake dependency.

Format all Lean sources:

```sh
lake exe fmt --recursive *.lean GraphQL Proofs Tests Lint
```

Check formatting without rewriting files:

```sh
lake exe fmt --check --recursive *.lean GraphQL Proofs Tests Lint
```

The lint target runs Lean's built-in linters with documentation warnings disabled.
It also enforces project-local community-style checks inspired by common
Mathlib/CSLib practice: lines at 100 columns except URLs, no trailing
whitespace or tabs, no unscoped diagnostic/resource `set_option`, no bare
`open Classical`, no lambda or dollar syntax, no double underscores in
declaration names, a 1500-line soft file limit, and no tracked Lean files
outside the transitive import closure of `GraphQL`, `Proofs`, `Tests`, `Lint`,
and `Lint.ImportClosureMain`.

The main top-level libraries are:

- `GraphQL`
- `Proofs`
- `Tests`
