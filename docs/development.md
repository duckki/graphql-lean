# Development

This document records local development commands for the Lean workspace.

## Build

Build all Lean targets:

```sh
lake build
```

## Lint

Run linting:

```sh
lake lint
```

The lint target runs Lean's built-in linters with documentation warnings
disabled on the root modules and immediate Lean files under `GraphQL/`,
`Proofs/`, and `Lint/`. The same files receive project-local community-style
checks inspired by common Mathlib/CSLib practice: lines at 100 columns except
URLs, no trailing whitespace or tabs, no unscoped diagnostic/resource
`set_option`, no bare `open Classical`, no lambda or dollar syntax, no double
underscores in declaration names, and a 1500-line soft file limit.

The import-closure pass separately checks all tracked Lean files recursively.
They must be reachable from [GraphQL](../GraphQL), [Proofs](../Proofs),
[Tests](../Tests), [Lint](../Lint), or
[Lint.ImportClosureMain](../Lint/ImportClosureMain.lean).

Check that every tracked Lean file is reachable from the public roots:

```sh
lake exe import-closure
```

## Formatting

This package uses leanfmt from
[duckki/leanfmt](https://github.com/duckki/leanfmt) as a Lake dependency.

Format all Lean sources:

```sh
lake exe fmt --recursive *.lean GraphQL Proofs Tests Lint
```

Check formatting without rewriting files:

```sh
lake exe fmt --check --recursive *.lean GraphQL Proofs Tests Lint
```

## Lean Roots

The main top-level Lean roots are:

- [GraphQL](../GraphQL)
- [Proofs](../Proofs)
- [Tests](../Tests)
- [Lint](../Lint)
