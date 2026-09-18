# Development

This document records development commands and code organization conventions for
the Lean workspace.

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
lake exe fmt --recursive *.lean GraphQL Proofs Tests Benchmarks Lint
```

Check formatting without rewriting files:

```sh
lake exe fmt --check --recursive *.lean GraphQL Proofs Tests Benchmarks Lint
```

To format only Lean files changed from `origin/main`, use:

```sh
scripts/fmt-changed.sh
```

The command refuses staged, unstaged, or untracked Lean files by default. Include them
explicitly with `--allow-dirty`; add `--check` to check rather than rewrite, or use
`--base REF` to choose another comparison ref.

## Lean module organization

Separate public definitions, proofs, tests, and tooling by role. Keep root modules
thin: they aggregate the corresponding modules rather than introduce definitions
or proofs of their own.

### Definitions and proofs

Public definition modules contain syntax, structures, predicates, executable
functions, and correctness propositions. Keep these surfaces readable independently
of their proofs. Ordinary theorems and proof-facing helper definitions belong in
separate proof modules organized around the definitions they support.

Termination material attached to a recursive definition may stay with that
definition. Standalone termination helper theorems are the only exception to the
definition-only rule; keep them in a clearly marked final section containing no
other theorems.

### Topics and dependencies

Name modules for their domain concepts or proof roles, not generic collections of
lemmas, facts, utilities, or miscellaneous helpers. Split large proof developments
at logical boundaries rather than by line count. Keep local facts together, then
build higher-level results from explicit prerequisite layers.

Definition modules must not import proof modules. Proof modules may import the
definitions they support and prerequisite proofs; imports of other definition
areas should reflect an explicit connection established by the theorem. Prefer
explicit imports at layer boundaries over reliance on long transitive chains.

When moving a theorem, preserve its declaration name unless there is a separate
reason to rename it. Relocation alone should not require downstream proof scripts
to change the names they use.

### Tests

Organize ordinary tests by the definition or proof topic they exercise, mirroring
those areas where practical. Keep generated and fixture-driven conformance tests
separate, grouped by source and feature. Test roots should remain aggregators;
introduce a new root only for a durable major test family.

## Conformance Fixtures

Fixture generation and graphql-js oracle commands are documented in the
[conformance fixture guide](../conformance/graphql-js/README.md). The
[conformance summary](spec-conformance.md) records coverage; the
[incremental-delivery guide](incremental-delivery.md#focused-checks) records its
focused verification commands.
