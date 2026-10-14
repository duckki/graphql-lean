# Development

This document records development commands and code organization conventions for
the Lean workspace.

## Build

Build the public definitions and proofs (the default Lake targets):

```sh
lake build
```

Tests are separate from the default build. Run the retained regression tests:

```sh
lake build Tests
```

These tests are checked during Lean compilation; there is no separate runtime test
runner. Build `Tests` explicitly when verifying the exercise branch.

The Makefile provides the same separation:

| Command | Checks |
| --- | --- |
| `make build` | Definitions and proofs |
| `make test` | All tests and their dependencies |
| `make check` | Lint and formatting of changed Lean files |
| `make all` | Build, tests, and checks, in order |

`make fmt` formats changed Lean files, then builds and lints definitions and proofs;
it does not run tests. Makefile targets run sequentially even when invoked with `-j`,
so Lake processes do not build shared artifacts concurrently.

## Lint

Run linting:

```sh
lake lint
```

The lint target first builds definitions and proofs, not tests. It runs Lean's built-in
linters with documentation warnings disabled on the root modules and immediate Lean
files under `GraphQL/`,
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
those areas where practical. Keep test roots as aggregators. This branch retains
query-inclusion regressions under `Tests/GraphQL/`.

### Exercise solutions

The `Proofs` library supplies the query-inclusion supporting lemmas. Final exercise
witnesses belong in `Proofs/GraphQL/Theories/QueryInclusion/`. After adding a solution,
first build its module explicitly, then import it from `Proofs.lean` to include it
in regular builds and the tracked import-closure check.

Keep the checker, specification, correctness propositions, and their assumptions
unchanged during the exercise. A solution must contain no residual `sorry`/`admit`
and introduce no axioms. Inspect its transitive dependencies with `#print axioms`.

## Review

Do not commit before user review. Prepare a reviewable slice, run relevant checks,
summarize the diff, and wait for the user to request a commit. After committing, stop
again for review before starting another slice unless explicitly authorized to continue.
