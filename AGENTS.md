# Talk branch instructions

This branch is a focused definitions, proof-scaffold, and tests project for a one-hour talk on GraphQL
query inclusion. Keep the scope focused on `GraphQL.Theories.QueryInclusion`,
`GraphQL.Theories.ResponsePath`, and their dependencies.

## Exercise and model

- The executable checker is `GraphQL.QueryInclusion.includesBoolReference`.
- The proof exercise is `IncludesBoolReferenceSound`. Preserve the statement, checker,
  specification, schema well-formedness premise, and both operation-validity premises.
- `IncludesBoolReferenceComplete` is also a proposition without a proof witness in this
  baseline. Do not claim it is proved.
- Keep raw syntax permissive and express invariants in validation or well-formedness.
- The retained executor uses opaque resolver references, already-coerced inputs,
  non-null bubbling, and execution error counts. Named fragments, incremental delivery,
  execution-semantic inclusion, other execution algorithms, and unrelated theories are
  outside this branch's scope.

## Organization and checks

Public definitions and correctness propositions belong under `GraphQL/`. Put ordinary
proof theorems under `Proofs/GraphQL/` when adding an exercise solution; do not put them
in public definition modules. Termination helper theorems may remain in explicitly
marked sections beside recursive definitions. Ordinary tests belong under
`Tests/GraphQL/`; root modules stay thin aggregators.

Run `lake build`, `lake build Tests`, and `lake lint`; `make all` also checks formatting
of changed Lean files. See `docs/development.md` for commands and
`docs/theories/query-inclusion.md` for the contract and proof boundaries.

## Review workflow

Do not commit before review. Prepare a reviewable slice, run relevant checks, summarize
the diff, and wait for the user to request the commit. After committing, stop again for
review before continuing to the next slice unless explicitly authorized to continue.
