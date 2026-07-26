# Lean Module Organization

This repo separates definition surfaces from proof modules. The goal is to keep
the core GraphQL model easy to read while letting proof files grow by topic.

## Top-Level Files

`GraphQL/` files should contain public definitions only:

- syntax types,
- structures,
- inductive predicates,
- executable functions,
- public propositions and predicates,
- notation or small definition-facing helpers.

Do not add ordinary `theorem` or `lemma` declarations to top-level files.
Theorems should live under `Proofs/GraphQL/`, in a path named for the definition
area they support.

Examples:

- Definitions for validation belong in `GraphQL/Validation.lean`.
- Proofs about validation belong under `Proofs/GraphQL/Validation/`.
- Definitions for execution belong in `GraphQL/Execution.lean`.
- Proofs about execution belong under `Proofs/GraphQL/Execution/`.
- Public project-theory definitions belong under `GraphQL/Theories/`.
- Proofs about project theory belong under `Proofs/GraphQL/Theories/`.

## Termination Proof Exception

Termination material for recursive definitions may remain in the same file as
the definition when Lean requires it to be attached to the recursive block.

Standalone termination helper theorems are the only allowed top-level theorem
exception. Put them at the bottom of the file, below this exact style of banner:

```lean
/-! ============================================================
Termination theorems only
============================================================ -/
```

No non-termination theorem should appear below that banner.

## Proof Module Names

Proof modules should be named by topic. Avoid generic file names such as:

- `Theorems.lean`
- `Lemmas.lean`
- `Facts.lean`
- `Utils.lean`

Prefer names that say what the proofs are about:

- `Proofs/GraphQL/Execution/FieldCollection.lean`
- `Proofs/GraphQL/Validation/SelectionValidity.lean`
- `Proofs/GraphQL/Validation/FieldMerge.lean`
- `Proofs/GraphQL/SchemaWellFormedness/PossibleTypes.lean`
- `Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/FieldSemantics.lean`

If a file name starts to need "misc", "helper", or "common", split by the
nearest domain concept instead.

## Import Shape

Definition modules should not import proof modules. This keeps the core model
usable without pulling in large proof dependencies.

Proof modules may import:

- the definition module they prove facts about,
- earlier proof modules for prerequisite facts,
- downstream definition modules only when the theorem topic explicitly bridges
  those areas.

The root import surface `GraphQL.lean` imports public definition modules only.
The root import surface `Proofs.lean` imports theorem/proof-facing modules.

## Normal Form Proofs

Ground-type normalization proofs should stay under
`Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/` and be split by
the proof role:

- directive-freeness preservation,
- schema and possible-type facts,
- validation transport,
- field-merge transport,
- lookup validity,
- semantic readiness,
- executable field collection,
- field execution semantics,
- abstract return semantics,
- selection-set semantic preservation,
- operation/store semantic lifts,
- normality and non-redundancy.

The public `GraphQL/Theories/NormalForm.lean` file should keep only the
normal-form definitions, predicates, normalizer functions, and public
correctness propositions.

## Layered Proof Modules

For large proof areas, split modules by logical proof layer rather than by line
count. The base file should hold the core local predicates, low-level response
or collection facts, and the first theorem layer that directly proves facts
about those predicates.

Use submodules for named proof roles:

- `Validity.lean`: validation assumptions transported into proof-facing
  invariants.
- `.../State.lean`: state witness records and constructors.
- `.../Executable.lean`: executable-field or executable-group wrappers around
  lower-level semantic facts.
- `.../FlatSpec.lean`: conversion from execution witnesses into flat-spec
  equivalence predicates.
- `.../Query.lean`: root-selection, `executeQueryWithFuel`, and `executeQuery`
  wrapper theorems.

Prefer explicit imports at these layer boundaries. Do not rely on long
transitive imports when a module directly mentions a proof layer's declarations.

The ungrouped execution equivalence modules under
`Proofs/GraphQL/Algorithms/ExecutionUngrouped/Equivalence/` follow this pattern:

- `AppendSelection.lean` keeps response/key and one-step append execution facts,
  while `AppendSelection/Validity.lean` and `AppendSelection/State.lean` hold
  validation and append-state witnesses.
- `AppendSelection/SingleFieldGroup.lean` keeps complete-value child-state
  lemmas, while `SingleFieldGroup/Executable.lean` and
  `SingleFieldGroup/Query.lean` lift them to executable-group and query
  wrappers.
- `FieldGroup/AppendSteps.lean` keeps append-step and append-plan machinery,
  while `AppendSteps/FlatSpec.lean` and `AppendSteps/Query.lean` perform the
  flat-spec and query lifts.

## Refactor Rule

When moving a theorem, preserve its declaration name unless there is a specific
reason to rename it. Module moves should not make downstream proof scripts pay
for both a relocation and a rename at the same time.
