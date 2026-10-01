# Repo Agent Memory

This repo is a Lean formalization workspace for a scoped plain GraphQL fragment.

## Spec Conformance Status

Spec conformance is summarized in `docs/spec-conformance.md`.

The main model's explicit skips include:

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

## Current Model and Proof Boundaries

### Main execution

`GraphQL.Execution` is the spec-facing model. Runtime objects use opaque resolver-owned
references. Operation equivalence quantifies over resolver environments, variable values,
explicit fuel, and source values. Responses contain data and a natural-number execution
error count; `Execution.Result` models non-null bubbling. Input preparation materializes
missing defaults but assumes supplied values are already coerced and type-conformant.

### Incremental delivery

The separate `GraphQL.IncrementalDelivery` model targets the draft at `045e193`.
The specification is authoritative; GraphQL.js is a design reference, not an additional
normative source. The detailed cross-reference is in
`docs/incremental-delivery/README.md`.

Public modules separate these responsibilities:

- `Operation`: scoped inline-fragment/field syntax and incremental directives.
- `EventSource`: a generic opaque language of finite admitted and finished histories.
- `Execution`: pure finite completion, work, response mapping, and batching.
- `WorkQueueSemantics`: independent work-accounting relations and source contract.
- `Observation`: finite observations, query completion, and query-local queue conformance.
- `Correctness`: response properties, reconstruction, and public correctness statements.
- `WorkQueueImplementation`: the executable reference queue/publisher and its conformance
  and query-observation propositions; it imports Observation, not Correctness.

Keep WorkQueueSemantics, Correctness, and WorkQueueImplementation as single public
modules.
Implementation proofs alone are split into topic modules under
`Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/`.

Execution accepts `createWorkQueue : Work → WorkQueue`. The core computes initial data
and finite work independently of observation order. Work stores precomputed pure outcomes,
not suspended resolvers. `Work.combine` joins structural components without choosing a
completion order; each nested occurrence has one producer, while group ancestry and
enclosing owners supply separate dependencies. Shared tasks can have multiple owners.

`executeQuery`, `executeQueryWithFuel`, and `executeRootSelectionSet` return
`ExecutionResult`: an ordinary response when work is empty, otherwise an initial
incremental result and resumable response stream. Empty stream boundaries are nonempty
work. The finite stream hook retains a boundary at `initialCount = list.length`, but not
when the count exceeds the list. The pinned draft does not wire streaming into its list
completion algorithm; this extension is documented explicitly.

`EventSource` stores observed history and admissible/finished predicates, not a chosen
future. `ResponseEventStream.Accepts`, `next`, and `Observes` live in Observation.
Observation supplies available inputs; execution neither chooses completion order nor
drains the source. ID allocation belongs to response mapping. Work-value grouping,
work-event batching, and response batching are distinct.

The proposed `WorkQueue.Conforms` contract fills the draft's unspecified CreateWorkQueue
boundary with `Initialized`, `PrefixClosed`, `AccountsForWork`, and
`TerminationMatchesWork`. These are model contributions, not normative spec pseudocode.
Admission uses output histories and existential occurrence/failure evidence, not required
runtime graphs or ledgers. Never hide a contract gap by assuming wire lifecycle,
disjointness, successful merging, or response equivalence.

The contract applies to normalized publication owners. A shared value needs a healthy open
supporter, while its wire ID is a longest-path open contributor, possibly a different
failed
co-owner. Ordered failure cuts allow settlement before notification; licensing requires a
previously announced contributor, not necessarily one still open at settlement. Later
failure cannot retroactively cancel published producers. Publications and completion
notices require open IDs. Keep these boundaries distinct in proofs and documentation.

`queryObservation` observes the actual `executeQueryWithFuel` result; `queryOutcome`
requires a complete observation. Correctness separately assumes
`queryWorkQueueConforms` for the same constructor and the nonempty work submitted by that
query. Observations alone do not imply conformance. Invalid roots and ordinary responses
impose no law on an unused queue constructor.

The reference implementation's `State.initialize` constructs concrete state;
`createWorkQueueForSchedule work schedule` projects its replay to Execution.WorkQueue.
`Execution.initializeIncrementalResponse` shares initial-envelope construction and ID
allocation between spec `yieldIncrementalResults` and the reference initializer of the
same name. The reference initializer adds concrete queue and live-owner state. Subsequent
updates use `Execution.mapWorkEventBatch`; initial notices are not synthetic work events.
`ExecutedWork` means work produced by root completion. `schedule.ValidFor work`
packages source and executable-start premises. `ExecutedWork.initializes` derives initial
notice validity; callers of `createWorkQueueForScheduleConforms` need only executed work,
nonemptiness, and source validity, not a separate initialization premise.

`ImplementationCorrect schema operation`, witnessed by `implementationCorrect_holds`
in CursorObservation, supplies query-local conformance and actual-factory observation.
`queryScheduleMatches` hides derived work, source validity, and admitted inputs behind the
shared `replayIncrementalResponse` runner. The completeness flag covers both prefixes and
terminated outcomes. This bridge does not depend on the optional ResponseStreamCursor.
CursorCorrectness supplies reusable end-to-end results without duplicating the public
query-correctness propositions.

All 12 public query-correctness statements, reference conformance, and the query bridge
have proof witnesses. Safety and disjointness cover admitted prefixes, including errors.
ID liveness and lifecycle cover complete finite runs. Reconstruction, basic-position
coverage, and leaf-once additionally require zero counted errors. Existential finite
progress does not guarantee completion of every admitted prefix or every source.

Incremental validation, named fragments, effectful resolvers, infinite sources, host
timing/fairness, and formal refinement of the actual GraphQL.js runtime remain outside
scope. Optional nonblocking and local commutation results do not strengthen admission.
Use the topic guides for theorem maps, research boundaries, and implementation
differences,
rather than duplicating detailed proof status here.

### Normal forms and repository organization

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

## Verification

Run `lake build` and `lake lint` for whole-project verification. Both pass for the
current definitions, proofs, and regressions. Public-witness axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`, with no proof holes or added axioms.

Focused commands are in `docs/incremental-delivery/README.md#focused-checks` and
`docs/incremental-delivery/implementation.md#verification-and-limits`.

## Where To Look

- `docs/spec-conformance.md`: high-level coverage, assumptions, and exclusions only.
- `docs/execution.md`: main execution representation and specification correspondence.
- `docs/incremental-delivery/README.md`: incremental execution details, per-definition
  spec
  mapping, queue assumptions, correctness statements, and proof status.
- `docs/incremental-delivery/semantics.md`: history-based queue contract, primary-source
  research comparison, failure witnesses, and open refinement obligations.
- `docs/incremental-delivery/implementation.md`: reference queue/publisher implementation,
  GraphQL.js correspondence, conformance proof structure, and verification boundaries.
- `docs/development.md#lean-module-organization`: module organization rules for keeping
  top-level Lean files definition-only and theorem files topic-specific.
- `docs/overview.md`: durable project introduction, architecture, and topic navigation.
- `docs/theories/normal-form.md`: public normal-form statements and proof-witness map.
- `docs/theories/normal-form-uniqueness.md`: ground and complete uniqueness proof plan.
- `docs/theories/query-inclusion.md`: query-inclusion semantics, checker, and proof
  domain.
- `docs/algorithms.md`: verified non-spec algorithms.
- `docs/references.md`: GraphCoQL reference notes and proof-strategy context.
- `GraphQL/Theories/NormalForm.lean`: public normal-form definitions and
  correctness propositions.
- `GraphQL/Execution.lean`: main resolver-parametric execution model.
- `GraphQL/IncrementalDelivery.lean`: separate incremental-delivery module surface.
- `GraphQL/Validation.lean`: current operation validity assumptions.
- `Tests/GraphQL.lean`: ordinary GraphQL test aggregator.
- `Tests/Conformance.lean`: conformance test aggregator.

## Development Notes

Keep raw syntax permissive and put invariants in validation or well-formedness
predicates. Prefer small, proof-friendly definitions over feature expansion.
When changing spec scope, update `docs/spec-conformance.md`.
Keep that page coverage-only and `docs/overview.md` high-level. Put execution details,
spec mappings, and proof status in the relevant topic guide rather than duplicating
them in those summaries. Fixture commands belong in `conformance/graphql-js/README.md`.
Keep documentation a snapshot of the current design and proved results, not a development
log. Git retains superseded designs, proof plans, and per-commit progress.
For routine work on implementation proofs, change the relevant proofs/tests and keep
all implementation documentation updates in `docs/incremental-delivery/implementation.md`.
Do not update other documentation or `AGENTS.md` for normal proof progress; changes to
public definitions or contracts may require corresponding updates there.

Keep `GraphQL/` files definition-only. Put ordinary theorems in topic-specific
`Proofs/GraphQL/` modules, following `docs/development.md#lean-module-organization`.
Put ordinary tests under `Tests/GraphQL/` and conformance/generated fixture
tests under `Tests/Conformance/`; keep top-level `Tests/*.lean` files to
aggregators only.

Review workflow: do not commit before review. Prepare one reviewable slice at a
time, run the relevant checks, summarize the diff, and wait for the user to ask
for the commit. After committing, stop again for review before continuing to the
next proof or implementation slice, unless the user explicitly asks to continue
past that review boundary.
