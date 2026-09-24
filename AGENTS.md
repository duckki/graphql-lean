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

## Current Status

`GraphQL.Execution` is the spec-facing execution model used by proof modules.
Runtime object values are parameterized by opaque resolver-owned refs, and
operation equivalence is stated over all resolver environments, variable
values, explicit fuel values, and source values. Execution returns a response
envelope with `data` plus a `Nat` execution-error count, and null bubbling
through non-null wrappers is modeled with `Execution.Result`.

The separate `GraphQL.IncrementalDelivery` model targets PR #1110 at `045e193`.
Its syntax remains in `Operation.lean`; `Execution.lean` contains pure finite
resolver execution and the spec-shaped response interface. `WorkScheduler.lean` is
self-contained, importing only Execution: it contains both work accounting and the
source contract in the `WorkScheduler` namespace. `Correctness.lean` is also self-contained,
importing WorkScheduler and
containing wire/query observations, reconstruction, and public correctness propositions.
Query correctness statements live in the `Correctness` namespace.
Do not split either module merely to shorten it. `Exploration.lean` and the executable
schedule enumerator have been removed; admission is defined solely by relations.
Incremental validation, named fragments, effectful resolvers, infinite sources, and
host timing remain outside scope.

`executeQuery`, `executeQueryWithFuel`, and `executeRootSelectionSet` now return
`ExecutionResult` directly, with an explicit `Execution.WorkScheduler` source factory.
The pinned draft retains an ordinary response branch when there is no work; otherwise
execution returns the initial incremental result and a resumable `ResponseEventStream`.
`Response` remains the ordinary data/errors map shared with `GraphQL.Execution.Response`.
`ExecutionResult` is the generalized query return type: ordinary response or incremental
stream. This model name is broader than Section 7's ordinary execution-result map.
`ExecutionObservation` is the separate finite materialization used by correctness:
it stores the updates observed so far and may be an interrupted prefix or complete outcome.
`EventSource` stores opaque admissible/finished predicates and the observed history, not
a selected future trace. This partial state can admit multiple next observations.
`ResponseEventStream.next` accepts available batches with an admissibility premise and updates
the history and mapper IDs functionally. Initialization abstracts waiting for the first
result; no host timing, threads, or infinite-run semantics are introduced.
`executeRootSelectionSetCore` still computes data and finite Work independently of
scheduling. Work retains precomputed pure outcomes; resolver execution is not suspended.

Spec algorithm boundaries are explicit: root/composite callers collect, build a plan,
then pass new defer usages and that plan to `executeExecutionPlan`. Plan execution never
replans. `executeCollectedFields` owns schema lookup and response-map insertion;
`executeField` returns a completed value. `completeListValue` is the ordinary draft loop;
`completeListValueWithStream` is the explicitly non-spec stream hook. The root's response
branch is inline; `executionFromWork` and `executeResponseField` are proof-only induction
helpers, not public execution wrappers. The direct-result root equation now lives in
`Proofs/GraphQL/IncrementalDelivery/Correctness/RootExecution.lean`; the response-field
decomposition is also checked.
The stream hook retains an empty boundary at `initialCount = list.length`, but not when
the count exceeds the list. An empty stream is nonempty work: root execution returns an
incremental response before queue initialization, matching the pinned draft and GraphQL.js.
There is no queue-level ordinary-response fallback or alternate exhausted-source contract.
See the per-definition
cross-reference in `docs/incremental-delivery.md` for retained model projections.

The former deterministic `WorkScheduler.Queue`, FIFO selection, and queue-state proofs
were removed. The later `ExecutionProgram`/`Realizes` layer is also removed.
`WorkQueueResult.Conforms` characterizes initialization, admitted prefixes, and termination.
`WorkScheduler.Conforms scheduler work` requires that contract only for the given nonempty
work. Query observations apply it to the work actually submitted, not every raw Work;
ordinary responses and invalid roots impose no law on their unused scheduler. The unused
global `LawfulWorkScheduler` bundle was removed. The spec-named
`mapIncrementalWorkEventsToResponseEvent` installs a mapper for work-event batches, and
response mapping alone owns `IDState`, `ensureID`, and the entry constructors.
`batchIncrementalResults` builds a new stream with nonempty groups of upstream inputs.
Its event mapper runs the upstream mapper in order, concatenates response-entry lists,
and takes the final hasNext; there is no batching flag. `ResponseEventStream.Input`
distinguishes one upstream event from an aggregated group without selecting future events.
`ResponseEventStream.next` takes caller-supplied available batches. Query execution never
chooses a completion order, drains a source, or chooses a response batch width.

The public `WorkScheduler` namespace gives the independently specified finite
work-accounting relation, distinct from the factory type `Execution.WorkScheduler`.
It distinguishes work outcomes, successful value publication, and node termination,
preserves producer dependencies and stream publication order, supports failure and
cancellation, and permits alternative notice frontiers and owner ties. The source is
opaque to execution; its history evidence is not a required implementation structure.
`WorkScheduler.lean` has a `Proposed WorkQueue invariants` section, separate from the finite
witness model: `Initialized`, `PrefixClosed`, `AccountsForWork`, and `TerminationMatchesWork`
are named premises assembled by `Conforms`. They are prospective spec contributions,
not already-normative scheduler requirements. Observable Section 7 requirements remain
proof targets; no response correctness predicate is assumed by these queue invariants.
The pinned spec leaves CreateWorkQueue undefined. The accounting/release rules
complete that gap and must not be described as normative spec pseudocode. In particular,
any inadequacy of this contract should become a counterexample or missing assumption,
not be hidden by filtering on lifecycle, disjointness, or merge success.
`SharedGroupValue`, `selectGroupOwner`, and `normalizeGroupValues` are proof-side
GraphQL.js adapter definitions in `OwnerNormalization`; they are not public execution or
scheduler definitions.

Work admission is now defined directly over output histories. `ValidHistory` combines
prefix/run admission; `AdmissibleNext` permits a nonempty extension of a valid nonterminal
history, with multiple possible next batches. `Graph`, `Task`, `Progress`, `Step`,
and `Steps` have been removed. Structural `Occurrence`, `Located`, `TaskAt`, and
`NodeAt` relate outputs to the original Work without compilation or task allocation.
They are now ordinary definitions over `locateWork`: one address traversal returns a
`WorkLocation` view of existing subwork, producer, and enclosing owners. Invalid edges
return none; all repeated node descriptors remain visible. `StructuralEquivalence`
proves agreement with the former structural inductives for arbitrary raw Work.
`Explains` existentially supplies one coherent output-to-occurrence matching and a
bounded ordered failure-cut witness. Notice/closure facts are recomputed from outputs.
`EventAllowed` checks payload provenance, fresh publication, producer/item dependencies,
owner choices, and licensed announcements/closures against output prefixes.
Least causal `NodeFailed` and `TaskCancelled` judgments permit cancellation before
notification without inventing failures. Producer failure and cancellation are explicit
cases; the redundant `ProducerUnavailable` judgment is removed from the public model.
The public failure/cancellation predicates wrap the small `Causality` inductive kernel.
`Reachable` is a single structural inductive outside that namespace, beside the task
and node projections; it has no separate public wrapper.
`TaskHasOwners`, `TaskHasProducer`, `TaskSucceeds`, `NodeHasDependencies`, and `NodeHasProducer`
factor its structural premises without adding invariants or scheduler state.
`NodeAccounted` and `DependencySatisfied` reuse these projections; `EventAccounting`
checks their equivalence to the full-descriptor conditions. Owner selection and notices
still inspect full node metadata. Address traversal uses `do` notation.
`NodeAt` dependency keys are defer ancestors for groups and enclosing defer owners for
streams; structural generation remains the separate singular `producer` relation.
`DependencySatisfied` and `CanAnnounce` name dependency satisfaction and notice readiness.
Question-based section banners separate structural, causal, and observation facts.
Successful silent completions and synthetic stream-end tasks are abstracted away.
Equivalence to the removed transition
model is not proved; the previous contract is recoverable from `4af5c80`.
See `docs/incremental-deliver-scheduler.md` for the research comparison and open obligations.

`AdmissiblePrefix` permits interrupted/stalled finite histories. `AdmissibleRun`
additionally accounts for work and emits termination. `queryObservation` covers both;
`queryOutcome` covers complete finite work runs with all permitted response batching.
`specificationSource` admits every contract prefix/run for explicit initial notices;
`specificationScheduler` requires an explicit initialization choice. There is no canonical
query `.toTrace` or default deterministic scheduler.

`Correctness.lean` defines `ExecutionObservation.DeliversSlices` by successful deterministic
`ExecutionObservation.decodeSlices` output. Public `DeliveryTrace.decodePatch`, `decodePatches`,
and `decodeUpdates` replace the former inductive position relations; they replay supplied
wire observations using causal notices and list cursors. Work admission stays relational.
The redundant defer-only position relation and unused stream-free domain are removed.
One Boolean `DeliveryTrace.idUsageValid` checker underlies both prefix ID safety and
complete lifecycle validity. Lifecycle additionally checks closure and hasNext flags.
Reconstruction modifies data only and obtains its error count from `ExecutionObservation.totalErrors`.
No correctness property is added to scheduler admission by this simplification.

### Current proof and build status

All 12 public query-correctness statements have checked witnesses. Whole-project
`lake build` and `lake lint` pass. `Tests/.../PublicStatements.lean` checks every exact
public witness type; axiom audits report only `propext`, `Classical.choice`, and
`Quot.sound`, without `sorryAx` or additional axioms.

The public propositions and proof witnesses are:

- `incrementalDirectiveFreeExecutionEquivalentToBasic`: `Correctness/Query`.
- `queryOutcomeExists`: `Correctness/QueryOutcomeExistence`.
- `deliveryIDsUnique`, `deliveryIDsEventuallyComplete`,
  `deliveryIDsCompleteExactlyOnce`: `Correctness/QueryIdentity`.
- `deliveryIDUsageValid`, `deliveryPatchesAnnounced`: `Correctness/QueryIDUsage`.
- `deliveryLifecycleValid`: `Correctness/QueryLifecycle`.
- `deliverySlicesDisjoint`: `Correctness/QueryDisjointness`.
- `deliveredResponsePositionsEquivalentToBasic`, `basicLeavesDeliveredExactlyOnce`:
  `Correctness/QueryCoverage`.
- `mergedExecutionEquivalentToBasic`: `Correctness/QueryReconstruction`.

Every witness uses the statement name plus `_holds`. Safety/disjointness cover all
admitted prefixes, including errors and interrupted observations. ID liveness/lifecycle
cover complete finite runs, including failures. Data reconstruction, basic-position
coverage, and leaf-once require only `queryOutcome` and `totalErrors = 0`;
`queryOutcome_executionComplete_iff` derives the former separate completeness premise.
Disjointness is `slices.flatten.Nodup`, equivalently within-slice uniqueness and pairwise
disjointness. The raw-trace `executionComplete` predicate is unchanged.

#### Observation, lifecycle, and data proof layers

`RootExecution` factors direct-result execution into proof-only work packaging and proves
initial data/error independence. `InputObservation` characterizes supplied input replay
and residual streams; composition and batching preserve every intermediate admitted prefix.
`SourceObservation`/`QueryObservation` recover actual work histories.
`SourceRealization`/`QueryRealization` prove the converse, including all nonempty response
groupings and ordinary/invalid-root branches. Main interfaces include
`workObservation_iff_realizable` and `queryObservation_iff_workHistory`.
`HistoryPrefixes` proves admission prefix closure; `SpecificationSource` proves maximal
source conformance for valid initial notices. These are realization theorems, not assumed
response correctness or selected futures.

Work-node accounting/lifecycle proofs derive fresh notices, open references, unique
completion, and terminal closure directly from admission. Mapper identity, reference,
metadata, and response-replay proofs transport them through stable allocation and both
batching stages. `IDUsageProperties`, `LifecycleProperties`, `LifecycleControl`, and
`ResponseMerging` independently explain the conditional wire checkers. Termination-only
updates after the last ID closes remain permitted.

`ExecutionErrors` and `TaskErrors` derive positive bubbling failures for generated work;
raw work may encode zero-count errors. Failure reporting and error-conservation proofs
cover all grouping stages. `SuccessfulWork` and `PublicationCoverage` derive failure-free,
exactly-once task publication from complete zero-error observations, without strengthening
scheduler admission.

`SourcePositions` supplies source path/cursor certificates. Work/mapper/notice metadata,
`StreamCoordinates`, and `HistoryStreamCursors` transport them to actual observations.
Absolute-position, atom, and wire-replay proofs connect them to deterministic public
decoders; `PositionComposition` retains residual cursors and earlier notices.
`QueryDisjointness` covers all admitted prefixes.

Typed source reconstruction and `RootSourceReconstruction` identify the successful source
inventory with basic execution. `QueryCoverage` derives position equivalence and leaf-once.
Source/history attachment proofs establish parent availability; `TypedCursorAgreement`,
`HistoryMerging`, and `WireAtomMerging` establish actual reconstruction.
`QueryReconstruction` finishes response equivalence using error conservation.
These are unconditional witnesses of the public propositions, not missing wire bridges.

#### General finite progress

`Initialization` derives valid initial notices for every nonempty generated work tree.
`QueryExistence` retains the independent initialization-only factory and prefix-existence
theorem. Complete existence is separately proved in `QueryOutcomeExistence`.

`HistoryExtension`, `PublicationExtension`, and `FailureExtension` construct actual
steps preserving old evidence. `CompletionExistence` finalizes any task-accounted history
and also supports selective owner closure. `FiniteHistories` bounds histories by finite
publication/completion tokens and supplies property-preserving maximal extensions.
`TaskReadiness`, `DependencyKeys`, `OwnerAvailability`, and `LeastKeyProgress` derive
producer/item readiness and a least healthy outstanding owner.

`NoticeFrontiers`/`NoticeCoverage` construct covering initialization and actual carriers.
Full ordinary notice coverage can fail after object publication: silent co-owner
accounting can make a child stream eligible before a carrier is available.
`GroupAccounting` proves that a healthy accounted defer group has a published contributor,
without assuming that each cancelled task's owners fail.
`MixedNoticeMetadata`, `MixedNoticeCoverage`, and `MixedNoticeExtension` establish the
proof-only `SupportedNoticesCovered`: groups use ordinary eligibility, while streams may
wait until one parent and its full ancestry are satisfied. Public admission remains more
permissive. The witness is an existential construction choice, not a scheduler law.

`MixedProgressEvents` preserves supported coverage across success/failure events and
stream completion; covering group-success and stream-item carriers supply it directly.
`MixedExistence.mixed_completeRun_exists` maximizes a supported history. Healthy accounted
keys can close; a least outstanding owner has full support and is already announced,
giving a further ready step unless every task is accounted for. Finalization supplies
the complete run, for arbitrary shared owners, mixed nesting, and fixed outcomes.

`QueryOutcomeExistence` obtains all metadata from execution:
`executeRoot_completeRun_exists`, `executeRoot_completeObservation`, and
`queryOutcome_exists` require no history, validation, success, scheduler, or shape premise.
The public `queryOutcomeExists` in `GraphQL/IncrementalDelivery/Correctness.lean` packages
this final theorem. This proves existential finite progress, not completion of every
admitted prefix or every conforming source. Fairness, host-future termination, and
equivalence to the removed graph scheduler remain unproved/outside scope.

#### Scheduler research follow-up

`History.CanFinish` and `Execution.WorkQueueResult.Nonblocking` are optional public
progress propositions, separate from unchanged admission and `Conforms`. Proof-only
`WorkScheduler/Nonblocking.viableSource` admits exactly prefixes of terminal runs, is
nonblocking, and conforms when its initialization is viable. Any conforming nonblocking
source admits only viable histories; an unfinished maximal admitted history is impossible.
`Tests/Nonblocking` proves that initializing only an empty stream while omitting an
independent successful one-item stream has no complete run under any explanation/batching.

`MixedExistence.mixed_supported_accounted_extension` generalizes mixed progress to an
existing explained prefix with supported coverage. `mixed_supported_continuation` retains
initial notices and existing work batches, with matching/failure evidence existential.
The old complete-run theorem wraps covering initialization and this continuation result.
It does not show arbitrary admitted prefixes or arbitrary restrictive sources nonblocking.

`FailureWitness` omits explicit failure Nodup. `WorkScheduler/Minimality` derives
`FailureWitness.nodup` for all raw work: open-owner licensing supplies nonempty ownership,
and an earlier duplicate cancels its task. `failureWitness_iff_nodup_and` verifies that
restoring the redundant clause changes nothing. Terminal node accounting implies task
accounting under nonempty task ownership and an explained history; the public terminal
task clause is retained for permissive raw work. Tests retain an explained raw
ownerless counterexample and isolate freshness, item order, failure licensing, and counts.
`WorkScheduler/Independence` proves local accounting commutation of distinct already-ready
successful object publications, including shared owners, and notice-free healthy group
closures with distinct keys. Tests show that notice permutations change wire IDs and
closure permutations change entry order; no exact wire-history quotient is asserted.
Old/new normalization was explicitly excluded. Host fairness and elimination of ordered
failure evidence remain open. See the scheduler guide's checked research results.

#### Specializations and regression coverage

`DeferOnly.completeRun_exists` and its ready-extension interface specialize mixed progress
using the constant defer-role assignment and equivalence of the two coverage predicates.
Singleton and root-singleton work interfaces specialize the defer-only theorem.
All four shape-restricted query-existence interfaces are thin compatibility wrappers
around unconditional query existence, retaining their declaration names and parameters.

Raw stream/phase results retain independent proofs where they have genuinely weaker
metadata assumptions or preserve an existing prefix: `NestedStreamExistence`,
`StreamContinuation`, `DeferredStreamExistence`, `DeferredPhase`, and
`InitialDeferredExistence`. Do not add stronger metadata premises just to reuse mixed
progress. `located_producer_context` now lives in `WorkMetadata`, and
`ready_owner_dependency_unsatisfied` in `OwnerAvailability`; their names are unchanged.
The generic mixed proof no longer imports special-case existence proofs.

Tests cover actual alternating defer/stream/defer/stream work with shared producers,
produced defer failures, stream-item failures, exhausted fuel with nonempty work, invalid
roots, silent co-owner accounting, empty streams, nonzero cursors, cancellation,
decoder composition, and complete wire realization. `MixedNoticeCoverage` retains both
the full-coverage counterexample and its complete-run witness.
`EmptyStreams` proves zero-item incremental outcomes for empty/exact-count queries and
rules out ordinary outcomes under every scheduler for those retained boundaries.

Retired program/graph/enumeration proofs and duplicate helpers are recoverable from
`718d6ab`; the graph scheduler from `4af5c80`, and deterministic scheduler from `e0b027b`.
The obsolete `DeferNoticeCoverage` proof module is recoverable from `567c83f`.
Their old open-proof reports are historical, not current obligations.
See `docs/incremental-delivery.md` for the current detailed proof map and
`docs/incremental-deliver-scheduler.md` for research and stronger-progress boundaries.

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

For model/interface regressions, use these optional focused checks
(the WorkScheduler regressions also import the small causal-failure proof module):

```sh
lake build GraphQL.IncrementalDelivery Tests.GraphQL.IncrementalDelivery.Execution Tests.GraphQL.IncrementalDelivery.SpecInterfaces Tests.GraphQL.IncrementalDelivery.Sources Tests.GraphQL.IncrementalDelivery.Correctness Tests.GraphQL.IncrementalDelivery.PositionDecoding Tests.GraphQL.IncrementalDelivery.WorkScheduler
```

The rebuilt query/observation, source/history, and all public correctness proofs are
checked with:

```sh
lake build Proofs.GraphQL.IncrementalDelivery.Correctness Tests.GraphQL.IncrementalDelivery.Query Tests.GraphQL.IncrementalDelivery.WireProperties Tests.GraphQL.IncrementalDelivery.SourceObservation Tests.GraphQL.IncrementalDelivery.QueryObservation Tests.GraphQL.IncrementalDelivery.WorkLifecycle Tests.GraphQL.IncrementalDelivery.HistoryScheduling Tests.GraphQL.IncrementalDelivery.FailureReporting Tests.GraphQL.IncrementalDelivery.QueryDisjointness Tests.GraphQL.IncrementalDelivery.QueryCoverage Tests.GraphQL.IncrementalDelivery.QueryReconstruction Tests.GraphQL.IncrementalDelivery.PublicStatements
```

The broader incremental check is:

```sh
lake build GraphQL.IncrementalDelivery Proofs.GraphQL.IncrementalDelivery.Semantics Tests.GraphQL.IncrementalDelivery
```

The current tree passes `lake build` and `lake lint`. The broader incremental check
builds proof modules; the definition-only check does not. `lake lint` runs a whole-project build.

## Where To Look

- `docs/spec-conformance.md`: high-level coverage, assumptions, and exclusions only.
- `docs/execution.md`: main execution representation and specification correspondence.
- `docs/incremental-delivery.md`: incremental execution details, per-definition spec
  mapping, scheduler assumptions, correctness statements, and proof status.
- `docs/incremental-deliver-scheduler.md`: history-based scheduler design, primary-source
  research comparison, failure witnesses, and open refinement obligations.
- `docs/development.md#lean-module-organization`: module organization rules for keeping
  top-level Lean files definition-only and theorem files topic-specific.
- `docs/overview.md`: durable project introduction, architecture, and topic navigation.
- `docs/theories/normal-form.md`: public normal-form statements and proof-witness map.
- `docs/theories/normal-form-uniqueness.md`: ground and complete uniqueness proof plan.
- `docs/theories/query-inclusion.md`: query-inclusion semantics, checker, and proof domain.
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
