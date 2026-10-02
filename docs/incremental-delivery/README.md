# Incremental Delivery

This guide documents the separate `GraphQL.IncrementalDelivery` model: its execution
interface, specification correspondence, work-queue assumptions, response correctness
statements, and proof status. For coverage without implementation details, see the
[conformance summary](../spec-conformance.md#incremental-delivery-draft-covered).

Read this guide for the execution/spec cross-reference and public correctness statements.
The [semantics guide](semantics.md) defines the independent work-queue contract and its
research basis. The [implementation guide](implementation.md) describes the executable
reference queue, its GraphQL.js correspondence, and its conformance proof.

The target draft spec is
[graphql/graphql-spec PR #1110 at 045e193](https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec). The specification references are:

- [Execution](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%206%20--%20Execution.md).
- [Response](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%207%20--%20Response.md).
- [Type System](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%203%20--%20Type%20System.md).

## Module boundaries and execution scope

| Public module | Responsibility |
| --- | --- |
| [Operation](../../GraphQL/IncrementalDelivery/Operation.lean) | Incremental operation syntax, separate from the main operation model. |
| [EventSource](../../GraphQL/IncrementalDelivery/EventSource.lean) | Generic opaque finite source languages and observation helpers; no execution dependency. |
| [Execution](../../GraphQL/IncrementalDelivery/Execution.lean) | Pure finite resolver execution, deferred/streamed work, observable WorkQueue interface, and response mapping. |
| [WorkQueueSemantics](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean) | Relational work accounting and proposed source invariants; imports only Execution. |
| [Observation](../../GraphQL/IncrementalDelivery/Observation.lean) | Finite execution observations, query completion, and query-local queue conformance; shared by Correctness and WorkQueueImplementation. |
| [Correctness](../../GraphQL/IncrementalDelivery/Correctness.lean) | Public correctness propositions; imports Observation. |
| [WorkQueueImplementation](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean) | Concrete queue/publisher state machine and its projection to the shared WorkQueue interface. |

WorkQueueSemantics and Correctness are self-contained definition modules. Public
definitions
do not import proof modules. Schema, resolver, input preparation, and ordinary response
primitives are shared with [the main execution model](../execution.md).

Collection supports inline-fragment defer, skip/include, runtime type conditions, aliases,
variables, labels (including explicit null), and overlapping deferred selections. Fields
are partitioned by filtered defer-usage sets; shared fields resolve once. Stream applies
to the outermost list, keeps its initial prefix, and resets inherited defer context inside
remaining items. Null propagation and errors retain the counted-error projection.

Execution assumes valid directive placement/types, non-repeatability, literal unique
labels, and no overlapping streamed field selections. Incremental validation and
named-fragment algorithms are not implemented. Full coercion, detailed errors,
introspection, mutation, subscription, and transport retain the main model's exclusions.
Resolver outcomes are pure and finite: effectful resolvers, infinite sources, host timing,
and external transport cancellation are outside scope.

## Execution results and response streams

`executeQuery`, `executeQueryWithFuel`, and `executeRootSelectionSet` return
`ExecutionResult` directly. A plain `createWorkQueue : Work → WorkQueue` parameter
supplies
the draft's unspecified CreateWorkQueue, without a scheduler structure:

- With no incremental work, root execution returns `.single response`.
- Otherwise, it returns `.incremental initial subsequent`: an initial incremental
  result and a resumable `ResponseEventStream`.

`Response` remains the ordinary data/errors map shared with
`GraphQL.Execution.Response`. `ExecutionResult` is the generalized
ordinary-or-incremental query return type, broader than Section 7's ordinary
execution-result map. Request-error results and subscription streams are excluded.
`ExecutionObservation` is deliberately separate: it materializes a finite list of
updates observed from an `ExecutionResult`, and may represent either an interrupted
prefix or a complete outcome.

`executeRootSelectionSetCore` computes initial data/errors and finite (remaining) `Work`.
Resolver results and child work are precomputed pure outcomes in Lean model,
not host futures. Incremental delivery models how the aggregate `Work` tree is peeled
off and serialized into a sequence of events.
The event source varies their completion observations, not their underlying values.
Initial data/errors come from the execution core; pending notice identities, order,
and initial wire IDs come from source initialization and need not be independent of it.

Initialization abstracts waiting for the first result and consumes no subsequent
work-event batch. The model follows YieldIncrementalResults's unbatched initial envelope;
optional proxy coalescing of later updates into that envelope remains unmodeled.

### WorkQueue modeling and node ID accounting

`Execution.WorkQueue` contains initial groups/streams and a shared `EventSource` of
work-event batches. `WorkQueueEvent` represents GROUP_VALUES, GROUP_SUCCESS,
GROUP_FAILURE,
STREAM_VALUES, STREAM_SUCCESS, STREAM_FAILURE, and WORK_QUEUE_TERMINATION.

A source stores admissible/finished predicates and its observed history, not a future
trace. This intentionally partial state can admit several next batches. Hidden progress
states remain existential witnesses in the work contract; an unavailable next batch
does not imply source termination.

`mapIncrementalWorkEventsToResponseEvent` installs a resumable mapper separate from
task accounting. The mapper owns `IDState`, `ensureID`, `getPendingEntry`,
`getIncrementalEntry`, `getCompletedEntry`, and
`getIncrementalStreamUpdateResult`. Initial and later notices share one ID supply.
The draft gives these helper algorithms implicit access to `idMap` and `nextID`.
Lean makes that context explicit: `IDState` stores both values, and the entry
constructors receive `idFor` so the stateful mapper remains the only ID authority.

`Execution.initializeIncrementalResponse` constructs the initial root data/errors
envelope and pending notices, returning the ID state that seeds subsequent mapping.
Both `yieldIncrementalResults` and the reference implementation use this helper. Initial
notices come directly from queue initialization; `mapWorkEventBatch` only maps subsequent
updates, so no synthetic initial work event is needed.

The executable draft mapper also separates `GROUP_VALUES` from
`GROUP_SUCCESS`/`GROUP_FAILURE`. The model consequently permits a payload and its
completion notice in different batches, so a notice may follow an earlier data patch.
It reads Section 7's requirement that the corresponding data "must have been
completed" in the notice's result as a statement about completion by that point, not
as a requirement that the data patch and notice be co-located. If co-location is
intended, the draft's work-event contract or mapper needs an additional coupling rule.

### Batching and sequential observation

`batchIncrementalResults` constructs a new response stream. Its source admits
nonempty available groups of upstream inputs in order. Its mapper runs the upstream
mapper on that group, concatenates response-entry lists, and uses the final hasNext.

`ResponseEventStream.Input` records the stage's input type: a work-event batch for
the initial mapper, a list of upstream inputs for batching. Each `next` accepts an
admitted input, emits one response event, and advances history and mapper IDs
functionally. Every intermediate upstream prefix must be admitted. Construction
consumes no events; batching begins at the current source position and composes with
an existing batching stage.

Compatible values can be grouped within a work event, work events can share batches,
and response updates can be batched again independently. Observation is sequential
and aggregated. It models availability choices, not wall-clock waiting or threads;
query execution does not choose a completion order or drain the source.

## Spec-origin execution definitions

The names below use lower camel case for the corresponding spec algorithm. Review
`GraphQL/IncrementalDelivery/Execution.lean` alongside the pinned Execution chapter.
This is a scoped formal model, not a literal transcription: schema/resolvers, fuel,
state supplies, and the shared error-count representation are explicit Lean parameters.
The table states both the algorithm boundary and the retained projections; it must not
be read as claiming the omitted spec features are implemented.

| Definition / spec counterpart | Steps to compare and retained projection |
| --- | --- |
| `coerceVariableValues` / CoerceVariableValues | Materialize missing defaults; supplied values are already coerced. Full request validation/coercion is excluded. |
| `collectFields` / CollectFields | Iterate selections, collect each selection, merge response-name groups, append new defer usages. The per-selection body is `collectSelection`; named fragments and visitedFragments are excluded. |
| `collectSubfields` / CollectSubfields | For every grouped field, collect its child selection set under its defer usage, then merge fields and new usages. Collecting an empty set has the same effect as skipping it. |
| `getFilteredDeferUsageSet` / GetFilteredDeferUsageSet | An immediate occurrence clears the set; otherwise deduplicate usages and remove those dominated by an ancestor. Stored ancestor lists replace the parent-pointer loop. |
| `buildExecutionPlan` / BuildExecutionPlan | Partition field groups by equivalent filtered defer-usage sets relative to the parent set. Returns an ExecutionPlan only; performs no execution. |
| `getNewDeferMap` / GetNewDeferMap | Extend the inherited map with path/label-aware deferred fragments and their ancestry. Parent pointers are flattened into ancestor lists. |
| `executeExecutionPlan` / ExecuteExecutionPlan | Takes newDeferUsages and an already-built ExecutionPlan. Extend the defer map, execute immediate fields, collect execution groups, and combine work. The executionMode parameter is omitted because this model exposes only query operations and normal composite execution. Pure sequential evaluation is observationally sufficient for pure resolvers; bubbling failure discards/cancels unexposed sibling work. |
| `collectExecutionGroups` / CollectExecutionGroups | Look up each partition's fragment owners, construct its ExecuteExecutionGroup task, accumulate tasks. Finite pure task outcomes replace future computations; no completion order is selected. |
| `executeExecutionGroup` / ExecuteExecutionGroup | ExecuteCollectedFields returns data, counted errors, and child work. Deferred errors remain task-local until their delivery boundary. |
| `executeCollectedFields` / ExecuteCollectedFields | Take the first grouped field, look up its schema definition, call ExecuteField, insert its value under responseName, accumulate work. Invalid groups/schema misses still produce counted errors, rather than implementing the spec's skip-undefined branch; validation is excluded. |
| `executeField` / ExecuteField | Read the first field, coerce arguments, resolve, CompleteValue. Returns a completed value and work, not a response-map slice. The caller-provided FieldDefinition bundles the spec's fieldType with argument definitions needed by the shared coercion helper. Explicit responseName gives alias-correct paths. |
| `completeValue` / CompleteValue | Fuel-bounded non-null/null/list/leaf/composite cases. Composite completion explicitly calls CollectSubfields, BuildExecutionPlan, then ExecuteExecutionPlan. Leaf coercion/runtime type resolution retain the shared model's projections. List dispatch includes the separately named stream extension below. |
| `completeListValue` / CompleteListValue | Complete each item at its indexed path and accumulate values/work. An explicit index carries the loop counter, normally starting at zero. This algorithm itself does not initiate streaming. |
| `executeRootSelectionSet` / ExecuteRootSelectionSet | The model-only core performs CollectFields, BuildExecutionPlan, ExecuteExecutionPlan. The root then extracts data/errors, checks for work, calls YieldIncrementalResults, and batches the subsequent stream. The ordinary/incremental branch is inline. |
| `executeQuery` / ExecuteQuery | Query-only entry point calling root execution. The explicit-fuel variant also materializes variable defaults and checks root-source applicability, inherited model entry-point conventions. Default-fuel calculation and arbitrary-invalid-root errors are not spec steps. |
| `yieldIncrementalResults` / YieldIncrementalResults | Call the supplied CreateWorkQueue function, use initializeIncrementalResponse for the initial envelope and IDs, return that result plus the resumable work-event mapper. Waiting for initialization is abstracted; no future batch is selected or consumed. |
| `mapIncrementalWorkEventsToResponseEvent` / MapIncrementalWorkEventsToResponseEvent | Install a lazy mapper over admitted batches, threading the ID map when an observation is accepted; the seven-case per-batch loop is factored as mapWorkEventBatch. Initial and later notices share IDs despite the draft's allocation-scope ambiguity. |
| `ensureID` / EnsureID | Reuse the node ID or allocate the next decimal string and increment the supply. |
| `getPendingEntry` / GetPendingEntry | Ensure IDs and build notices, groups before streams; one map over concatenated lists represents the two spec loops. |
| `getIncrementalEntry` / GetIncrementalEntry | Ensure the chosen group's ID, include data/errors, drop its path prefix to obtain subPath. |
| `getCompletedEntry` / GetCompletedEntry | Ensure the node ID and include counted completion errors. Callers pass zero for omitted errors. |
| `getIncrementalStreamUpdateResult` / GetIncrementalStreamUpdateResult | Package hasNext and the three entry lists. Empty lists encode omitted optional entries; this is a typed result, not a JSON serializer. |
| `batchIncrementalResults` / BatchIncrementalResults | Return a new stream over nonempty available groups of upstream inputs. Map the upstream events in order, concatenate response lists, and take the final hasNext. No batching flag or selected future suffix; host readiness/clocks are not modeled. |

These response structures precede JSON serialization. An error count of zero encodes an
omitted `errors` entry, an empty object-result `subPath` encodes an omitted `subPath`,
and empty update lists encode omitted `pending`, `incremental`, or `completed` entries.
For labels, `Option DirectiveLabel` preserves the wire distinction: `none` means the
label entry was omitted, while `some .null` means an explicit null argument.

The two planning call sites are the root core and CompleteValue's composite branch:
both perform collection → BuildExecutionPlan → ExecuteExecutionPlan explicitly.
Work is a finite tree, not the spec's literal groups/tasks/streams record: `Work.combine`
retains independent sibling components without selecting a completion order, and the
structural scheduler relations identify shared fragment owners. Its left/right
association is nevertheless structural: work addresses traverse those sides, so the
constructor does not assert commutativity or associativity.

| Draft `Work` field/operation | Lean representation |
| --- | --- |
| `groups` | The contributing `DeferredFragment` owners on each `Work.executionGroup` occurrence. |
| `tasks` | A `Work.executionGroup` occurrence records one finite execution-group outcome; the item outcomes inside `Work.stream` represent later stream work. |
| `streams` | Each `Work.stream` occurrence records one stream delivery boundary and its finite remaining items. |
| Combining work records | `Work.combine` retains sibling work without choosing a schedule; unlike the draft's unordered-map merge, its association is used by the WorkQueue semantics as "address". |

Each nested work occurrence has one structural producer. Scheduler dependencies are
instead group ancestry or enclosing stream owners; they are not additional producers.
That representation difference, pure precomputation instead of futures, and the explicit
draft gaps below remain substantive abstractions rather than line-by-line equivalences.

`Tests/GraphQL/IncrementalDelivery/SpecInterfaces.lean` checks that executing a supplied
plan respects its partitions (even when replanning its field metadata would disagree),
ExecuteField returns a value, and CompleteListValue does not install a stream task.

## Operation definitions

`Operation.lean` contains syntax/data projections, not execution algorithms:

| Definition | Spec correspondence / reason |
| --- | --- |
| `DirectiveApplication` | Built-in skip/include/defer/stream directive applications and defaults. Raw inputs stay permissive; incremental validation is excluded. |
| `Selection` | Field and InlineFragment grammar, with aliases already resolved to responseName. Named spreads and source locations are excluded. |
| `Operation` | Query OperationDefinition: name, kind, variable definitions, selection set. Document selection and other operation kinds are excluded. |
| `Operation.rootType` | Root-operation-type lookup, a helper rather than a named execution algorithm. |
| `Selection.responseName?`, `subselections`, `isField`, `isInlineFragment` | Syntax accessors/predicates; no standalone spec algorithms claim these names. |
| `Selection.size`, `SelectionSet.size`, `Operation.size` | Non-spec structural measures supporting termination and the default completion-fuel bound. |

## Model-only definitions and why they exist

- `EventSource`: opaque admissible/finished predicates and the already-observed history.
  The state is partial, admitting multiple future continuations; it is not a complete
  schedule or a required task-ledger representation.
- `createWorkQueue : Work → WorkQueue`: a plain function supplying CreateWorkQueue's
  interface, not a scheduling algorithm or additional structure.
- `Execution.WorkQueue`: initial groups/streams and an opaque event source, hiding the
  implementation's concrete state and input events.
- `WorkQueueEvent`, `ExecutionGroupValue`, `StreamItemValue`: typed versions of the seven
  named event forms and their successful payloads, using GraphQL.js names. The reference
  implementation uses these canonical execution types directly.
  `ExecutionGroupValue.deliveryGroups` retains implementation metadata through owner
  selection. The reference source checks it; abstract admission and wire mapping ignore
  it. Raw and normalized events share representation, not owner semantics.
- `IDState`: the mapper's idMap and nextID, separate from scheduling.
- `Execution.initializeIncrementalResponse`: factors initial notice allocation and root
  response packaging from YieldIncrementalResults. The reference implementation reuses
  it, adding concrete queue and live-owner state without duplicating response construction.
- `mapWorkEventBatch`: factors the spec's per-batch loop from its surrounding stream map.
- `ResponseEventStream`, `ResponseEventStream.Accepts`, `ResponseEventStream.next`:
  the mapper's responseEventStream, represented by a source input type, partial source
  history, mapper IDs, and an event-mapping function. Observation supplies one admitted
  input and updates state functionally. Batching transforms the input type to a nonempty
  group of upstream inputs and installs the spec's aggregation function. `Execution.lean`
  defines and constructs streams. `Observation.lean` supplies `Accepts`, `next`, and the
  finite `Observes` relation, so advancing a stream requires importing that module.
  `Correctness.lean` adds response-correctness properties; neither stream construction nor
  observation requires it.
- `combineIncrementalResults`: the list-entry concatenation and final hasNext rule used
  by the spec's batching stage.
- `executeRootSelectionSetCore`: factors the first three root steps, preserving their
  order and distinct call boundaries.
- `getStreamUsage`, `streamInitialCount?`, `completeListValueWithStream`,
  `completeStreamItems`: finite implementation of the stream directive/response contract
  where the pinned execution algorithm lacks a hook. These are explicitly not named spec
  algorithms. The outermost-list rule and fresh item delivery boundaries belong to this
  extension.
- `rootSourceAppliesBool`, `executeQueryWithFuel`, `executeQueryFuelBound`: inherited
  entry-point checks and explicit/default finite-completion controls, not extra normative
  query steps.
- `directiveAllowsSelectionBool`, `selectionDirectivesAllowBool`, `directiveLabel?`,
  `activeDefer?`: the collection algorithm's directive checks and typed label extraction.
- `FieldDetails`: the draft's field detail, using GraphQL.js's type name. The field
  selection is flattened into execution-relevant components and its defer usage.
  `FieldCollection.collectedFieldsMap` and `newDeferUsages` name the draft's returned
  collection components.
- `CollectedFieldsMap.addFieldSet`, `CollectedFieldsMap.merge`, `FieldCollection.append`:
  list-backed ordered-map accumulation for collection.
- `deferUsageSetsEquivalent`, `addExecutionPartition`: finite set equality and
  partition-map insertion used by BuildExecutionPlan.
- `freshExecutionKey`, `lookupDeferredFragment?`: explicit defer/stream node identity
  supply and defer-map lookup, not scheduler choices.
- `Completion.pure`, `error`, `combine`, `map`, `catchNull`, `nonNull`: typed
  data/work/error propagation replacing pseudocode return values and raised errors.
- `Work.size`, `Work.itemsSize`: finite executable-record accounting, also used to
  recognize when no execution-group task, stream descriptor, or remaining stream item
  exists.
- `EventSource.Allows`, `advance`, `IsFinished`, `ofList`, `batch`: observation-state
  plumbing, fixed finite fixture sources, and nonempty order-preserving grouping. Every
  intermediate prefix must be admitted; no available output does not imply termination.
  Grouping starts at the current source position without replaying prior events.

The remaining structures and aliases name typed spec concepts or representation machinery:
DeferUsage, FieldDetails, CollectedFieldsMap, FieldCollection, ExecutionPlan,
ResponsePathSegment/ResponsePath, DeliveryNode, DeferredFragment/DeferMap, Work,
Completion, StreamUsage, DirectiveLabel, and response-entry/result types. `Response`
retains the ordinary data/errors map shared with `GraphQL.Execution.Response`.
`ExecutionResult` names the generalized ordinary-or-incremental query return type, not
Section 7's narrower ordinary execution-result map. Request-error results and subscription
streams are excluded. `ExecutionObservation` is the finite materialized observation used
by correctness statements; it is not the resumable execution return type.
Shared resolver/value/coercion/error primitives are re-exported from GraphQL.Execution;
their scope is the same as in that model. Representation helpers do not claim normative
names.

## Work-queue contract

The pinned draft spec leaves CreateWorkQueue unspecified. The independent
[WorkQueueSemantics](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean) contract
completes that interface; its accounting and release rules are proposed model
contributions, not normative draft pseudocode.

The boundary is **normalized publication events**. A concrete queue and its publisher's
owner-selection step may together supply this interface. The response mapper then
allocates wire IDs and constructs entries.

### Source contract

`WorkQueue.Conforms` combines four independently named premises:

| Premise | Requirement |
| --- | --- |
| `Initialized` | Fresh initialization with an admitted empty observation history. |
| `PrefixClosed` | Every prefix of an admitted history is admitted. |
| `AccountsForWork` | Every admitted history satisfies `AdmissiblePrefix` or `AdmissibleRun` for the submitted work. |
| `TerminationMatchesWork` | Finished histories are exactly admitted terminal work runs. |

`queryWorkQueueConforms` requires this contract only for nonempty work actually submitted
by the query. Ordinary responses and invalid roots impose no law on their unused queue
constructor.

### Work accounting

Admission is a relation over output histories, not a required runtime data structure.
`Explains` supplies one coherent publication matching and ordered failure-cut witness;
`EventAllowed` checks each atomic event against its preceding output prefix.

The rules require fresh publication, producer-before-child and stream-item order, valid
open owners, licensed announcements and closures, counted failures, and terminal work
accounting. Shared publication requires a healthy open supporter; its effective wire
owner is a longest-path open contributor and may be a different, failed co-owner awaiting
completion. Accepted failures require a previously announced contributor, not necessarily
one still open at settlement. Actual publications and completions still require open IDs.

Failures can precede their notifications. Cut-indexed causality prevents later failure
from retroactively cancelling a published producer or invalidating an earlier notice.
`NodeErrors` counts accepted failures through each completion's boundary.

`AdmissiblePrefix` includes interrupted or stalled histories. `AdmissibleRun` additionally
accounts for work and emits termination. Value coalescing and work batching preserve the
atomic explanation. No lifecycle checker, disjointness conclusion, or reconstruction
property is assumed by admission.

See [semantics](semantics.md) for the structural predicates, notice rules, failure
evidence, optional nonblocking condition, and checked research results. The executable
machine and its smaller host-source contract are described in
[implementation](implementation.md).

### Finite progress domain

Complete finite outcomes exist for every modeled query. This is an existential result,
not completion of every admitted prefix, every conforming source, or every real resolver
future. A source can stall without being finished. Infinite execution, host timing, and
fairness are outside this model.

## Observations and correctness

`Observation.lean` defines finite execution observations and shared query predicates in
`GraphQL.IncrementalDelivery`; observation types and their methods retain the `Execution`
namespace. `Correctness.lean` adds response positions, lifecycle checks, reconstruction,
and public correctness propositions in `GraphQL.IncrementalDelivery.Correctness`.

`ResponseEventStream.Observes` repeatedly accepts batches and updates stream state.
`ExecutionResult.Observes` relates execution results to finite `ExecutionObservation`
observations; its complete flag additionally requires source termination.
`queryObservation createWorkQueue ...` directly observes `executeQueryWithFuel` with the
specified queue constructor; it contains no work extraction or conformance assumption.
`queryOutcome` is its complete-observation case. The correctness propositions separately
require `queryWorkQueueConforms createWorkQueue ...`, local to the nonempty work this
query actually submits. The predicate derives work from execution internally and checks
the queue returned by `createWorkQueue`; it needs no separate concrete-queue predicate.
Conformance of an unrelated queue is not enough. Invalid roots and ordinary responses
impose no queue law. The existence statement supplies both a conforming queue constructor
and a complete outcome. There is no canonical query trace or executable schedule
enumerator.

### Wire positions, lifecycle, and reconstruction

`ExecutionObservation.DeliversSlices` states that the deterministic
`ExecutionObservation.decodeSlices`
returns the given mixed defer/stream slices. `DeliveryTrace.decodePatch`,
`decodePatches`, and `decodeUpdates` replay supplied payloads and updates, returning
`none` for a missing owner notice or list cursor. Positions use response aliases and
zero-based list indices, optionally including container roots. Notices must occur
earlier or in the same update; stream cursors come from initial data and earlier
payloads, including earlier payloads within the same update.

These are model observation helpers, not spec algorithms or scheduler choices.
Decoding positions does not assume valid lifecycles or successful reconstruction.
Only deterministic wire decoding is functional; work admission remains relational.

The Boolean `DeliveryTrace.idUsageValid` checker is shared by prefix ID safety
and complete lifecycle validity. Same-update announcements precede patches, which
precede completions. `ExecutionObservation.lifecycleValid` additionally requires every
announcement to close and hasNext to describe subsequent responses, not currently open
IDs.
The last ID may close before a separate termination-only response. Missing
termination, premature hasNext false, duplicate IDs/completions, and closed-ID
patches remain invalid.

`mergeExecutionObservation` reconstructs data from ID-resolved paths. It rejects
incomplete
or malformed lifecycles and patches at missing or incompatible attachment points.
Data patches do not count errors: the reconstructed envelope uses
`ExecutionObservation.totalErrors`, counting initial, patch, and completion errors once.
Failed shared groups can report errors under multiple IDs; the count-only model
does not deduplicate error identities.

`completedWithoutErrors` requires complete delivery and zero counted errors. Failure
may discard undelivered data; initial null bubbling can cancel work before any
ID is announced, and fuel exhaustion counts as an error. Thus ID closure alone
is not enough for comparison with ordinary execution. This premise does not
assume successful merging, attachment order, or response equivalence.

For admitted complete query outcomes, lifecycle validity is already proved. The three
basic-execution comparison statements therefore assume only `result.totalErrors = 0`
in addition to `queryWorkQueueConforms` and `queryOutcome`, not a separate
`completedWithoutErrors` certificate.
`queryOutcome_completedWithoutErrors_iff` proves these premises equivalent on that domain.
For arbitrary observations, `completedWithoutErrors` checks both lifecycle validity and
zero counted errors.

### Public statements

| Statement | Observation domain and claim |
| --- | --- |
| `incrementalDirectiveFreeExecutionEquivalentToBasic` | Syntactically directive-free operations return the basic response for every queue constructor, without a conformance premise. |
| `deliveryIDsUnique` | Every admitted prefix/run has unique announcements. |
| `deliveryPatchesAnnounced` | Every patch references an earlier or same-update announcement. |
| `deliveryIDUsageValid` | Every admitted prefix/run uses IDs safely, including open-ID patch references and unique completions. |
| `deliveryIDsEventuallyComplete` | Every announced ID completes in the same or a later update of a complete finite run. |
| `deliveryIDsCompleteExactlyOnce` | Every announced ID has exactly one completion in a complete finite run. |
| `deliveryLifecycleValid` | Every complete finite run satisfies the full lifecycle checker. |
| `deliverySlicesDisjoint` | Every admitted prefix/run has globally unique delivered paths: `slices.flatten.Nodup`, equivalently internal uniqueness and pairwise-disjoint slices. |
| `queryOutcomeExists` | Every modeled query has some complete finite outcome, without a scheduler, history, success, or work-shape premise. |
| `mergedExecutionEquivalentToBasic` | Complete, error-free observations reconstruct a response equivalent to execution with incremental directives erased. |
| `deliveredResponsePositionsEquivalentToBasic` | Complete, error-free observations deliver exactly the basic response positions, up to permutation. |
| `basicLeavesDeliveredExactlyOnce` | Every basic response leaf occurs exactly once in complete, error-free delivery. |

Directive erasure preserves aliases, selection order, arguments, type conditions,
ordinary directives, and variable definitions/defaults. These are correctness
statements proved from the independent contract, not scheduler assumptions.
Liveness is conditional on a complete finite run, not a fairness theorem.

The reference implementation's public `ImplementationCorrect` in
`WorkQueueImplementation.lean` supplies these assumptions for actual queue/publisher
observations described by `queryScheduleMatches`, independently of the optional cursor
API. That operational predicate hides derived work, source validity, and admitted input
histories. It calls the shared `replayIncrementalResponse` implementation, without
assuming queue conformance or response correctness. Its completeness flag covers prefixes
and terminated outcomes; the accompanying block comment names the reusable correctness
witnesses instead of duplicating these statements. See the [implementation bridge](implementation.md#query-correctness).

## Proof status and verification

All 12 public query-correctness witnesses are proved against the current contract:
directive-free equivalence, finite outcome existence, safety, lifecycle, disjointness,
coverage, and reconstruction. The build, tests, and lint checks pass, including
`PublicStatements`, the auxiliary and specialized proofs, and the broader regressions.
The public-witness axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx` or added axioms.

The general mixed-work progress construction is checked. Historical causality agrees
with the current publication snapshot on an explained history, by
`Explains.nodeFailed_iff_snapshot` and `taskCancelled_iff_snapshot`; their forward
direction uses the proved exclusion of publications for failed or cancelled tasks.

`Tests.GraphQL.IncrementalDelivery.FailureCutBoundary` proves that a licensed
failure immediately after a child notice preserves the carrier's admission and the
explained history. The generic `Explains.record_failure` preservation theorem is checked
as well. Reference-implementation conformance, derived initialization, and the
implementation-to-query bridge are proved; their details and proof structure are in the
[implementation guide](implementation.md#work-queue-conformance).

| Public statement | Witness module (theorem name is the statement plus `_holds`) |
| --- | --- |
| `incrementalDirectiveFreeExecutionEquivalentToBasic` | `Correctness/Query` |
| `queryOutcomeExists` | `Correctness/QueryOutcomeExistence` |
| `deliveryIDsUnique`, `deliveryIDsEventuallyComplete`, `deliveryIDsCompleteExactlyOnce` | `Correctness/QueryIdentity` |
| `deliveryIDUsageValid`, `deliveryPatchesAnnounced` | `Correctness/QueryIDUsage` |
| `deliveryLifecycleValid` | `Correctness/QueryLifecycle` |
| `deliverySlicesDisjoint` | `Correctness/QueryDisjointness` |
| `deliveredResponsePositionsEquivalentToBasic`, `basicLeavesDeliveredExactlyOnce` | `Correctness/QueryCoverage` |
| `mergedExecutionEquivalentToBasic` | `Correctness/QueryReconstruction` |

Safety and disjointness cover all admitted prefixes, including failed/interrupted ones.
Liveness and lifecycle cover complete finite runs, including failures. Reconstruction,
basic-position coverage, and leaf-once retain the complete, zero-error boundary.
These guarantees are universal over admitted owner, completion-order, and batching
choices.
Existence instead constructs some complete outcome for every modeled query; it does not
assert that every prefix can complete or that every conforming implementation is fair.

### Proof structure

The public query witnesses are under
[Correctness](../../Proofs/GraphQL/IncrementalDelivery/Correctness). Their principal layers
are:

- **Execution and observation:** `RootExecution` relates pure completion to public root
  execution. `InputObservation` proves replay, composition, and batching laws.
  `SourceObservation`/`QueryObservation` recover admitted work histories;
  `SourceRealization`/`QueryRealization` realize them as actual observations.
  `WorkQueue.observes_inputs` and `executionFromWork_observes_replay` retain a specified
  queue constructor, not merely some equivalent source.
- **Identity, lifecycle, and errors:** queue `EventAccounting`, `EventLifecycle`, and
  `BatchLifecycle` derive notice freshness, open references, and terminal closure.
  Mapper and replay proofs transport them through ID allocation and both batching stages.
  `FailureReporting` derives an open owner for the first accepted failure;
  `TaskErrors` and `FailureCounts` connect complete zero-error observations to successful
  work publication.
- **Positions and reconstruction:** `SourcePositions` and metadata/cursor certificates
  connect task occurrences to response paths. Wire-decoder replay gives prefix
  disjointness.
  `SourcePublicationCoverage` and `RootSourceReconstruction` identify the successful
  inventory with basic execution. Attachment and merge proofs establish actual response
  reconstruction, not only position coverage.
- **Finite progress:** initialization, legal history extension, and a finite activity
  bound
  support `MixedExistence.mixed_completeRun_exists`. Its witness preserves supported
  notice coverage so outstanding work retains a usable announcement carrier.
  `QueryOutcomeExistence` derives all required metadata from execution and exposes
  `queryOutcomeExists_holds`.

`MixedExistence.mixed_supported_continuation` also extends an explained prefix with
supported notice coverage, preserving its notices and batches. This sufficient condition
is not required of every admitted prefix. The optional `History.CanFinish` and
`WorkQueue.Nonblocking` predicates distinguish a possible terminal extension from one
admitted by a particular source; see the [progress results](semantics.md#nonblocking).

Regressions cover overlapping owners, mixed defer/stream nesting, cancellation, errors,
empty streams, nonzero cursors, decoder composition, and actual wire realization.
`QueryOutcomeExistence` tests include generated alternating defer/stream work and invalid
roots; `MixedNoticeCoverage` checks both the notice-coverage boundary and a complete-run
witness.

See the [development guide](../development.md) for the verification workflow.

## Implementation boundary: shared publication owners

The contract constrains the effective publication owner after publisher normalization,
not the raw queue's triggering group. The reference publisher, proof-side owner adapter,
and shared-owner regressions are documented in the
[implementation guide](implementation.md#shared-publication-owners).

## Exhausted finite stream boundaries

`completeListValueWithStream` retains a stream boundary when `initialCount` is reached,
even if no item remains. For an active outer-list directive with a successfully completed
initial prefix, let `n` be `initialCount` and `L` the finite list length:

| Boundary | Generated work |
| --- | --- |
| `n < L` | A stream containing the remaining items. |
| `n = L`, including `0 = 0` | An empty stream boundary, with no item tasks. |
| `n > L` | No stream: exhaustion occurs before reaching the boundary. |

This matches the pinned GraphQL.js
[`completeIterableValue` handoff](https://github.com/graphql/graphql-js/blob/961747301cf70e59aead2d7a5121779a79a52877/src/execution/Executor.ts#L1038-L1076),
which tests the boundary before asking whether another item exists.
Other work can make the query incremental in every row. Failure in the initial prefix
retains normal null/error propagation and does not introduce a stream under a nulled
position.

Boundary generation belongs to the model's stream hook because the pinned draft does not
wire `@stream` into CompleteListValue. The draft's
[root algorithm](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%206%20--%20Execution.md#L385-L403)
chooses an ordinary response only when tasks and streams are empty, before queue creation.
An exhausted stream remains nonempty work: queue initialization cannot switch it back to
an ordinary response.

An empty stream has a key and a pending/completed lifecycle, but no item publications or
data positions. The contract permits that lifecycle without a synthetic end task.
Optional ignoring of active directives and coalescing later updates into the initial
payload remain outside the model.

[`EmptyStreams`](../../Tests/GraphQL/IncrementalDelivery/EmptyStreams.lean) proves exact
incremental outcomes for empty/exact-count lists and excludes ordinary outcomes for those
boundaries under every queue constructor. It also checks excess counts, aliases, labels,
disabled/skipped directives, synchronous inner lists, initial-prefix failure, nested
producers, and shared defer owners. This establishes the finite boundary behavior,
not full GraphQL.js refinement.

## Pinned draft gaps and editorial choices

- [Spec incompleteness] CompleteListValue does not wire in stream execution; the
  separately named stream hook implements the modeled directive/response behavior.
- [Spec incompleteness] CreateWorkQueue lacks an algorithm or complete invariant
  specification; the proposed contract makes the additional assumptions explicit.
- [Spec typo] ExecuteField's path wording uses field names where the response
  chapter requires aliases; the model uses response names.
- [Spec typo] The response chapter's final hasNext sentence repeats true;
  termination mapping uses false.
- [Spec ambiguity] Initial and later notices share the ID map despite ambiguous
  allocation scope in the draft.
