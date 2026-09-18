# Incremental Delivery

This guide documents the separate `GraphQL.IncrementalDelivery` model: its execution
interface, specification correspondence, scheduler assumptions, response correctness
statements, and proof status. For coverage without implementation details, see the
[conformance summary](spec-conformance.md#incremental-delivery-draft-covered).

The target is
[graphql/graphql-spec PR #1110 at 045e193](https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec),
not an unpinned latest draft. The specification references are:

- [Execution](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%206%20--%20Execution.md).
- [Response](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%207%20--%20Response.md).
- [Type System](https://github.com/graphql/graphql-spec/blob/045e19363c2b55f127960bd3b5e8072a15b29aec/spec/Section%203%20--%20Type%20System.md).

## Module boundaries and execution scope

| Public module | Responsibility |
| --- | --- |
| [Operation](../GraphQL/IncrementalDelivery/Operation.lean) | Incremental operation syntax, separate from the main operation model. |
| [Execution](../GraphQL/IncrementalDelivery/Execution.lean) | Pure finite resolver execution, deferred/streamed work, source interface, and response mapping. |
| [WorkScheduler](../GraphQL/IncrementalDelivery/WorkScheduler.lean) | Relational work accounting and proposed source invariants; imports only Execution. |
| [Correctness](../GraphQL/IncrementalDelivery/Correctness.lean) | Observations, wire properties, reconstruction, and public correctness propositions; imports WorkScheduler. |

WorkScheduler and Correctness are self-contained definition modules. Public definitions
do not import proof modules. Schema, resolver, input preparation, and ordinary response
primitives are shared with [the main execution model](execution.md).

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
`ExecutionResult` directly. An explicit `Execution.WorkScheduler` parameter supplies
the draft's unspecified CreateWorkQueue:

- With no incremental work, root execution returns `.single response`.
- Otherwise, it returns `.incremental initial subsequent`: an initial incremental
  result and a resumable `ResponseEventStream`.

`Response` remains the ordinary data/errors map shared with
`GraphQL.Execution.Response`. `ExecutionResult` is the generalized
ordinary-or-incremental query return type, broader than Section 7's ordinary
execution-result map. Request-error results and subscription streams are excluded.

`executeRootSelectionSetCore` computes initial data/errors and finite `Work`.
Resolver results and child work are precomputed pure outcomes, not host futures.
The scheduler varies their completion observations, not their underlying values.
Initial data/errors come from the execution core; pending notice identities, order,
and initial wire IDs come from source initialization and need not be independent of it.

Initialization abstracts waiting for the first result and consumes no subsequent
work-event batch. The model follows YieldIncrementalResults's unbatched initial envelope;
optional proxy coalescing of later updates into that envelope remains unmodeled.

### Partial sources and mapping

`WorkQueueResult` contains initial groups/streams and an opaque `EventSource` of
work-event batches. `WorkEvent` represents GROUP_VALUES, GROUP_SUCCESS, GROUP_FAILURE,
STREAM_VALUES, STREAM_SUCCESS, STREAM_FAILURE, and WORK_QUEUE_TERMINATION.

A source stores admissible/finished predicates and its observed history, not a future
trace. This intentionally partial state can admit several next batches. Hidden progress
states remain existential witnesses in the work contract; an unavailable next batch
does not imply source termination.

`mapIncrementalWorkEventsToResponseEvent` installs a resumable mapper separate from
task accounting. The mapper owns `IDState`, `ensureID`, `getPendingEntry`,
`getIncrementalEntry`, `getCompletedEntry`, and
`getIncrementalStreamUpdateResult`. Initial and later notices share one ID supply.

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

## Spec-facing execution definitions

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
| `executeExecutionPlan` / ExecuteExecutionPlan | Takes newDeferUsages and an already-built ExecutionPlan. Extend the defer map, execute immediate fields, collect execution groups, append work. It never calls BuildExecutionPlan. Pure evaluation is sequential; bubbling failure discards/cancels unexposed sibling work. |
| `collectExecutionGroups` / CollectExecutionGroups | Look up each partition's fragment owners, construct its ExecuteExecutionGroup task, accumulate tasks. Finite pure task outcomes replace future computations; no completion order is selected. |
| `executeExecutionGroup` / ExecuteExecutionGroup | ExecuteCollectedFields returns data, counted errors, and child work. Deferred errors remain task-local until their delivery boundary. |
| `executeCollectedFields` / ExecuteCollectedFields | Take the first grouped field, look up its schema definition, call ExecuteField, insert its value under responseName, accumulate work. Invalid groups/schema misses still produce counted errors, rather than implementing the spec's skip-undefined branch; validation is excluded. |
| `executeField` / ExecuteField | Read the first field, coerce arguments, resolve, CompleteValue. Returns a completed value and work, not a response-map slice. The caller-provided FieldDefinition bundles the spec's fieldType with argument definitions needed by the shared coercion helper. Explicit responseName gives alias-correct paths. |
| `completeValue` / CompleteValue | Fuel-bounded non-null/null/list/leaf/composite cases. Composite completion explicitly calls CollectSubfields, BuildExecutionPlan, then ExecuteExecutionPlan. Leaf coercion/runtime type resolution retain the shared model's projections. List dispatch includes the separately named stream extension below. |
| `completeListValue` / CompleteListValue | Complete each item at its indexed path and accumulate values/work. An explicit index carries the loop counter, normally starting at zero. This algorithm itself does not initiate streaming. |
| `executeRootSelectionSet` / ExecuteRootSelectionSet | The model-only core performs CollectFields, BuildExecutionPlan, ExecuteExecutionPlan. The root then extracts data/errors, checks for work, calls YieldIncrementalResults, and batches the subsequent stream. The ordinary/incremental branch is inline, with no public executionFromWork wrapper. |
| `executeQuery` / ExecuteQuery | Query-only entry point calling root execution. The explicit-fuel variant also materializes variable defaults and checks root-source applicability, inherited model entry-point conventions. Default-fuel calculation and arbitrary-invalid-root errors are not spec steps. |
| `yieldIncrementalResults` / YieldIncrementalResults | Call the supplied CreateWorkQueue factory, create initial pending notices, return the initial result plus the resumable work-event mapper. Waiting for initialization is abstracted; no future batch is selected or consumed. |
| `mapIncrementalWorkEventsToResponseEvent` / MapIncrementalWorkEventsToResponseEvent | Install a lazy mapper over admitted batches, threading the ID map when an observation is accepted; the seven-case per-batch loop is factored as mapWorkEventBatch. Initial and later notices share IDs despite the draft's allocation-scope ambiguity. |
| `ensureID` / EnsureID | Reuse the node ID or allocate the next decimal string and increment the supply. |
| `getPendingEntry` / GetPendingEntry | Ensure IDs and build notices, groups before streams; one map over concatenated lists represents the two spec loops. |
| `getIncrementalEntry` / GetIncrementalEntry | Ensure the chosen group's ID, include data/errors, drop its path prefix to obtain subPath. |
| `getCompletedEntry` / GetCompletedEntry | Ensure the node ID and include counted completion errors. Callers pass zero for omitted errors. |
| `getIncrementalStreamUpdateResult` / GetIncrementalStreamUpdateResult | Package hasNext and the three entry lists. Empty lists encode omitted optional entries; this is a typed result, not a JSON serializer. |
| `batchIncrementalResults` / BatchIncrementalResults | Return a new stream over nonempty available groups of upstream inputs. Map the upstream events in order, concatenate response lists, and take the final hasNext. No batching flag or selected future suffix; host readiness/clocks are not modeled. |

The two planning call sites are the root core and CompleteValue's composite branch:
both perform collection → BuildExecutionPlan → ExecuteExecutionPlan explicitly.
Work is a finite tree, not the spec's literal groups/tasks/streams record: append retains
the work components and the semantic work compiler identifies shared fragment owners.
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

- `EventSource`: opaque admissible/finished predicates and the already-observed history. The state is partial, admitting multiple future continuations; it is not a complete schedule or a required task-ledger representation.
- `Execution.WorkScheduler`: explicit factory supplying the result of CreateWorkQueue. No effect-program syntax or interpreter is needed for this pure functional model.
- `WorkQueueResult`: the initial groups/streams and event-stream result expected by the spec's undefined CreateWorkQueue.
- `WorkEvent`, `GroupValue`, `StreamValue`: typed versions of the seven named event forms and their successful payloads.
- `IDState`: the mapper's idMap and nextID, separate from scheduling.
- `mapWorkEventBatch`: factors the spec's per-batch loop from its surrounding stream map.
- `ResponseEventStream`, `ResponseEventStream.Accepts`, `ResponseEventStream.next`: the mapper's responseEventStream, represented by a source input type, partial source history, mapper IDs, and an event-mapping function. Observation supplies one admitted input and updates state functionally. Batching transforms the input type to a nonempty group of upstream inputs and installs the spec's aggregation function.
- `combineIncrementalResults`: the list-entry concatenation and final hasNext rule used by the spec's batching stage.
- `executeRootSelectionSetCore`: factors the first three root steps, preserving their order and distinct call boundaries.
- `getStreamUsage`, `streamInitialCount?`, `completeListValueWithStream`, `completeStreamItems`: finite implementation of the stream directive/response contract where the pinned execution algorithm lacks a hook. These are explicitly not named spec algorithms. The outermost-list rule and fresh item delivery boundaries belong to this extension.
- `rootSourceAppliesBool`, `executeQueryWithFuel`, `executeQueryFuelBound`: inherited entry-point checks and explicit/default finite-completion controls, not extra normative query steps.
- `directiveAllowsSelectionBool`, `selectionDirectivesAllowBool`, `directiveLabel?`, `activeDefer?`: the collection algorithm's directive checks and typed label extraction.
- `addExecutableGroup`, `mergeExecutableGroups`, `FieldCollection.append`: list-backed ordered-map accumulation for collection.
- `deferUsageSetsEquivalent`, `addExecutionPartition`: finite set equality and partition-map insertion used by BuildExecutionPlan.
- `freshExecutionKey`, `lookupDeferredFragment?`: explicit occurrence identity supply and defer-map lookup, not scheduler choices.
- `Completion.pure`, `error`, `combine`, `map`, `catchNull`, `nonNull`: typed data/work/error propagation replacing pseudocode return values and raised errors.
- `Work.size`, `Work.itemsSize`: finite structural accounting, also used to recognize an empty work tree.
- `EventSource.Allows`, `advance`, `IsFinished`, `ofList`, `batch`: observation-state plumbing, fixed finite fixture sources, and nonempty order-preserving grouping. Every intermediate prefix must be admitted; no available output does not imply termination. Grouping starts at the current source position without replaying prior events.

The remaining structures and aliases name typed spec concepts or representation machinery:
DeferUsage, ExecutableField, CollectedFieldsMap, FieldCollection, ExecutionPlan,
ResponsePathSegment/ResponsePath, DeliveryNode, DeferredFragment/DeferMap, Work,
Completion, StreamUsage, DirectiveLabel, and response-entry/result types. `Response`
retains the ordinary data/errors map shared with `GraphQL.Execution.Response`.
`ExecutionResult` names the generalized ordinary-or-incremental query return type, not
Section 7's narrower ordinary execution-result map. Request-error results and subscription
streams are excluded.
Shared resolver/value/coercion/error primitives are re-exported from GraphQL.Execution;
their existing scope is unchanged. Representation helpers do not claim normative names.

`executionFromWork` exists only in
[`Proofs/.../Correctness/RootExecution.lean`](../Proofs/GraphQL/IncrementalDelivery/Correctness/RootExecution.lean).
Its direct-result equation factors the public root branch for proofs, without an effect
program. `Semantics/FieldExecution.lean` contains a checked response-field decomposition
for induction. Neither helper is called or imported by public definitions.

## Opaque scheduler and proposed invariants

The pinned draft does not define CreateWorkQueue. The work-accounting contract
therefore completes an underspecified interface; it is not a literal spec algorithm
or an already-proved characterization of every conforming implementation.

`WorkScheduler.lean` separates accounting from a **Proposed WorkQueue invariants**
section. The factory type is `Execution.WorkScheduler`; the accounting definitions
live in the distinct `GraphQL.IncrementalDelivery.WorkScheduler` namespace.

### Source contract

`WorkQueueResult.Conforms` combines four independently named premises:

| Premise | Requirement |
| --- | --- |
| `Initialized` | Fresh initialization with an admitted empty observation history. |
| `PrefixClosed` | Every prefix of an admitted history is admitted. |
| `AccountsForWork` | Every admitted history satisfies `AdmissiblePrefix` or `AdmissibleRun` for the submitted work. |
| `TerminationMatchesWork` | Finished histories are exactly admitted terminal work runs. |

`Execution.WorkScheduler.Conforms scheduler work` applies these premises only to
that nonempty work. Query observations require conformance for the work actually
submitted; ordinary responses and invalid roots need no law for their unused source.
A global requirement over every raw Work would include impossible initializations,
including the unused empty-work case.

`specificationSource` admits every contract history for explicit initial notices;
`specificationScheduler` takes the initialization choice as a parameter. Neither
chooses a future completion order. `specificationSource_conforms` proves conformance
for valid initial notices; invalid notices are not repaired. There is no global
scheduler axiom or default queue policy.

### Work accounting

Admission is a relation over output histories, not an internal queue or progress
machine. `ValidHistory` admits an interrupted prefix or complete run.
`AdmissibleNext work history batch` checks a nonempty extension of a valid,
nonterminal history. Multiple next batches may be legal; none is selected by execution.

Structural `Occurrence` addresses distinguish deferred results and stream-item
positions. `Located`, `TaskAt`, and `NodeAt` relate those positions directly to
the original Work, retaining contributing owners, producers, and ancestry.
They are ordinary definitions over one `locateWork` address traversal; its
`WorkLocation` return value is just the located subwork and its static context.
Node lookup retains every descriptor, including repeated keys. `StructuralEquivalence`
proves these definitions equivalent to the former structural inductives for all raw work.
There is no compiled graph, allocated task record, mutable ledger, synthetic
stream-end task, or done/published/announced/closed progress structure.

`Explains` supplies one output-to-occurrence matching for the entire observed
history and a causal failure explanation. `EventAllowed` checks each atom
against its preceding output prefix. Notices and closures are derived from the
outputs themselves. The explicit rules completing the queue interface are:

- Publication is fresh and follows the producer's value and the preceding stream item.
- A shared object result chooses one available longest-path owner; ties remain possible.
- Group release observes defer ancestry; stream release observes successful owners.
- A failure witness names real failing occurrences reachable through successful producers.
- Each recorded failure has an announced, still-open contributing owner at its cut.
- Failure/cancellation propagates through unavailable producers and failed dependencies.
- Successful closure accounts for the node's contributing work.
- Terminal histories account for all work and all announced nodes before termination.

Failure can precede its output notification. An existential ordered list of
`(output cut, failing occurrence)` pairs records only the evidence needed to
explain that possibility. Cuts are bounded by the current history, not host time
or a selected future. Each failure must be fresh and not cancelled by earlier
failure evidence, and have an open contributing owner in the observed prefix at its cut.
This release requirement prevents an unannounced failed group from disappearing through
cancellation without any failure completion. One owner suffices for shared work; other
owners may remain unannounced, and failure notification may still be delayed.
Least causal `NodeFailed` and `TaskCancelled` judgments exclude
self-justifying failure cycles. Those two public predicates wrap a small `Causality`
kernel whose rules use named structural projections for owners, producers, and
dependency keys. `Reachable` is a single inductive alongside the structural projections,
independent of failure propagation, with no public alias. Failed and cancelled producers
are explicit cases, without a separate producer-unavailability judgment.
`FailureEquivalence` proves failure/cancellation equal to the preceding three-judgment
presentation and preserves producer-chain reachability for arbitrary raw work.

`DependencySatisfied` includes absent or unannounced accounted-for dependencies;
it does not require a success notification. It reuses `NodeHasProducer` for node absence;
`NodeAccounted` reuses `TaskHasOwners` for contributing work. `EventAccounting` proves
these conditions equivalent to their full-descriptor formulations. Owner selection
and announcements still inspect full node metadata. `CanAnnounce` expresses notice readiness.
`Announcements` permits alternative fresh eligible frontiers; `ValueGrouping`
and `WorkBatching` preserve ordered aggregation. None of these relations allocates
wire IDs or consults response correctness.

No lifecycle checker, disjointness claim, merge-success test, or equality to basic
execution is an admission filter. A counterexample must expose a missing requirement
or a model bug, not be excluded by assuming the desired correctness property.

See [scheduler design and research](incremental-deliver-scheduler.md) for the
trace-semantics rationale, alternatives, failure abstraction, and open obligations.
Equivalence to the removed graph/transition contract is not established; in
particular, erasing successful silent completions and synthetic stream-end tasks
requires a normalization argument. Commit `4af5c80` retains the old presentation.

### Finite progress domain

`AdmissiblePrefix` permits interrupted or stalled finite observations.
`AdmissibleRun` additionally accounts for work and emits termination. A stalled
source need not be finished, and an implementation need not realize every permitted
choice. Complete finite runs do not assert fairness or eventual completion of real
resolver futures. Infinite execution and host-future termination are not modeled.

## Observations and correctness

`Correctness.lean` defines wire/query observations, response positions, lifecycle
checks, reconstruction, and public correctness propositions. The query propositions
live in `GraphQL.IncrementalDelivery.Correctness`.

`ResponseEventStream.Observes` repeatedly accepts batches and updates stream state.
`ExecutionResult.Observes` relates execution results to finite `QueryResult`
observations; its complete flag additionally requires source termination.
`queryObservation` quantifies over factories conforming for the query's actual work.
`queryOutcome` is its complete-observation case. There is no canonical query trace
or executable schedule enumerator.

### Wire positions, lifecycle, and reconstruction

`QueryResult.DeliversSlices` states that the deterministic `QueryResult.decodeSlices`
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
precede completions. Lifecycle validity additionally requires every announcement
to close and hasNext to describe subsequent responses, not currently open IDs.
The last ID may close before a separate termination-only response. Missing
termination, premature hasNext false, duplicate IDs/completions, and closed-ID
patches remain invalid.

`mergeQueryResult` reconstructs data from ID-resolved paths. It rejects incomplete
or malformed lifecycles and patches at missing or incompatible attachment points.
Data patches do not count errors: the reconstructed envelope uses
`QueryResult.totalErrors`, counting initial, patch, and completion errors once.
Failed shared groups can report errors under multiple IDs; the count-only model
does not deduplicate error identities.

`executionComplete` requires complete delivery and zero counted errors. Failure
may discard undelivered data; initial null bubbling can cancel work before any
ID is announced, and fuel exhaustion counts as an error. Thus ID closure alone
is not enough for comparison with ordinary execution. This premise does not
assume successful merging, attachment order, or response equivalence.

For admitted complete query outcomes, lifecycle validity is already proved. The three
basic-execution comparison statements therefore assume only `result.totalErrors = 0`
in addition to `queryOutcome`, not a separate `executionComplete` certificate.
`queryOutcome_executionComplete_iff` proves these premises equivalent on that domain;
the raw-trace `executionComplete` predicate remains unchanged.

### Public statements

| Statement | Observation domain and claim |
| --- | --- |
| `incrementalDirectiveFreeExecutionEquivalentToBasic` | Syntactically directive-free operations return the basic response for every factory, without a conformance premise. |
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
statements to prove from the independent contract, not scheduler assumptions.
Liveness is conditional on a complete finite run, not a fairness theorem.

## Proof status and verification

**All 12 public query-correctness statements have checked witnesses** through
`Proofs.GraphQL.IncrementalDelivery.Correctness`. The public existence statement
`queryOutcomeExists` packages the general finite-progress theorem alongside the
11 safety, lifecycle, and response-correctness statements. No response-correctness
predicate or progress requirement was added to scheduler admission.
`Tests.GraphQL.IncrementalDelivery.PublicStatements` checks every witness against
its exact public proposition.

Whole-project `lake build` and `lake lint` pass. The public witnesses use only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional
axioms are used.

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
These guarantees are universal over admitted owner, completion-order, and batching choices.
Existence instead constructs some complete outcome for every modeled query; it does not
assert that every prefix can complete or that every conforming implementation is fair.

### Execution, histories, and actual observations

`RootExecution` connects direct-result root execution to proof-only work packaging.
`executeQueryWithFuel_initialResponse_independent` shows that initial data/errors do
not depend on the factory, even without conformance. `Query` proves directive-free
equivalence, including the default-fuel entry point, by showing that execution produces
no incremental work.

`InputObservation` characterizes finite stream observations as replay of supplied inputs
with an exact residual stream. Its append/split and batching laws retain all intermediate
admitted prefixes, prior source history, nonempty response groups, and termination.
These folds replay observations; they do not select futures.

`SourceObservation` and `QueryObservation` recover independently admitted work histories
from actual mapper/query observations. `SourceRealization` and `QueryRealization` prove
the converse, including arbitrary nonempty response grouping, ordinary responses, and
invalid roots. The main interfaces are `workObservation_iff_realizable` and
`queryObservation_iff_workHistory`. `WorkObservation` and `replayResponse` are proof-only
witnesses, not extra execution semantics.

`HistoryPrefixes` proves history prefix closure, truncating failure cuts without losing
earlier causes. `SpecificationSource` proves maximal-source and operation-local factory
conformance for supplied valid initial notices. Realization alone does not imply that
a terminal history exists; the independent progress proof below supplies one.

### Identity, lifecycle, and errors

`WorkScheduler/EventAccounting`, `EventLifecycle`, and `BatchLifecycle` derive notice
freshness, open-key references, unique completion, and finite-run liveness directly from
admission. `ValueGrouping` and work batching preserve notice occurrences up to permutation;
stream coalescing need not preserve notice order inside a batch.

`MapperIdentity`, mapper reference/metadata proofs, and `ResponseReplay` transport those
facts through stable injective ID allocation, actual event mapping, and response batching.
`QueryIdentity`, `QueryIDUsage`, and `QueryLifecycle` finish the public witnesses.
Termination-only responses after the last ID closes remain permitted: final `hasNext`
tracks future responses, not merely currently open IDs.

`IDUsageProperties`, `LifecycleProperties`, and `LifecycleControl` separately explain
the Boolean wire checkers. Safety gives uniqueness and causal references; safety plus
liveness gives exactly-once completion. `ResponseMerging` proves that successful merging
preserves total errors and implies lifecycle validity. These conditional wire lemmas are
not scheduler premises.

`ExecutionErrors` certifies positive bubbling failures in generated work. `TaskErrors`,
`FailureReporting`, `FailureCounts`, and `ErrorCounts` preserve actual failure counts
through work/value/response grouping. `SuccessfulWork` and `PublicationCoverage` then
derive a failure-free explanation and exactly-once publication of every task from a
complete zero-error observation. Raw work may encode zero-count errors; generated-work
positivity is derived, not imposed on raw admission.

### Positions and response reconstruction

`SourcePositions` supplies disjoint source paths and coherent cursor seeds.
`WorkMetadata`, `MapperMetadata`, and `NoticeMetadata` identify selected owners,
pending paths, stable IDs, and object subpaths. `PublicationPositions`,
`StreamCoordinates`, and `HistoryStreamCursors` connect occurrence-labelled publication
to ordered stream positions, including nonzero initial cursors and nested streams.

`HistoryAbsolutePositions`, `WorkPatchShapes`, `WirePositionReplay`, and
`ResponsePositionDecoding` connect those source positions to the public deterministic
wire decoders. `PositionComposition` proves decoder append/inversion equations, retaining
residual cursors and earlier notices. `QueryDisjointness` concludes global path uniqueness
for every admitted prefix/run, including failures.

`SourcePublicationCoverage` identifies successful terminal publications with the complete
source inventory. `SourceSuccess`, typed source-reconstruction modules, and
`RootSourceReconstruction` identify that inventory with ordinary directive-erased
execution. `QueryCoverage` proves position equivalence and leaf-once using ordinary
response-path uniqueness.

`SourceAttachments` and `SourceExecutionAttachments` establish parent-container
availability; `HistoryAttachments` transports it through producer-before-child order.
`TypedCursorAgreement` relates list cursors to actual lengths, and `HistoryMerging`
proves successful merging. `WireAtomMerging` handles ID lookup and both batching stages.
`QueryReconstruction` combines these facts with typed inventory equivalence and error
conservation to prove actual response equivalence, not merely position coverage.

### Finite progress and complete-outcome existence

The general proof has the following dependency layers:

1. `Initialization` derives valid initial notices from generated ancestry, continuity,
   and fresh stream regions. `QueryExistence.initializedScheduler` demonstrates
   initialization nonvacuity independently of completion.
2. `HistoryExtension`, `PublicationExtension`, and `FailureExtension` construct actual
   permitted continuations, preserving old evidence. `CompletionExistence` closes all
   remaining IDs and emits termination once every task is accounted for; it also supports
   selective closure while reserving another group as a future notice carrier.
3. `FiniteHistories` bounds observable activity by a finite inventory of publication
   occurrences and completion keys. `TaskReadiness` and `DependencyKeys` supply
   well-founded producer/item descent. `OwnerAvailability` constructs a step when a
   ready task has an announced healthy owner; `LeastKeyProgress` finds a least such
   outstanding key.
4. `NoticeFrontiers` and `NoticeCoverage` construct covering initialization and actual
   group-success/stream-item carriers. `GroupAccounting` proves that a healthy accounted
   defer group has a published contributor, without assuming each cancelled task's
   owners fail.
5. `MixedNoticeMetadata`, `MixedNoticeCoverage`, and `MixedNoticeExtension` establish
   proof-only supported coverage. A stream may wait until one defer parent and its full
   ancestry are satisfied. Full ordinary notice coverage is too strong: legitimate
   silent co-owner accounting can make a stream eligible during an object publication
   which cannot carry notices. Public admission still permits that earlier notice.
6. `MixedProgressEvents` preserves supported coverage across actual success/failure and
   completion events. `MixedExistence.mixed_completeRun_exists` maximizes a finite
   supported history. Healthy accounted keys can close; a least outstanding owner has
   full support and must already be announced, so its ready task would extend the
   history. This contradiction accounts for every task, and finalization supplies a run.
7. `QueryOutcomeExistence` obtains all metadata from execution and proves
   `executeRoot_completeRun_exists`, `executeRoot_completeObservation`, and
   `queryOutcome_exists`. `queryOutcomeExists_holds` exposes the last result at its
   public proposition, with no shape, validation, success, history, or scheduler premise.

The constant defer-role assignment specializes mixed progress to
`DeferOnly.completeRun_exists`; singleton and root-singleton work results specialize it
further. All four shape-restricted query interfaces are compatibility wrappers around
unconditional query existence. Their existing names and parameters are retained.

Raw-work results with genuinely weaker assumptions remain independent.
`NestedStreamExistence` needs only stream shape and owner paths, while
`StreamContinuation` preserves a supplied prefix under its reached-state conditions.
`DeferredStreamExistence`, `DeferredPhase`, and `InitialDeferredExistence` retain
useful phase/metadata boundaries. Replacing them with the general theorem would add
premises, so they are not treated as redundant.

`completeObservation_exists_iff` and
`completeObservation_exists_iff_accounted_history` retain the exact raw-work existence
boundary. None of these results guarantees completion of every admitted prefix,
fairness, host-future termination, or equivalence to the removed graph scheduler.

`MixedExistence.mixed_supported_continuation` additionally extends an existing explained
prefix with supported notice coverage, preserving its notices and supplied batches.
Optional `History.CanFinish` and `WorkQueueResult.Nonblocking` distinguish viability in
the contract from continuation within a particular source; neither strengthens `Conforms`.
Proof-only `viableSource` supplies a nonblocking reference language, while a missing-notice
counterexample shows that conformance alone is insufficient. The scheduler research guide
records the checked [progress, minimality, and local commutation results](incremental-deliver-scheduler.md#checked-research-results),
including the distinction between accounting equivalence and ordered wire equality.

Regressions cover overlapping owners, arbitrary fixed outcomes, cancellation, absent
ancestor placeholders, empty streams, nonzero cursors, decoder composition, and actual
wire realization. `Tests/.../QueryOutcomeExistence` inspects generated
defer/stream/defer/stream paths with shared producers, produced defer failures, stream-item
failures, exhausted fuel with nonempty work, and invalid roots.
`Tests/.../MixedNoticeCoverage` retains both the full-coverage counterexample and its
complete-run witness.

### Focused checks

Definition-only regression modules cover execution branches, supplied-plan boundaries,
partial sources, response mapping/batching, relational scheduler choices, and wire
correctness examples. These focused checks supplement the whole-project build:

```sh
lake build GraphQL.IncrementalDelivery \
  Tests.GraphQL.IncrementalDelivery.Execution \
  Tests.GraphQL.IncrementalDelivery.SpecInterfaces \
  Tests.GraphQL.IncrementalDelivery.Sources \
  Tests.GraphQL.IncrementalDelivery.Correctness \
  Tests.GraphQL.IncrementalDelivery.PositionDecoding \
  Tests.GraphQL.IncrementalDelivery.WorkScheduler
```

The correctness proofs and their proof-interface regressions are checked separately:

```sh
lake build Proofs.GraphQL.IncrementalDelivery.Correctness \
  Tests.GraphQL.IncrementalDelivery.Query \
  Tests.GraphQL.IncrementalDelivery.WireProperties \
  Tests.GraphQL.IncrementalDelivery.SourceObservation \
  Tests.GraphQL.IncrementalDelivery.QueryObservation \
  Tests.GraphQL.IncrementalDelivery.WorkLifecycle \
  Tests.GraphQL.IncrementalDelivery.HistoryScheduling \
  Tests.GraphQL.IncrementalDelivery.QueryDisjointness \
  Tests.GraphQL.IncrementalDelivery.QueryCoverage \
  Tests.GraphQL.IncrementalDelivery.QueryReconstruction \
  Tests.GraphQL.IncrementalDelivery.PositionComposition \
  Tests.GraphQL.IncrementalDelivery.Realization \
  Tests.GraphQL.IncrementalDelivery.QueryOutcomeExistence \
  Tests.GraphQL.IncrementalDelivery.PublicStatements
```

The broader proof/test aggregates and whole-project lint also pass. See
[development](development.md) for general repository commands.

## Pinned draft gaps and editorial choices

- CompleteListValue does not wire in stream execution; the separately named
  stream hook implements the modeled directive/response behavior.
- CreateWorkQueue lacks an algorithm or complete invariant specification;
  the proposed contract makes the additional assumptions explicit.
- ExecuteField's path wording uses field names where the response chapter requires
  aliases; the model uses response names.
- Initial and later notices share the ID map despite ambiguous allocation scope
  in the draft.
- The response chapter's final hasNext sentence repeats true; termination mapping
  uses false.
