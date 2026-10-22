# Reference work-queue implementation

The executable reference machine was based on GraphQL.js `v17.0.1` at
[`9617473`](https://github.com/graphql/graphql-js/tree/961747301cf70e59aead2d7a5121779a79a52877).
Retained-outcome handling and failure reporting are now compared against the repaired
implementation at
[`4a9b312`](https://github.com/graphql/graphql-js/tree/4a9b3121e65cc9c758109b2b6fec8d29f9a5b99b).
Its authoritative target is the incremental-delivery draft at
[`045e193`](https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec),
interpreted through the independent [work-queue contract](semantics.md).
This is a Lean reference implementation with conformance proof modules, not a formal
refinement of JavaScript source or its async runtime.

The work-queue contract requires a positive-error completion covering each cancelled
task's response attachment before termination. Failed completions select a supported
causal explanation instead of summing all contributing failures. Reference conformance,
the implementation/query bridge, all twelve established public query-correctness witnesses,
and finite complete-query-outcome existence are proved with the same public premises.
The completion, replay, recording, and regression modules use the selected-cause definitions.

`TaskOutcome` retains collected diagnostics and a selected boundary cause separately.
`BoundaryErrorCounts` follows caught nulls, non-null rethrow, field/list completion and
nested work. `ExecutedWork.taskFailure_count` and `nodeFailureCause_count` show that
execution-generated failed boundaries select one primitive error. Raw work can carry
other positive counts; no global singleton-error law is imposed on queue admission.

The executable queue stores rejection on `TaskNode`, preserving dormant memberships and
pending counts for later replay in task registration order. It has no group-level failure
or provenance cache and no runtime healthy-owner guard. `TaskEligibility`, unique group
and computation keys, `TaskOwnerFrame`, and complete drain proofs establish the source,
registration, ownership and retirement invariants. `ActiveRejectionReplay` shows that
active groups have no replayable retained rejection at a handler boundary.

`RetainedFailures` certifies surviving rejected computations and their contributing
memberships. Counter proofs distinguish successful group settlements from all received
outcomes. Semantic health excludes supported rejections on healthy contributors.
Notice contents require nonempty memberships, registered task provenance, successful
producer prerequisites and exclusion of earlier publication. Subtree cleanup and late
registration preserve cancellation evidence through taskless ancestor records.

Present-task source labels retain every received rejection, including causally redundant
ones. `SelectedFailureCuts` chooses informative object cuts in proof evidence without
changing executable handling. `SelectedFailureCauses` and `InformativeFailureInventory`
preserve supported positive completion causes and group invalidation. Successful-item
safety licenses that same ordered inventory; canonical publication, control admission
and terminal reporting use its common history and matching.

Finite progress uses `OpenFailureCauses` to justify failed open completions and
`StreamNoticesSupported` to preserve stream dependency support at actual notice carriers.
Execution-derived stream allocation uniqueness supplies descriptor agreement. The mixed
continuation and complete-run proofs derive these certificates without changing the
public query statements or source contract. Raw existence fixtures state the required
positive-failure premises explicitly.

Shared-owner regressions cover retained diagnostics, task-order cause selection, late
rejections, cancelled-parent registration, buffered producer publication, both host
batchings and rejection of invented aggregate counts. Failure scope coverage uses
observable positive completion scopes and remains separate from internal cancellation.

## Code and reading order

- [WorkQueueImplementation.lean](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean)
  contains all public implementation definitions in
  `GraphQL.IncrementalDelivery.ReferenceWorkQueue`.
- [Observation.lean](../../GraphQL/IncrementalDelivery/Observation.lean) supplies the shared
  observation and query-local conformance predicates. The public implementation imports
  this module, not `Correctness` or any proof module.
- [Implementation proofs](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation)
  are topic-based modules collected by the
  [proof aggregator](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation.lean).
- [ReferenceCorrectness](../../Tests/GraphQL/IncrementalDelivery/ReferenceCorrectness.lean)
  checks the public bridge, shared replay, and representative response behavior.

Read the executable pipeline and source assumptions below before the conformance proof.
The [execution guide](README.md) gives the spec cross-reference and public query theorems.

## Executable pipeline

```text
Host GraphEvent batches (values, errors, child work)
    → State.handleGraphEvents: queue state + raw WorkQueueEvent batches
    → IncrementalPublisher: effective-owner selection + normalized events
    → spec response mapper: pending, incremental, completed, hasNext
```

Inputs describe settlements, not publications. A settlement can remain buffered, emit
several events, or emit nothing immediately. Independent settlements can arrive in
different orders or batches; the state machine processes each observation sequentially.
There is no simulated async runtime, chosen future trace, or host-time model.

`Execution.WorkQueueEvent`, `ExecutionGroupValue`, and `StreamItemValue` are shared types.
Raw and normalized events have the same representation but different owner semantics.
Value lists support multi-task group flushes and multi-item stream updates. The abstract
contract checks singleton atomic publications and relates them to emitted batches through
`WorkBatching`; it does not restrict wire updates to a single value.

### Work representation

`Execution.Work` is a finite structural tree containing pure resolver outcomes.
Each task/item stores `TaskOutcome.result` with collected diagnostics and a separate
`cause`. `TaskAt` and `GraphEvent.MatchesWork` use `TaskOutcome.deliveryResult`: successful
payloads keep all diagnostics, while failed payloads report their selected explanation.
Implementation `Work` has GraphQL.js-shaped `groups`, `tasks`, and `streams` collections:

| Record | Contents |
| --- | --- |
| `Group` | Delivery node and immediate defer-parent reference. |
| `Task` | Structural task occurrence and all contributing delivery groups. |
| `Stream` | Delivery node; subsequent items arrive through host events. |

`Work.fromExecution` lowers only the immediate boundary: it traverses `combine` nodes,
but does not integrate a task's children or a stream's items. Successful host events
supply separately lowered child work. `taskChildWork?`, `taskGroups?`, and
`streamItemWork?` check that data against the original execution tree. Queue task/stream
records contain bookkeeping, not resolver computations or retained execution subtrees.

Each contributor supplies its full ancestor chain as parent-first registration candidates,
including taskless defer groups. `Task.groups` contains only actual contributors.
`State.registeredGroups` prevents repeated descriptors from recreating retired nodes;
`State.cancelledGroups` separately retains failure retirement. A child of a cancelled
parent is registered as cancelled without a live node. Successful retirement does not
cancel later descendants.

### Host events

| GraphEvent | Payload and meaning |
| --- | --- |
| `taskSuccess` | Task occurrence, object data, path, counted errors, contributor descriptors, and child Work. |
| `taskFailure` | Task occurrence and its selected delivery-failure count. |
| `streamItems` | Stream descriptor and a nonempty ordered batch of item occurrences, values, counted errors, and child Work. |
| `streamSuccess` | Exhaustion after all modeled items. |
| `streamFailure` | Stream descriptor and the error count of its next failing item. |

`ExecutionGroupValue.deliveryGroups` is implementation metadata, not a wire field.
`GraphEvent.MatchesWork` checks it against the task's actual contributors before publisher
selection. Abstract admission derives ownership directly from Work and ignores this
annotation, as does response mapping after owner selection. Contributor lists alone do
not identify task occurrences; the proof separately constructs publication provenance.

### State and transitions

`State` holds active roots, live group/task nodes, registration and cancellation references,
started task/stream descriptors, initial notices, and a termination flag. `GroupNode`
stores child links, task memberships, and pending count, matching GraphQL.js's group
bookkeeping. `TaskNode` stores its task, an optional settled value, a retained rejection,
and produced child streams. The rejection represents the cache on GraphQL.js's task
`Computation`; there is no per-group failure cache or stored failure-origin occurrence.
`rejectedTask?` inspects group tasks in registration order for release-time replay.
Finite lists implement keyed maps and ordered sets.

`State.initialize` integrates immediate work, prunes taskless group shells, starts the
remaining roots, and records initial notices. Starting work records eligibility for host
events; it does not run a promise or iterator.

| Transition | Behavior |
| --- | --- |
| `taskSuccess` | Ignore removed tasks; otherwise store the value, integrate children, and decrement each surviving contributor. Flush released zero-pending groups, start released work, and replay retained rejections. |
| `finishGroupSuccess` | Publish stored values once, remove shared memberships, close the group, and promote children/streams. |
| `taskFailure` | Retain the task's rejection and close its active owners. Dormant owners keep the task and its pending count for later replay. |
| `drainReadyGroups` | Replay retained task rejections in group task order, closing all active owners of the rejected task; otherwise close zero-pending groups and start released work. |
| `streamItems` | Integrate item children, activate roots, emit items and new notices, then drain ready groups after the carrier event. |
| `streamSuccess` / `streamFailure` | Close the active stream without retroactively cancelling work released by earlier published items. |
| `handleGraphEvents` | Process the batch in order and emit termination when both root collections are empty. A terminated state absorbs later calls. |

`pruneEmptyGroups` tests empty task membership, not merely a zero pending count:
settled values or rejected computations may still await release.
`removeGroup` cancels dependent descendants while retaining tasks with surviving owners.
Missing stale child links do not consume its live-node traversal budget.

Both task handlers use task-node presence, as GraphQL.js does. Removing the final owner
removes that node, so later callbacks have no effect. A surviving dormant owner retains
its shared task even after another owner closes. Semantic failure/cancellation evidence
belongs to the independent history contract; it is not an extra runtime health gate.

### Publisher and shared replay

`IncrementalPublisher` stores the mapper's ID state separately from live notices. Closed
IDs remain allocated, but only open contributors participate in `getBestIdAndSubPath`.
The publisher normalizes ownership; Execution's shared helpers allocate IDs and construct
entries. `IncrementalPublisher.handleBatch` delegates subsequent entry mapping to
`Execution.mapWorkEventBatch` after normalizing owners.
Normalization preserves values, errors, order, and lifecycle events; it cannot repair
invalid accounting.

Initial response construction is shared with spec execution:

- `Execution.initializeIncrementalResponse response initialGroups initialStreams`
  constructs the root data/errors envelope and pending notices, returning the initial
  result and ID state. `yieldIncrementalResults` uses this state for later updates.
- `ReferenceWorkQueue.initializeIncrementalResponse response work` initializes concrete
  queue state, passes its initial notices to that same helper, and creates the publisher
  with the returned IDs and live nodes. It returns the initial result, queue, and publisher.

Initial notices are not synthetic work events: `mapWorkEventBatch` constructs subsequent
updates and has no root-response argument. There is no separate implementation of pending
serialization or initial-envelope construction in `IncrementalPublisher`.

All executable replay views share `State.runWithPublisher`, the queue/publisher loop:

| Entry point | Result |
| --- | --- |
| `State.runNormalized` | Residual queue and normalized work-event batches for supplied host inputs. |
| `createWorkQueueForSchedule work schedule` | Observable `Execution.WorkQueue`, constructed from one initialized state and the source's admitted input histories. |
| `ReferenceWorkQueue.initializeIncrementalResponse` | Initial response, concrete queue, and publisher, using Execution's shared initializer. |
| `State.run` | Response updates plus residual queue/publisher, including updated mapper IDs. |
| `replayIncrementalResponse completed inputs` | Initial result, updates, and concrete termination flag. |
| `ResponseStreamCursor.initialize`, `run`, `step` | Optional resumable packaging of the same initialization and replay. |

A silent input produces no response update. `replayIncrementalResponse_eq_cursor` in
[CursorReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/CursorReplay.lean)
proves that the finite runner and cursor have identical initial results, updates, and
termination flags. `ResponseStreamCursor.initialize_eq` identifies their shared initial
envelope and ID state by definitional equality.

The queue adapter admits normalized outputs realized by some source-admitted input
prefix. This existential describes a language of observations, not a selected future.
Completion is determined by the queue's terminal flag, not the host source's `finished`
predicate. Host batches and the one-update-per-work-batch mapping are unchanged; spec
execution supplies the outer `batchIncrementalResults` response aggregation. Sharing the
initializer adds no event consumption, buffering policy, or second ID allocator.

## Host event source assumptions

`schedule.ValidFor work` requires:

1. An empty source history, admission of empty input, and prefix-closed admission.
2. `ValidGraphEvents work` for each admitted flattened input: exact fixed payloads,
   errors, contributors, and child work; fresh occurrence identities; producer settlement
   before dependent work; ordered stream items and valid exhaustion/failure.
3. `inputsStarted work inputs = true` for each admitted input. Batches are nonempty,
   occur before queue termination, and settle only already-started tasks/streams.
   Eligibility is checked sequentially, including earlier events within the same batch.

These are input laws, not output-correctness assumptions. They require neither valid
response lifecycles nor disjointness, reconstruction, initial-notice correctness, or
admission of the produced output history. They assert no fairness or eventual settlement.

### Optional finite nonblocking

`WorkQueue.Nonblocking` means every admitted output prefix has a finished continuation
in the same source language. Source validity alone does not imply it: a source admitting
only empty input remains valid while an initialized empty-stream boundary stays open.

`schedule.NonblockingFor work` is the optional local queue-boundary premise: every admitted
input prefix whose residual queue has not terminated admits another nonempty input batch.
`ImplementationNonblocking`, witnessed by `implementationNonblocking_holds` in proofs
`Nonblocking`, states that a valid source satisfying this premise yields a nonblocking
queue for nonempty executed work. `createWorkQueueForSchedule_nonblocking` proves the
transfer even without the execution-generation restriction. Its witnesses are a finite
fresh-identity budget and exact replay composition. The proof extends the actual input
prefix, including silent batches, rather than selecting a different realization of its
output. The host source's
`finished` predicate is irrelevant; concrete queue state determines output termination.

This premise is stronger than requiring another batch only when a healthy unsettled
task or a live stream exists. Connecting that weaker host-only premise requires a separate
no-internal-deadlock argument. `NonblockingReadiness` establishes active-root health and
exact pending counts; task-start coverage and outstanding-host-work coverage are not yet
established here. Neither premise is added to `ValidFor` or the conformance contract.

The **nonblocking** names distinguish the two levels: `NonblockingFor` is a local source
assumption, while `WorkQueue.Nonblocking` is the finished-continuation conclusion. Use
**readiness** for the internal fact that host work is outstanding. Progress is a broader
informal category; host responsiveness is not an alias for queue nonblocking. These
finite existential results assert neither elapsed-time guarantees nor host fairness.

## Work-queue conformance

The public work-level proposition is:

```lean
def createWorkQueueForScheduleConforms : Prop :=
  ∀ work (schedule : EventSource (List GraphEvent)),
    ExecutedWork work
    → work.size ≠ 0
    → schedule.ValidFor work
    → (createWorkQueueForSchedule work schedule).Conforms work
```

`ExecutedWork` means work returned by pure root execution, including its fixed outcomes;
it is not merely a plan. Nonempty work is required because ordinary execution constructs
no queue, while incremental initialization requires a nonempty notice frontier.
The existing witness
[`createWorkQueueForScheduleConforms_holds`](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/Conformance.lean)
has the following four-clause proof structure. Terminal accounting includes showing that
every cancelled task has a covering positive-error completion:

| Clause | Proof route |
| --- | --- |
| `Initialized` | Source freshness and empty-input admission; generated initialization supplies valid initial notices. |
| `PrefixClosed` | Every output-batch prefix has an admitted input-prefix realization. |
| `AccountsForWork` | One joint replay witness establishes atomic admission and terminal accounting. |
| `TerminationMatchesWork` | Concrete termination gives complete accounting; an abstract run's marker forces the concrete terminal flag. |

### Initialization

`ExecutedWork.nodeRefCoherent` and `ExecutedWork.initializes` derive coherence and
initial-notice correctness. Neither is a caller premise or hidden in the host-source law.

[Initialization](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/Initialization.lean)
proves structural eligibility and reference uniqueness.
[InitialAncestorAccounting](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialAncestorAccounting.lean)
proves that every initially announced group's ancestors have no contributing task in
the full execution work.
[ConstructorInitialization](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/ConstructorInitialization.lean)
proves nonempty initial notices for nonempty executed work and assembles the result,
including exhausted stream boundaries.

[WorkQueueInitialization](../../Tests/GraphQL/IncrementalDelivery/WorkQueueInitialization.lean)
distinguishes legitimate generated nesting from raw work whose hidden tasks invalidate
an apparent notice frontier.

### Proof structure

[ConformancePlan](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/ConformancePlan.lean)
defines proof-only obligations and checked reductions. Its `ReplayWitnessExists` asks
for one `Witness` containing atomic nontermination events, a publication matching, and
ordered failure cuts. All eight obligations must hold for that same witness:

| Obligation | Checked construction |
| --- | --- |
| `BatchShape` | `batchShape_holds` relates canonical nonterminal atoms to the actual normalized batches. |
| `AnnouncedFailures` | `announcedFailures_exists` supplies prior contributor announcements for the accepted failure inventory. |
| `UncancelledFailures` | `mixed_failureCertificates` licenses mixed object/item failures against their ordered predecessors. |
| `PublicationAdmission` | `mixed_publicationCertificates` supplies payload, freshness, producer/item order, effective ownership, and carried notices. |
| `ControlAdmission` | `mixed_admissionCertificates` supplies group/stream controls and their notices on the same history. |
| `TaskAccounting` | `terminal_generatedTasks_accounted` uses producer-rank induction: available tasks publish or cancel; unavailable descendants inherit cancellation. |
| `NodeAccounting` | `terminal_nodes_of_tasks` combines task coverage with actual completion of announced references. |
| `CancellationReporting` | `terminal_cancellationReporting` combines concrete group failure origins, released stream closure, and producer-path inheritance on the same witness. |

`replayWitnessExists_holds` and `conforms_of_replayWitnessExists` are the joint construction
and checked source-contract reduction. `TaskAccounting` supplies publication or causal
cancellation; `CancellationReporting` separately supplies
for the covering completion required by `Terminal`. The reporting evidence must use the same
atomic events, publication matching, and failure inventory as the other obligations.
Independent existential witnesses for different leaves do not establish conformance.

The checked terminal reductions preserve this distinction: node accounting derives
internal task accounting for generated work, but full termination additionally requires
reporting. The proof-only completion-existence characterization likewise includes reports
for cancelled attachments; internal accounting alone is no longer its sufficient premise.

`TerminalReporting` proves the read-side bridge: terminal tasks retain ordinary internal
accounting, and every unpublished task has a positive-error completion covering its
attachment path. Reports persist under history extension and cover descendant paths;
in an explained history their nodes are known and announced. The existing safety,
disjointness, reconstruction, and zero-error coverage witnesses hold with the revised
terminal law. Reference conformance, the query bridge, and independent existential
complete-run constructions are rebuilt. The error-aware public coverage witness and
unconditional complete-query-outcome witness pass with the same public premises.

`FailureScopeMapping.replayResponse_unpublishedScope` transports terminal cancellation
reports through both batching stages and the actual response mapper. Every unpublished
task has a covering path in the client's decoded failure-scope list. Its proof preserves
exact completion notices and counts, then uses stable-ID injectivity and notice metadata.
This establishes the queue-to-wire boundary. The pure mixed-execution comparison below
relates ordinary response positions to these published or reported tasks.

`FailureAwareSourceCoverage.WorkObservation.source_addressed` proves partial source
coverage without a zero-error premise: every initial or successful prepared-payload
position is delivered or below a decoded failure scope. This uses actual publication
decoding for published tasks and terminal reporting for unpublished tasks. The ordinary
response comparison still needs to account for null ancestors produced by error bubbling.

`FailedTaskScopes.WorkObservation.failedTaskScopes` separately covers failing payload
attachments using actual decoded completions: publication provenance forbids publishing
a failure. `reported_attachment_explains_null` proves the null-ancestor case by comparing
the reported scope and reference path as prefixes of the same attachment.
`ReferenceFailureCoverage.WorkObservation.addresses_reference` combines these results
with prepared source coverage. Its `PreparedResponseCovers` is a proof-only
pure-execution target, not an extra queue law: every ordinary position must occur in the
prepared successful inventory or be explained by a failing attachment (possibly below a
null ancestor). `ResponsePositionsDeliveredOrFailed_of_preparedComparison` checks
the final dependency edge to the public statement, with the same incremental-argument
premise on the execution comparison. `RecursiveValueCoverage` constructs that comparison
without an assumed certificate and proves `ResponsePositionsDeliveredOrFailed_holds`.
The public statement permits later execution errors and requires zero initial errors;
its explanations use actual decoded failure scopes, not just internal cancellation.
`InitialFailurePreservation` supplies a general mixed-execution dependency for this
comparison: an initial bubbling result also bubbles after directive erasure, and an
initial null remains null or bubbles. Its mutual witness follows actual collection,
partitioning, field/value completion, non-null wrappers, and streamed prefixes under
incremental-argument validity. No schedule or equal-error-count premise is needed.
`executeRoot_preserves_failures` lifts this to root execution;
`completeStreamItems_failure_bubbles` proves that a retained failed mixed stream item
forces ordinary full-list bubbling. Regressions distinguish initial error counts from
ordinary totals when deferred selections add errors or streaming stops at the first
failed item. These forward implications justify initial bubbling/null boundaries without
assuming error-count agreement.
`OrdinaryFailureReflection` proves the reverse failure dependency for arbitrary mixed
execution: ordinary bubbling has an initial bubble or an actual retained failed task
below the current response attachment. Ordinary null similarly has an initial null/bubble
or descendant failure. The mutual witness follows plan partitions, nullable/non-null
wrappers, initial lists, and short-circuit streamed tails; successful partial items may
carry the failure in deferred child work rather than fail themselves.
`executeRoot_explains_failures` lifts this comparison to root execution, and
`preparedResponseCovers_bubblingRoot` constructs the general prepared certificate when
ordinary bubbling makes the reference root null. A mixed stream/defer regression checks
an error-free initial list and successful partial item outcomes whose failed deferred
children make ordinary execution bubble to root. The recursive comparison below separately
supplies position coverage inside ordinary nonbubbling mixed responses.
`QueryFailureReflection.queryOutcome_addresses_nullReference` connects the root-null
certificate to every complete conforming actual query observation with an error-free
initial response. The mixed regression checks this client-facing theorem without fixing
wire IDs or notice scopes. `ResponsePositionsDeliveredOrFailed_of_nonbubblingComparison`
checks the root dependency edge: only ordinary successful root field results need a
prepared position certificate. Their counted errors and nested null values remain
unrestricted; ordinary bubbling is discharged by the proved reflection witness.
`SourceCursorExtension` supplies the coordinate algebra for the nonbubbling
comparison. Extending a valid cursor environment preserves the full labelled source
inventory, including payloads and absolute item indices, and therefore both leaf-only
and container-inclusive positions. Initial field concatenation and adding an enclosing
list cursor reuse that witness. Prepending fields requires initial-position uniqueness
to exclude cursor shadowing, not a zero-error premise. Regressions retain counted errors
in successful payloads and exhibit the coordinate change from a duplicate earlier field.
`EntryFailureCoverage` keeps ordinary null tags in typed reference entries during
composition. Its local coverage relation uses only actual initial/source positions or
an actual failed task, and is stable under work combination and reference permutation.
The final bridge to `PreparedResponseCovers` uses ordinary reference-path uniqueness to
decode a tagged null as an actual null at that path; local composition needs no such
lookup. `ValueFailureCoverage` combines forward and reverse mixed failure reflection:
ordinary successful values have successful initial counterparts, ordinary non-null values
have non-null initial counterparts, and ordinary null entries are initially available or
explained by retained descendant failures. These facts allow arbitrary counted errors.
The nullable-object regression covers an ordinary null whose initial partial object has
no leaf positions, including preservation of its explanation under unrelated sibling work.
`EntryCoverageAssembly` combines field and item certificates using the actual initial
and source inventories. It preserves failed-task payloads and nullable ancestry while
appending work, maintains nested stream indices under cursor extension, and adds visible
object/list container entries from actual initial data. Earlier initial data requires
assembled initial-position uniqueness to exclude cursor shadowing; no zero-error premise
is used. Regressions combine a successful streamed scalar with counted errors and a
nullable failure beneath an initial object with no leaf positions, in both field and item
assembly. They also connect the assembled object certificate to `PreparedResponseCovers`.
`EntryCoverageRetention` preserves these certificates across the actual work boundaries:
successful deferred payloads expose the same field/source inventory, successful retained
stream items expose their local value/source inventory at the actual absolute index, and
both preserve failed descendant payloads. Combining retained partitions adds no synthetic
initial slice. The stream witness requires a real cursor lookup, not the total projection's
default-to-zero fallback. Regressions retain scalar data and nullable child failure at
initial count three plus item ordinal one, allow counted errors in successful payloads,
and exhibit the wrong coordinates when the required cursor is absent.
`StreamSuccessAlignment.completeStreamItems_aligns_ordinarySuccess` proves that ordinary
nonbubbling list execution prevents mixed stream short-circuiting: the full input tail is
retained, and every reference item aligns with its actual completed value and child work
at the same absolute index and a witnessed threaded state. Neither data nor error-count
equality is assumed. `completeStreamItems_nullEntry_covered` then proves actual coverage
of every ordinary null item, including partial initial objects with failed deferred
children. A mixed regression constructs a full prepared response certificate for two
such nullable items whose initial objects have no leaf positions.
`completeStreamItems_entriesCovered_of_values` checks the general streamed-tail dependency
edge: pure per-value coverage suffices for all reference entries in the actual tail.
Its recursive value-coverage argument is discharged by `RecursiveValueCoverage`, not a new
queue assumption. The nullable-item regression also instantiates it with the local
`ValueFailureCoverage.completeValue_nullEntries_covered` witness.
`CompletionCoverageAlgebra` packages successful ordinary field/value comparison while
allowing different initial data and error counts. It composes covered immediate fields,
retained partitions, and reference-entry permutations; an initial bubble rules out a
successful combined ordinary reference without executing cancelled work.
`FieldExecutionCoverage` checks the actual collected-field, deferred-partition, plan, and
root-collection dependency edges. Their proof-only dependency is `ResponseFieldCoverage`,
which `responseFieldCoverage_of_values` reduces to recursive value coverage. Generated
cursor/ownership witnesses supply initial uniqueness, and exact arbitrary-error ordinary
entry permutation supplies plan reordering. `QueryEntryCoverage` connects this root
comparison to `PreparedResponseCovers` and the public client-facing failure-coverage
statement. These are checked intermediate edges, not new scheduler/public premises.
An actual-query regression instantiates them for immediate and deferred nullable errors:
ordinary execution counts two errors, while the initial response counts one and retains
the other partition. No equality of error totals or zero-error comparison is assumed.
`ValueWrapperCoverage` checks actual named-type and non-null completion from their
recursive field/inner-value comparisons. Nullable object bubbling is explained either by
initial null data or a retained failed descendant task; successful non-null completion
uses forward failure preservation to exclude an initial null. Ordinary and initial error
counts need not agree. Regressions cover a deferred required field that nulls the ordinary
object but leaves a partial initial object, and a non-null object with a deferred nullable
field error. The named-type dependency decreases execution fuel; the non-null dependency
decreases only type structure. Exhausted value/field fuel and local ordinary null coverage
are proved. `ListExecutionCoverage` checks actual finite item traversal from local recursive
value coverage, preserving absolute offsets and actual threaded states. Generated cursor
seeds and ownership uniqueness justify head/tail assembly; nullable list wrapping adds
the enclosing cursor without losing retained failures. The inactive-stream branch is
also checked. Regressions cover nullable errors in partial non-null objects at a nonzero
item offset, and required deferred failures that null the ordinary list while leaving
error-free partial initial items. `StreamExecutionCoverage` joins covered initial prefixes
and actual streamed tails at their shared absolute boundary. Ordinary success prevents
tail short-circuiting; ordinary list bubbling is explained by retained failures. Empty
tails at exhaustion and counts beyond exhaustion follow the actual hook's separate branches.
`RecursiveValueCoverage.valueCompletionCoverage_holds` closes these recursive dependencies
by strong fuel induction and structural non-null type descent. Its
`responseFieldCoverage_holds` supplies every actual field/plan/root comparison, and
`ResponsePositionsDeliveredOrFailed_holds` is the general public proof witness.
The streamed regression constructs a full prepared certificate with failed descendants in
both partial initial and future objects, checks nullable list bubbling, and covers exhausted
and never-reached boundaries. The witness's axiom audit uses only `propext`,
`Classical.choice`, and `Quot.sound`.
`PlainFailureCoverage.preparedResponseCovers_plain` constructs the directive-free case
by exact initial-response agreement, without restricting error counts. Its public-statement
instance is syntax-restricted; it does not discharge mixed incremental failure comparison.
`BasicFieldErrors` supplies arbitrary-error partition algebra for that comparison:
`basicFields_append_result` combines partitions exactly, and
`basicFields_perm_withErrors` preserves bubbling versus success, successful field
permutation, and the full counted-error total. These do not assume successful execution.
`basicFields_entries_withErrors` and `basicFields_perm_entries_withErrors` retain exact
typed entries for nonbubbling field results with nullable errors. Thus the remaining
execution comparison can reuse partition reordering without an error-free-data shortcut.
`basicFields_bubbles_iff` and `BasicListErrors.basicList_bubbles_iff` identify an actual
bubbling field or item whenever ordinary collection bubbles. The list split uses the
existing exact append theorem, including errors. For plain item selections,
`completeStreamItems_itemContext_bubbles` links a retained streamed failure to ordinary
list bubbling. Short-circuit and ordinary completion need not have equal total error
counts; this result identifies the shared failing item rather than assuming count equality.
`basicStreamResults_failure_iff_bubbles` and
`completeStreamItems_itemContext_failure_iff` establish both directions: ordinary bubbling
has a retained first failed item, not just the converse. Successful plain streamed items
reconstruct exact ordinary data and the full error total even with nullable item errors.
`StreamFailureCoverage.completeListValueWithStream_plain_coverage` connects these facts to
the actual executable stream hook under a valid inherited defer context. Its prepared
certificate covers ordinary positions through disabled streaming, prefix failures,
exhausted tails, and later item failures. Successful positions come from the actual source
inventory; bubbling is justified by a real retained failed task at the list attachment.
This is the plain-item stream case, not the general mixed nested-execution witness.
`FailureCoverageAlgebra` preserves successful source positions under occurrence
relabelling and embeds actual failed tasks into combined or nested work. Adding retained
work therefore preserves a prepared coverage certificate without fixing a completion order.
`DeferredFailureCoverage` covers successful and bubbling combinations of retained deferred
partitions, including nullable errors, shared owners, and arbitrary child work.
`collectExecutionGroups_retains_results` connects the exact computed partitions and state
transitions to that algebra. `executeExecutionPlan_partition_coverage` supplies actual plan
coverage given local field-result comparisons, not an assumed response-coverage or queue
law. Regression queries share one scalar field between two defer blocks and distinguish a
nullable deferred error from a deferred non-null failure. The general mixed-execution
comparison still needs a recursive treatment of fields whose nested work changes their
initial result relative to ordinary completion.
`ContextFailureCoverage.executeExecutionPlan_context_coverage` discharges those local
equations for partitions with uniform inherited contexts and plain bodies, without an
execution-success premise. `preparedResponseCovers_singleDefer` connects collection,
planning, and actual root completion for a single active defer with an arbitrary plain
body. `ResponsePositionsDeliveredOrFailed_of_singleDefer` then proves the public
client-coverage proposition for that syntax fragment, universally over resolver
environments, variables, fuel, and conforming complete observations. Nullable object/list
errors and non-null bubbling are allowed; nested incremental bodies and mixed-context
shared partitions remain outside this restricted witness.
`preparedResponseCovers_equivalentPartitions` transports successful position membership
across field permutations and retains an actual root-attached failure when the combined
ordinary result bubbles. It does not transport null-path lookup across potentially
duplicate raw response names. `RootPartitionFailureCoverage` uses exact collection
erasure and `BuildExecutionPlan` permutation to compare actual root completion with the
ordinary root response, rather than just the plan's reordered field list. Its remaining
premises are local per-partition field-result equations. The interleaved shared-defer
regression checks an ordinary field order different from the immediate/deferred plan
order, with a positive-error nullable field.
The null-ancestor algebra constructs prepared coverage from a retained failed task at a
descendant attachment. `NestedFailureCoverage` tests actual execution through a non-null
object: ordinary completion produces null at alias `viewer`, while the deferred failure
is attached strictly below it at `viewer.content`. The initial response has zero errors.
Its client-facing regression quantifies over every conforming complete observation and
derives the decoded explanation without prescribing a notice ID or notice path. This
checks the necessary null-ancestor branch but does not replace the general mixed
execution induction.
`reference.isNullAt path` tests existing null positions on the shared response-value type.
`ReferenceNullPositions.isNullAt_iff_null_entry` relates this receiver-style null-ancestor
test to typed null entries for unique responses. Missing paths and descent through null
are not recognized as existing null positions. The proof reuses typed subtree lookup, so the
remaining execution comparison can construct typed evidence without duplicating alias or
index traversal reasoning.

### Client-coverage input boundary

`ResponsePositionsDeliveredOrFailed` requires
`operation.incrementalArgumentsValid variables` as well as an error-free initial response.
Without the argument premise, coverage is false on the model's permissive raw directive
syntax. `FailureCoverageInputs.coverage_requires_input_boundary` is a checked counterexample
using a conforming reference queue and an admitted complete source, not an invented wire
history:

```graphql
{ ... @defer { values @stream(initialCount: -1) } }
```

The initial response is error-free. `getStreamUsage` rejects the count, and nullable list
completion returns `values: null` with one counted error. The deferred group publishes
that data with its error count, then completes successfully with zero completion errors.
The client decoder therefore has no failed-completion scope. Erased execution returns
three list items, including `values[0]`, which is neither delivered nor below such a scope.
The argument premise rejects this nested directive. This fixture is not a claim about valid
GraphQL input or a new implementation bug; the queue accounts correctly for its fixed
payload.

The premise excludes enabled stream argument failures, including noninteger/null/negative
counts after operation defaults and variable bindings are evaluated. An explicitly false
condition disables the count check; an undefined condition does not. Missing count variables
use the modeled directive default of zero. The check conservatively traverses all syntax,
including skipped/unreachable selections, and is not full incremental validation: directive
placement, condition coercion, and label validity remain outside it. Execution, queue
conformance, and the completion-notice-based failure decoder are unchanged.
`RecursiveValueCoverage` proves general mixed-execution coverage under this input boundary.

`Correctness/ArgumentValidity` connects this premise to execution: every collected field
retains its own argument check and its nested selection checks, even across active defer
allocation, overlapping field merges, and object subcollection. Immediate and deferred
execution-plan partitions preserve the invariant. `getStreamUsage_ok` and
`fields_getStreamUsage_ok` exclude the modeled count-argument error at the stream hook;
they do not assume successful resolvers, successful items, or zero counted errors.

`FailureReportOrigins` supplies a reporting construction independent of `Terminal`:
a contributor's closure after a recorded positive failure covers the failed attachment,
even if its notice followed settlement. When an owner is still open at settlement,
closure of all announced refs guarantees such a reporting event. More generally, an owner
may be latent at settlement: it suffices that its ref was not already completed, is
eventually announced, and closes. The contributor-specific theorem also recovers the
owner's full scope, which may cover cancelled private tasks outside the failed shared
attachment. These are sufficient timing cases, not additional restrictions on host
settlement order.

`ExecutionPaths.executeRootSelectionSetCore_under` proves that generated work retains
producer-local attachment bounds through fields, deferred partitions, nullable bubbling,
and stream completion. `TaskAttachmentPaths.WorkUnder.producer_reported` then propagates
an existing report from a producer to its child task, without requiring a child notice.
`ExecutedAttachmentPaths` instantiates these results for executed work independently of
the source and queue contract. This handles report inheritance, not the separate question
of where the first covering report originates.

`TerminalCancellationReporting.cancellationReporting_iff_availableTaskReporting` reduces
the eighth construction leaf to root tasks and tasks whose producer has published.
Unreleased descendants inherit a report by finite producer-rank induction and generated
attachment locality. This equivalence needs neither terminal task accounting nor the
terminal reporting law.

`TerminalStreamReporting.terminal_availableItem_reported` discharges the released-item
branch on the canonical replay witness: source-success inventory and its existing ledger
publish every item at a successful closure; a failed closure instead carries a generated
positive error and the same list descriptor. Together with producer inheritance,
`cancellationReporting_of_availableObjectTaskReporting` reduces the remaining reporting
construction to released execution-group tasks. Their scopes must come from actual retained
group failures or ancestor cancellations, without choosing a different publication
matching or assuming the terminal reporting law.

`OwnerFailureReporting.ExecutedWork.groupReport_covers_task` connects ref-based group
report origins to response attachment coverage. A positive completion of a contributing
group or one of its full defer ancestors covers that task, even when the contributing
group is unannounced. Canonical ancestry and coherent paths come from execution, not from
the queue contract. The remaining concrete obligation is to recover these report origins
for unpublished released object tasks from retained failures and cancellation cleanup.

`CancelledGroupReporting` and `CancelledGroupReportingHandlers` preserve actual positive
completion origins through subtree removal, refused late-child registration, cached-failure
draining, and failed task settlement. The internal cancellation registry therefore retains
ref-based report evidence at these local boundaries, without assuming terminal reporting.
`SuccessfulGroupReporting` extends this preservation through successful settlements and
item arrivals, including their release-time failure drains. `FailureReportReplay` derives
positive caches and report origins for full matched raw replay from initial state.
`NormalizedFailureReports.cancelledContributor_task_reported` transports these origins
through the actual publisher to the common witness and obtains attachment coverage for
any cancelled contributor. The remaining released-object case is a failed contributor
that has not yet been removed: its retained failure must eventually close or be covered by
ancestor cleanup. This is not assumed as an extra source or conformance premise.

`CachedFailurePersistence`, `CachedFailureReplay`, and `RetiredFailureReports` follow
surviving task membership, computation replay, and actual covering cancellation reports.
Their evidence requires no executable group-level provenance cache.
`OldRootCoverage.terminal_oldRootCovered_absent` addresses final record absence from
root exhaustion when a root path was established at an earlier source boundary; the path
survives later handlers even after semantic health is lost.
`CoveredFailureReports.terminal_acceptedHealthyContributor_reported` consequently derives
a positive report for a healthy live contributor at an accepted failure, using generated
contributor uniqueness and independently proved prefix coverage.
`HealthyFailureOwners.matchedFailure_healthyContributor_live` derives the live-record
premise: a healthy retired contributor would have settled the same task successfully,
contradicting its fixed failing outcome. `TerminalFailureOrigins` proves that every record
invalidated by the accepted failure inventory has a positive terminal report. Its
source-prefix induction selects the first relevant failure and inherits earlier reports
through full defer ancestry. `TerminalObjectReporting.terminal_registeredTask_reported`
connects unpublished registered objects to that inventory: any healthy retired contributor
would publish the task, so an unpublished task has an invalidated contributor with an
actual report. Root lowering and publication reflection register all released objects.
`terminal_cancellationReporting` combines this frontier with stream reports and finite
producer inheritance, completing the eighth construction leaf without a new assumption.

The shared D/H regression now proves that its reporting-incomplete history is an admitted
prefix but not terminal under the original publication matching, regardless of failure
cuts. The concrete reference replay still announces H and emits its broader failure.

The proof uses concrete registration, retirement, buffered-value conservation, accepted
failure inventories, exact publisher registries, and notice tracking. These are derived
implementation invariants, not requirements imposed on the opaque host source.

The table is a manually maintained theorem map.
[WorkSchedulerConformancePlan](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerConformancePlan.lean)
contains the public-target, joint-construction, empty-stream, and reverse-termination
regressions, including the complete eight-leaf conformance construction.

## Query correctness

`ImplementationCorrect schema operation` connects the actual reference constructor to
the general query theorems. Its operational premise is
`queryScheduleMatches ... schedule result complete`. This predicate derives work from
execution, requires an applicable root and nonempty work, checks source validity, and
witnesses the result by an admitted finite input history passed to
`replayIncrementalResponse`. It assumes no target conformance or response property.

The theorem
[`implementationCorrect_holds`](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/CursorObservation.lean)
supplies both `queryWorkQueueConforms` and `queryObservation` for
`fun work => createWorkQueueForSchedule work schedule`:

- Prefix observations require no termination.
- Complete observations require the queue to have terminated and supply `queryOutcome`.
- Complete zero-error observations inherit reconstruction, basic-position equivalence,
  and exactly-once leaf delivery.
- Complete observations with valid incremental arguments and zero initial errors inherit
  failure-aware position coverage, even with later errors. The proof-only specialization
  `queryScheduleMatches_addressesResponsePositions` in `CursorCorrectness` uses the shared
  replay predicate, without requiring the optional cursor or new source premises.

The [public correctness witnesses](README.md#public-statements) apply directly; no
duplicate implementation-only correctness propositions are needed.
[CursorCorrectness](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/CursorCorrectness.lean)
packages the end-to-end cursor consequences. The public bridge itself does not depend
on the optional cursor.

`schedule` describes allowed input histories; the existential `inputs` selects one
admitted finite replay. An initially empty source history cannot stand in for that input
witness. Observation is through the reference constructor's own source, not a replacement
maximal source.

Ordinary and invalid-root branches are covered by the general query theorems, not this
nonempty incremental replay bridge. Abstract `queryOutcomeExists` does not imply that
every implementation source terminates.

## GraphQL.js correspondence

The current source comparison is pinned to
[WorkQueue.ts](https://github.com/graphql/graphql-js/blob/4a9b3121e65cc9c758109b2b6fec8d29f9a5b99b/src/execution/incremental/WorkQueue.ts),
[IncrementalPublisher.ts](https://github.com/graphql/graphql-js/blob/4a9b3121e65cc9c758109b2b6fec8d29f9a5b99b/src/execution/incremental/IncrementalPublisher.ts),
and [Computation.ts](https://github.com/graphql/graphql-js/blob/4a9b3121e65cc9c758109b2b6fec8d29f9a5b99b/src/execution/incremental/Computation.ts).
The draft remains authoritative.

| GraphQL.js construct | Lean counterpart |
| --- | --- |
| `Work`, `Task`, `Stream`, `Group` | Same record names; lowering adds structural occurrence identities and explicit parent metadata. |
| `GraphEvent`, `WorkQueueEvent` | Host inputs and queue outputs, including value/item batches and stream failure. |
| `GroupNode`, `TaskNode`, root/node collections | Same node names with explicit finite-list `State` fields. |
| `createWorkQueue` | `State.initialize` is the initialization core; `createWorkQueueForSchedule` additionally lowers work and exposes normalized outputs. |
| Integration, pruning, activation, and event handlers | Corresponding `maybeIntegrateWork`, `addGroups`, `pruneEmptyGroups`, `startNewWork`, task/stream handlers, and removal functions. |
| Publisher `buildResponse` (initial envelope) | `ReferenceWorkQueue.initializeIncrementalResponse`, composed with the shared `Execution.initializeIncrementalResponse`. |
| Publisher `_toPendingResults` | `Execution.getPendingEntry` with `ensureID`, called by the shared initializer and subsequent mapper. |
| Publisher `_handleBatch`, `_getBestIdAndSubPath` | `IncrementalPublisher.handleBatch`, `getBestIdAndSubPath`; owner normalization precedes shared `Execution.mapWorkEventBatch`. |

Modeling adapters:

- `NodeRef` values stand in for defer/stream object references; structural occurrences
  identify tasks. Finite lists replace maps/sets.
- Pure finite outcomes validate supplied events; errors are counts, not error objects.
- `Work.fromExecution` and permanent registration recover new declarations from repeated
  contributor metadata. Taskless ancestors retain release and cancellation links.
  GraphQL.js receives new declarations separately and needs no equivalent registry.
- The host supplies events instead of promises/iterators. Backpressure, async cancellation
  APIs, infinite sources, real-time readiness, and fairness are not modeled.
- Runner, source-adapter, and optional cursor functions are Lean interfaces, not
  additional
  normative GraphQL algorithms.

### Shared publication owners

The raw queue may flush a shared value through an outer group while the publisher selects
a deeper open contributor. The contract constrains the effective owner after
normalization.
It requires healthy open support but chooses a longest path among all open contributors,
including a failed co-owner still awaiting completion. Health support and the wire owner
need not coincide.

`PublisherOwnership`, `PublisherRegistry`, and the joint publication certificates prove
this selection against the actual registry at every publication.
The proof-only
[OwnerNormalization](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueSemantics/OwnerNormalization.lean)
adapter separately checks owner selection and payload/order preservation.
[OwnerNormalization tests](../../Tests/GraphQL/IncrementalDelivery/OwnerNormalization.lean)
cover ties and per-value choices;
[WorkSchedulerFailedOwnerRemapping](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerFailedOwnerRemapping.lean)
covers a deeper failed-but-open co-owner with a healthy supporter.

### Retained outcomes

GraphQL.js retains rejections in task computations and replays them when another owning
group starts. The finite queue retains that rejection on `TaskNode`; the explicit ready
drain represents replay after the notice carrier without reproducing promise scheduling.
A failure closes active owners only. It neither decrements a dormant owner's pending
count nor removes that owner's task membership.

`startGroup` visits tasks in registration order. For two shared tasks, the second can
settle first while both belong to a latent group. When the group is released after both
reject, GraphQL.js reports the first task's rejection, not the earliest settlement. The
validated-query probe confirms this with early execution both enabled and disabled:

```graphql
{
  ... @defer(label: "R1") { first: bad }
  ... @defer(label: "R2") { second: bad }
  ... @defer(label: "P") { slow ... @defer(label: "C") { first: bad second: bad } }
}
```

With non-null `bad`, settle `second`, then `first`, then `slow`. C's completion reports
`first`. The Lean fixture uses distinct raw counts to make the same replay order observable
without introducing error identities into the model.

Settled unpublished successful values are retained too. Starting their task again does not
integrate child work or decrement pending a second time. Empty-shell pruning uses task
membership, and removed task nodes absorb later callbacks.

[WorkSchedulerRetainedOutcomes](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedOutcomes.lean),
[WorkSchedulerRetainedAnnouncement](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedAnnouncement.lean),
and [WorkSchedulerRetainedErrorCounts](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedErrorCounts.lean)
check release, cancellation, selected-cause replay, and rejection of invented aggregates.
[DeliveryFailureReporting](../../Tests/GraphQL/IncrementalDelivery/Fixtures/DeliveryFailureReporting.lean)
checks task-order rejection replay and one explanation for a latent owner with two
failures, while preserving collected diagnostics in deferred and stream work.

### Cancelled-parent registration

`cancelledGroups` distinguishes an absent failed parent from a successfully retired one.
Without that information, late child registration can create an apparently healthy owner
under a failed parent, allowing a fully invalidated shared task to contribute another
error.
The repaired GraphQL.js implementation rejects new groups under removed parents. Its
computation replay also retains failures, avoids duplicate successful processing, and
prunes by task membership. These changes address the previously observed late-parent
and unannounced-completion defects. Lean keeps its explicit registry and ready drain;
agreement on the audited cases is not a JavaScript refinement theorem.

[WorkSchedulerLateFailedParent](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerLateFailedParent.lean)
checks generated work with failures, a later successful shared producer, and delayed child
registration. The cancellation registry prevents the invalid late contribution.
[WorkSchedulerReactivation](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerReactivation.lean)
checks permanent refusal of cancelled references, while
[WorkSchedulerTasklessParent](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerTasklessParent.lean)
checks release/cancellation through taskless ancestors.

#### Late-parent audit fixture

A representative query uses null-returning non-null `required` fields, successful `a`
fields, and a shared `user` object:

```graphql
{
  ... @defer(label: "P") {
    pBad: required
    user { ... @defer(label: "C") { x: required } }
  }
  ... @defer(label: "Q") {
    keepQ: a
    user { ... @defer(label: "D") { x: required y: required } }
  }
  ... @defer(label: "R") {
    rBad: required
    rBad2: required
    user { x: required }
  }
  ... @defer(label: "S") { user { y: required } }
}
```

The fixed settlement order is P's failure, the shared user producer's success, Y's
failure, R's rejection, X's failure, then Q's remaining success. R collects two diagnostics
but reports its selected unit cause. C is introduced
after P has failed. X's contributors are C, D, and R; Y's are D and S.

The reference machine marks C cancelled at registration. By X's settlement, C is
cancelled, Y's rejection is retained for D, and R has closed with its own failure. A
settlement cannot close dormant D. D's completion follows rejection replay when Q releases
it. Generated replay checks retained task rejection, cancellation provenance and normal
announcement before completion. The complete canonical witness admits the actual replay
and excludes the former aggregate completion count for every batching and matching.

The repaired GraphQL.js audit covers direct queue replay and validated queries. Late C
registration is rejected, and a latent failed group is completed only after announcement.
Cancellation and scope coverage remain independent of the selected numeric explanation.

### Wire and finite-stream projections

Explicit null labels follow the draft spec, whereas the GraphQL.js implementation
omits them. Empty/exact-count stream boundaries have pending/completed lifecycles without
item patches; see [exhausted streams](README.md#exhausted-finite-stream-boundaries).
The model does not claim agreement on every JavaScript error, cancellation, or
interleaving.

## Verification and limits

Reference conformance, the implementation bridge, reusable query-correctness witnesses,
and conformance/reporting regressions build and pass. No algorithm changes, additional
source premises, added axioms, or proof holes discharge the reporting obligation.
The general client-facing failure-coverage witness and its stream/defer regressions also
build and pass. Whole-project build, tests and lint cover the independent finite-progress
proofs and their selected-cause regressions.

Finite-progress witnesses distinguish internal task accounting from observable failure
reporting. Initial owner coverage constructs an accounted history, but alone does not
establish termination. The least-ref maximal-history criterion likewise derives task
accounting and closure of announced IDs, not reporting of cancelled attachments.
Complete-run existence for child-free streams additionally uses
positive failure counts and proves that actual stream closures report every unpublished
attachment. Empty streams and successful items with arbitrary counted errors are included.
Regressions cover these complete observations and reject zero-count notices as reports of
missing data. Stream-only progress also covers arbitrary finite nesting: mutual causal
induction transports actual reports through producer-local attachment prefixes, including
unannounced child streams. The stream-only query bridge derives these locality and
positive-count certificates directly from execution. A single deferred producer, including
shared and repeated owner descriptors, also has a complete-run witness for local stream-only
descendants and positive failures. A root failure supplies the covering scope for every
unannounced child; root success keeps groups healthy while actual singleton stream closures
cover later cancellations. The proof retains existing batch grouping through continuation.
Root-deferred tasks with initially covered groups also have complete-run witnesses for
arbitrary shared ownership and nested stream descendants. The deferred phase reserves a
healthy success carrier or uses justified cancellation, then stream continuation closes
announced IDs and derives actual reports. Generated ref coherence, producer-local path
bounds, and positive failed payloads supply the reporting certificate; raw zero-count
failures are excluded. Every group is initially visible, so its actual scope covers
unannounced stream descendants without giving those streams unnecessary IDs. Independent
nested root streams and an empty deferred phase are also covered. General mixed-work
progress uses full notice-scope origins to report unannounced deferred groups.

Healthy accounted defer groups retain a root or published producer descriptor, including
groups with repeated descriptors and shared owners. Within one explained history, a
dependency stays healthy when both it and its full transitive defer ancestry are satisfied:
accounting excludes future direct contributor settlements, and ref induction excludes
inherited dependency failure. Silent accounting alone is insufficient without ancestor
support. The shared-owner regression checks stability across a later failed-child closure.
The carrier-boundary bridge applies this result to group notices emitted by actual
group-success and stream-value events. Notice eligibility excludes settlements recorded
after its carrier, including settlements at the same output-prefix length. Ordered
licensing prevents those settlements from consuming already accounted-for dependencies;
carrier notice changes preserve publication and causal evidence. The retained-group
regression derives dependency stability from its actual notice rather than supplying that
support separately. Initial group notices have no represented defer dependencies: empty
history cannot account for a represented deferred task, and role separation excludes stream
descriptors. Together these witnesses establish lasting dependency health for every
announced group. General terminal scope assembly is supplied by `GroupScopeReporting`;
dependency stability alone does not report missing attachments or establish termination.

`CausalReportAssembly` separates that remaining construction from scope propagation. Its
mutual induction covers every cancellation rule given actual failed-group scope reports
and actual reports for accepted task failures. Defer-dependency reports reach streams
through their common producer attachment; producer failure/cancellation reports descend
through local attachment prefixes. Stream-only and healthy-group stream progress reuse
this assembly, and the latent broad-owner fixture exercises the failed-group branch.
The group-scope premises remain explicit proof obligations for general progress, not extra
queue laws; the accepted-task origins follow from announced-ID closure as described below.
An arbitrary admitted prefix need not already provide every such report, and a narrow
shared-task report does not imply its broader owner's scope was reported.
`finish_accounted_of_report_scopes` assembles those origins and appends bounded closures
and termination, retaining the original batch grouping. `GroupScopeReporting` derives
these origins and `mixed_reporting_continuation` uses them for general mixed progress.

The shared-owner regression also identifies why the legacy arbitrary-supported-prefix
continuation helper needs narrowing. Its reporting-incomplete prefix satisfies
`SupportedNoticesCovered`: the missing broader owner is failed, not healthy. That owner
remains eligible for a retained-failure notice, but all announced refs have already closed
and the work contains no stream tasks, so no admitted next event can carry its notice.
General finite existence must use a stronger constructive prefix invariant that retains
the needed carrier/report opportunity; it cannot follow from healthy notice coverage and
internal accounting alone. This concerns a proof helper, not a change to public admission
or to the complete-query existence statement.

`ReportingNoticesCovered` is the stronger proof-only construction frontier. It retains
healthy support coverage and additionally covers every eligible group notice, including
retained failed co-owners. Ready object publications, licensed failure settlements, healthy
stream closures, and covering stream publications preserve this frontier. A group-success
carrier with covering notices reestablishes it directly. The stranded-owner regression
violates the stronger frontier; its repaired history satisfies it without assuming
termination or reporting. These preservation witnesses introduce no public queue law or
source premise. General mixed progress must derive actual covering failure scopes before
finalization.

`mixed_reporting_accounted_extension` constructs that accounting while retaining the
stronger frontier. Its least-outstanding-owner argument supplies ready events, and maximality
under covering carriers makes every healthy ref dependency-satisfied.
`ReportingFrontiers` selects all eligible group notices and only stream notices with a
satisfied defer dependency and its full satisfied ancestry. `StreamNoticesSupported`
retains this evidence at each actual carrier boundary, before subsequent settlements.
The continuation derives positive direct causes for every failed open ID: announced
groups exclude inherited failure, while supported streams retain a healthy dependency.
Unique stream allocations identify dependency metadata; pure execution derives this
structural fact, so the public query-existence statement needs no additional premise.
`recorded_group_reported_of_covered_frontier` then derives a retained group's announcement
from its published producer and satisfied dependencies; its actual post-settlement closure
reports the whole group scope with a positive count. The broader private-attachment
regression verifies this derived-notice case. General scope assembly still needs report
inheritance through unannounced groups and unavailable producers; neither accounting nor
this retained-notice case subsumes those obligations. Notice-derived stability and positive
group completions handle the already-announced contributors, including earlier closure.

`mixed_reporting_closed_extension` additionally closes all announced IDs without losing
the reporting frontier or healthy dependency satisfaction. Bounded failure-only closures
preserve these properties and use an actual positive contributing task cause for each
failure completion. Internal accounting alone does not supply that cause.
The generated shared-owner regression checks accounting and ID closure together.
`SettlementClosures` separates the remaining timing cases: a contributor closed before a
later accepted settlement must have closed with a failure event, and a healthy accounted
ref cannot acquire a later direct contributor failure. `ZeroFailureOrigins` excludes any
direct recorded contributor at a zero-count group completion and identifies a failed
dependency or unavailable producer instead. Its root-group regression rejects zero-count
failure completions with no such causal origin. These results narrow the remaining scope
construction without strengthening public admission or assuming terminal coverage.

For coherent execution-generated work, actual group-failure completions have positive
counts. An announced group retains a root or published producer descriptor, even when other
descriptors are unavailable, and all its defer dependencies stay healthy. With no recorded
contributor these facts would make it healthy, contradicting a failed completion. An
announced failed group therefore has an actual covering report once announced IDs close.
This also covers groups that closed before a later shared settlement: licensing excludes
success, while group-failure positivity makes the earlier closure a genuine full-scope
report. The regressions reject zero-count group failure at arbitrary output positions and
derive the retained broader owner's root report without assuming terminal coverage.
`GroupScopeReporting` propagates these reports through unannounced groups and cancelled
producers to every missing task. Closing the announced-group case alone does not establish
`Terminal`; the complete construction additionally uses execution-derived owner scopes.

`accepted_failure_reported` supplies the recorded-task origin without an additional future
notice premise. Settlement licensing provides a previously announced contributor. If a
group contributor closed early, its positive full-scope report covers the shared task; if
unfinished, its actual later closure counts the settlement. Stream items retain an open
singleton owner by licensing. Thus, after announced IDs close, every accepted task failure
has a covering report. The generated shared-owner regression checks this for arbitrary
admitted histories and cuts. Causally cancelled tasks without their own accepted settlement
still need report inheritance through unannounced owners and unavailable producers.

`UnannouncedGroupFailureOrigins` narrows that obligation using the retained reporting
frontier and healthy dependency satisfaction. An unannounced failed group must have a
failed defer ancestor or an unpublished structural producer. Strong ref descent then
shows that a failed contributing group either supplies an actual report for the task's
attachment or leads to an unavailable ancestral producer. The path proof uses the task's
own defer-map ancestors, not a claim that each group's full scope lies below its producer.
For work whose group descriptors are all roots, unavailable producers are impossible, so
the task-local report follows even without assuming every group was announced. The latent
shared-owner regression checks this conclusion over arbitrary closed reporting frontiers.
The general nested-defer case still needs to connect unavailable ancestral producers to
actual covering reports; this reduction does not establish complete-run existence alone.

`CausalTaskReportAssembly` uses the weaker task-local origin boundary directly. Its mutual
induction requests full scopes only for streams; deferred task attachments supply the
failed-owner origins, including the generating task of a stream whose dependencies fail.
`RootGroupReportingExistence` combines this assembly with the retained frontier and accepted
settlement reports. It proves complete finite runs for coherent work whose defer descriptors
have no structural producer, including nonempty defer dependencies and nested streams,
without assuming every group is announced. The generated latent-owner fixture now checks
complete-run existence as well as accounting and ID closure. Produced defer descriptors
remain the open case for the general mixed-work existence witness.

Structural producer ref bounds are separate from healthy work availability.
`producer_owner_ref_le_structural` derives a no-larger producer owner for any generated
task owner, including cancelled tasks. `stream_producer_owner_lt` derives a strictly earlier
producer owner for a produced stream even when it has no items. Both use only ref/ancestry
coherence, defer continuity, and stream-owner ordering; they assume no notice, publication,
report, or source policy. Nested-stream regressions cover arbitrary fixed outcomes, including
raw zero-count failures, since these ordering facts do not require positive-error reporting.

`BoundedTaskReportAssembly` gives the induction step for unavailable producers. A cancelled
task with one owner below a chosen ref bound needs task-local failed-owner reports only
below that bound. Producer support retains a no-larger ref; stream dependencies and stream
producers have strictly smaller refs. Ordered-cut assembly retains the same bound while
using actual reports for accepted failures. The nested-stream regression applies this result
to arbitrary explained histories with closed announced IDs, without a terminal premise.
The general defer proof uses structural owner-scope evidence so an unannounced group's
unavailable producer has an earlier owner whose report can cover the group scope.

`GroupProducerOrigins` is a stronger sufficient certificate for selected work shapes. Each represented
group ref has a root descriptor, or a descriptor whose introducing producer has an earlier
contributing ref and an attachment covering the group scope. Other reused descriptors may
have narrower producers; the certificate requires only one suitable origin. It contains
no event history, notice, cancellation, error count, or reporting conclusion. Root-group
work supplies it directly. A generated regression supplies it for deferred groups inside
stream items, where each group's defer ancestry is empty and its producer is an item task.

Given those origins, `failed_owner_reported_of_group_origins` constructs task-local scopes
by strong ref induction. Unavailable introducing producers are cancelled by actual work
accounting; bounded assembly uses only recursively proved earlier scopes, and structural
path prefixes reach the missing attachment. Announced positive failures and accepted
settlements are the observable report origins. The resulting cancellation assembly and
`mixed_completeRun_exists_of_group_origins` handle produced defer groups and nested streams,
without an all-groups-announced or root-group-only restriction. The generated stream-item
defer regression proves both complete-run existence and cancellation reporting for arbitrary
closed accounted reporting frontiers. It is not, however, a law of arbitrary root execution:
the generated `ScopeMetadata` regression proves a counterexample where a root-scope defer
group is introduced by a task attached at a narrower object path. There is no alternative
descriptor satisfying the stronger producer-payload premise. This refutes the proof helper,
not the public queue contract; the conditional results remain valid on their stated domain.

`GroupOriginComposition` supplies the structural composition rules for that derivation.
Embedding relocates an origin descriptor and its introducing task together, preserving
owner refs and attachment paths. Combined work retains origins even when refs repeat.
The proof-only `GroupOriginsExcept` certificate leaves inherited refs to an enclosing
component: `combine_resolving` can discharge a reused ref with an earlier sibling origin,
without requiring its narrower local producer to cover the original scope. Execution-group
and stream-item wrappers turn suitable child roots into actual producer witnesses; already
introduced child origins retain their internal edges. Structural regressions cover broad
reused scopes, fresh group children, streamed-item defer groups, and exhausted streams.
These composition rules preserve their stated certificates, but do not make the stronger
producer-payload premise a law of execution or strengthen the public conformance contract.

`ScopeMetadata` and `ExecutedScopes` prove the actual scope-ordering rules of arbitrary pure
execution: defer ancestors cover their child group's notice scope, and stream-item work
allocates all node scopes beneath its list boundary. Inherited scopes are not narrowed to
the current task's attachment. `ScopeProvenance.producer_owner_scope` derives a no-larger
producer owner whose notice scope covers the child owner's scope. `GroupScopeOrigins`
follows equal-ref producers through decreasing structural dependency ranks; it reaches a
root descriptor or a strictly earlier contributing owner with a covering notice scope.
`executeRoot_groupScopeOrigins` supplies this certificate for every root completion without
a caller premise. The generated regression satisfies this owner-scope certificate while
refuting the stronger payload-scope certificate. `BoundedOwnerScopeReporting` preserves a
chosen owner's full notice scope during mutual causal descent at ordered failure cuts.
`GroupScopeReporting.failed_group_scope_reported` then constructs every failed group scope
by strong ref induction at a closed, accounted reporting frontier. Actual positive notices
and accepted settlements supply the reports; failed ancestors and unavailable producers
only transport them. `cancelled_reported_of_scope_origins` supplies task-level cancellation
reports from those full scopes. `mixed_reporting_continuation` finalizes reporting-covered
prefixes using those reports, retaining the original batches. Execution derives every
structural certificate used by `executeRoot_completeRun_exists`; the existing
`queryOutcomeExists_holds` witness adds no public premise. Raw-work regressions explicitly
supply positive-failure certificates and actual terminal report scopes; generated queries
derive the same certificates from execution. These proof/test modules build with the
selected-cause definitions.
The broader-scope counterexample also has a complete-run witness. Axiom audits
of the new scope/reporting proofs and public query-existence witness contain only standard
Lean axioms. No public definition or admission premise changes are needed.

Settlement-prefix witnesses separate each accepted failure from the earlier cuts that
license it, including settlements sharing one output boundary. Singleton ownership then
forces the reporting owner to remain open at settlement: prior completion would contradict
either uncancelled licensing or the fixed failing payload. Together with positive failure
counts and coherent owner paths, closure of announced IDs supplies an actual covering
report without assuming `Terminal`. This singleton result does not restrict shared tasks,
which may settle after one co-owner closes.
For shared failures, the licensing prefix still retains a healthy unfinished contributor.
If every announced contributor has closed, that surviving contributor must be latent.
This derives work availability without incorrectly requiring an open owner at settlement
or imposing an immediate notice on a previously unannounced contributor. A previously
announced co-owner reports the accepted shared task even when it closed earlier. Retaining
the latent owner's notice can additionally report its broader private cancellations; those
require their own scope or an inherited ancestor report, not merely the shared-task report.
Internal accounting alone remains insufficient.

For the shared-owner fixture in `Tests/GraphQL/IncrementalDelivery/FailureScopes.lean`,
the reference runner announces the latent broader group and reports its retained failure.
This supplies the necessary root scope for its cancelled private task. The general
eventual-notice lemma also proves that scope from an independently admitted repaired
history, without assuming `Terminal` or supplying the desired report as a premise. The
general conformance proof also covers cancellation through producer/dependency chains and omission
of notices whose work is already covered by a reported scope; the fixture is a regression,
not an assumption of that proof.

Shared-initializer regressions check preservation of root data/errors, initial notice
ordering, reuse of initial IDs by subsequent mapping, and definitional agreement between
the reference and Execution initialization paths. The source assumptions and public
conformance/correctness propositions require no additional premises for this factoring.

See the [development guide](../development.md) for the verification workflow.

`SelectedFailureCuts` constructs a subsequence of source failure cuts in proof evidence.
Each retained cut has a contributor uninvalidated by the preceding selected cuts.
The defer-only licensing helpers use these selected cuts; raw accepted rejections can be
redundant and do not supply an uncancelled-owner witness. First-report placement retains
the selected positive cause of each completion rather than an additive owner-error total. Omitting
a redundant cut preserves group and group-record invalidation, including through later
failures. This selection changes no source handling or output; the runtime can retain a
redundant rejection on a dormant shared task. The overlapping-owner regression in
`SuccessCounterReplay` checks this case. Cancellation licensing and terminal reporting
are separate conclusions in the conformance proof.
Selection commutes with source-prefix concatenation and restriction to any output boundary.
`SelectedFailureCauses` then preserves a group's selected positive completion cause when
its ancestry is healthy at that boundary; execution's unit-cause theorem preserves the
reported count even when a different earlier contributor supplies the explanation.
`SelectedGroupFailureInventory` derives this cause preservation for every actual normalized
group failure from the source and start laws. The overlapping-owner fixture completes its
parent and checks the dormant child's later failure against the selected earlier cause.
`InformativeFailureInventory` merges selected object cuts with actual stream-failure cuts
and proves complete positive cause accounting, ordering, bounds, freshness, reachability,
and prior contributor announcements. The mixed contributor-health proofs use this same
selection. Canonical event admission and terminal reporting are rebuilt against this inventory.
`InformativeObjectFailureSafety` and `InformativeStreamFailureSafety` license that same
inventory from the shared successful-item safety certificate. Their combined failure
witness preserves the original cut ordering and matching. The canonical successful-item
construction now uses this selection, and mixed failure-witness existence again follows
from execution-generated work and the original valid/started source laws. The overlapping
failure fixture checks a licensed witness for its actual completed replay. Failed-completion
admission uses each reported positive task cause, rather than an aggregate node-error sum. The reference
conformance proof and query-observation bridge use that selected-cause inventory.
Canonical group notices retain nonempty task memberships at their exact owner-fold or
drain boundary. Task registration supplies producer readiness and the common publication
ledger excludes earlier publication; notice eligibility needs no per-group failure cache.
The source-handler/object-prefix bridge is independent of failure-cut selection.
Canonical publication and control admission now share these contents, notice freshness,
ancestor completion, and the selected failure witness. Rejection-drain notice separation
uses the entire owner-completion block. Endpoint accounting transports group invalidation through the selection instead of
requiring every redundant raw token in the witness. Actual source rejection and terminal
exhaustion supply observable covering reports. The reference conformance proof combines
these results with event admission. The optional native-refinement proofs establish their
separate finite correspondence statements, without certifying an actual host runtime.

Generated replay again proves healthy uncancelled retirements, active-root ancestry, and
missing-parent boundaries. Successful owner settlement derives nonfailed memberships from
the success-only pending ledger; rejection draining derives them from unrejected task
lookups. These proofs use retained task rejections and contain no executable health guard.
`TaskNodeKeys` proves that computation keys remain unique through raw queue transitions.
`ActiveRejectionReplay` combines that map invariant with source-derived ownership and
complete drains: no active owner retains a replayable rejection at a handler boundary.
This discharges the active-counter readiness proof from the original source assumptions.
Failed group completions also have healthy ancestry at their actual source-handler cut.
This covers fresh failure owner passes and rejection drains after successful object or
stream-item preparation, including a replay that closes several active owners.

The proof is restricted to finite execution-generated work and valid host sources.
It does not establish completion from every admitted prefix, host fairness, eventual
resolver settlement, an infinite-run semantics, or refinement of the actual GraphQL.js
runtime. The [semantics guide](semantics.md#remaining-research-frontiers) separates these
open questions from the conformance proof boundary.
