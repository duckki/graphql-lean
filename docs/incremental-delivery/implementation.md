# Reference work-queue implementation

The executable reference machine was based on GraphQL.js `v17.0.1` at
[`9617473`](https://github.com/graphql/graphql-js/tree/961747301cf70e59aead2d7a5121779a79a52877).
Cached-failure reporting follows GraphQL.js
[PR #4870 at `299a279`](https://github.com/graphql/graphql-js/tree/299a2792ccb325b04cc8a01adc3c9ee162393eea).
Its authoritative target remains the incremental-delivery draft at
[`045e193`](https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec),
interpreted through the independent [work-queue contract](semantics.md).
The error-count representation already abstracts the draft's singular error object.
Collecting several cached task causes extends its singleton failure-mapping algorithm.
This is a finite Lean reference implementation, not refinement of JavaScript's async runtime.

Public definitions retain ordered fresh group declarations and observed FIFO positions
of internally queued group failures, including synchronous initial rejections. These revised
modules also retain callback eligibility from earlier intermediate states within one host
batch. Initialization and source validity share an optional startup observation,
defaulting to empty. The empty-startup specialization preserves ordinary activation for
every kernel work value; its source validity is equivalent to the original asynchronous
source laws. The independent work-accounting contract and public correctness propositions
are unchanged.

Group registration follows GraphQL.js's parent traversal. `State.addGroups.go` visits
candidates in encounter order and recursively visits a candidate parent before its child,
using a temporary visited set. `State.addGroup` installs the record only if its parent
is live, attaches its child link immediately, and retains first-registration/failure
history for repeated raw-fixture ancestry. Child links and returned roots follow actual
installation order; the recursion depth is bounded by the candidate count plus one.
This traversal does not require a sorted or already parent-first declaration list.

Generated declarations can be child-first when an immediate field merges selections from
a deferred occurrence. The `GraphQLJsAlignment` fixture checks `user { name }`, deferred
`P { user { ... @defer(label: "C") { age } } }`, and
`users { ... @defer(label: "A") { name } }` with two users. Pruning P's empty shell promotes
C before the unrelated A roots. Both queues and the pinned GraphQL.js implementation
produce initial labels `[C, A, A]`, wire IDs `0, 1, 2`, and the corresponding payloads.
Nested child-first candidates additionally check child-link order, duplicate visits, and
refusal beneath failed or successfully retired parents. These are definition-level checks;
the recursive traversal now preserves live-ref uniqueness and initial pending counts through
`RegistrationTraversal` induction. Task-membership uniqueness, pending-token accounting,
registered/started-task provenance, permanent retirement, stream-root frames, and causal
cancellation inheritance also compile for this traversal. Refused-child retirement uses
the actual absent-parent premise; a live parent is installed normally even in raw states
with inconsistent cancellation history. Registration also preserves sound and complete task
links, healthy pending counts, retained task rejections, and record-aware cancellation
provenance. Live-ref preservation allows parent metadata replacement and retains an actual
representative of the same ref. Registry coverage now proves that every visited candidate
is registered when its traversal returns, including child-first declarations and scope-local
visits awaiting an ancestor caller. Unsettled task links and pending lower bounds compile.
Internal controls retain current-head eligibility, and admitted stream item callbacks remain
live from their earlier eligibility boundary through consumption. Parent-link and healthy
installation proofs retain the execution-derived declaration context.
`RegistrationParentTraversal` proves that
candidate parents are permanently registered before each child installation, using acyclic
creation refs and a bound on distinct visits. It preserves encounter order and adds no
ordering requirement on the candidate list or restriction on the public source.
`RegistrationSupport` proves liveness from a fresh ancestry chain ending at a live record
or a parentless declaration, with parent closure supplied by the execution context. It also
derives such support below a protected live ancestor. These are proof certificates over
existing state and immutable work, with no new source law or runtime metadata. Healthy
contributor integration now uses these support chains and execution-derived parent closure;
fresh stream-item candidates derive support from region separation. Descriptor provenance,
canonical parent links, duplicate-free child links, and membership order compile for the
recursive installer. Healthy owner accounting now retains those registration frames through task and stream
integration. Healthy retired-ancestor evidence derives complete support chains below a live
producer owner, and new root provenance follows recursive installation directly. Their
end-to-end replay consumers retain the same derived registration frames. Recursive
registration also
preserves existing live paths and excludes links from fresh groups into the entry registry.
Its root frontier is duplicate-free because each emitted ref is permanently registered
before another candidate can emit it. Stream records and termination are unchanged by
registration. Immediate parent-link completeness now follows each installation, using
registered parents of live children. Refused children below absent registered parents
inherit retirement certificates whether the parent completed successfully or was removed
by failure. Cancellation-report provenance follows only the branch that actually records
a cancellation marker. Health of refused fresh records additionally uses retained-failure
accounting: no recorded failure contributes to an unregistered ref, while its absent
uncancelled parent retired healthy. The release-health frame carries live registration
coverage through integration, pruning, and draining. These distinctions are proof evidence,
with no runtime change. Uncancelled ancestor-marker closure also follows refused-child
inheritance. New task contributor presence is derived after the actual group-registration
stage: an absent uncancelled contributor would retire a still-live producer owner. Fresh
stream-item contributors use complete fresh parent-chain support. The cancellation-aware
handler proofs use these constructed facts through startup and the ready drain. Their
source replay now retains every earlier eligibility frame within each batch, follows
realized enqueue effects, and treats internal controls as value-free. Successful carrier
retirement and stream-item completion use the same dispatched queue boundaries.

Batch admission additionally covers a child task started by P's completion and retired
by A's failure before its own notification is consumed. The `GraphQLJsAlignment` fixture
uses P containing `a`, A containing `first: required` and `second: required`, and B sharing
`second: required`. Both queues complete P, A and B with error counts `[0, 1, 1]`.
Retaining that callback preserves the rejection available to B's startup. The admission
predicate accumulates earlier eligibility locally, preserves the full rejection snapshot,
and checks internal notices only against the current FIFO head. `InputReplay` proves prefix composition with accumulated eligibility and an actual earlier
dispatch-boundary witness for every admitted callback. `FailureProjection` retains the complete
admitted failure inventory through these batches. Callback, source-admission and
conformance proofs use this same source domain. Healthy-counter
and rejection-retention replay now retain prefix invariants at every earlier eligibility
boundary, using the original full availability snapshot. This supplies disposition and
permanent-task evidence for callbacks that start and retire within the same batch.
Failure-reporting announcement evidence uses that actual earlier eligibility boundary and
transports its notices through the remaining output prefix. Structural retirement replay
and produced-group coverage retain execution-derived parent closure when integrating child
work. Fresh parentless root liveness and frontier coverage now follow the recursive
installer under canonical descriptors and live registration coverage. Fresh regions and
initial root coverage derive full ancestry support from their execution certificates.
Closed owner replay retains all earlier eligibility frames, and live-root and task
completion bridges carry the actual child-parent registration context.

`ControlEligibility` derives current-head permission from enqueue permission and the
source's existing nonrepeating closure identities. Ordinary dispatch only appends notices;
a different closure cannot consume the pending head. The same permission survives complete
host batches, including terminal bookkeeping, without an additional source law.

The declaration-transparent structural navigation and finite observation-token bound compile.
Mixed response slices, cursor seeds, positive execution errors and declaration-independent
stream allocation projections also compile, as does the empty-startup activation specialization.
Execution-derived path, ancestry, descriptor, role, allocation-region and stream-owner
certificates also compile for declarations. Source labels, typed slices, reconstruction,
attachment, cursor-origin and selected-cause proofs retain the same task addresses.
Declaration inventories now supply bounded, canonical group records independently of task
support. Scope provenance, finite failure coverage, event payload provenance, and the
base group-ref, task-membership and retirement invariants compile with FIFO dispatch.
Execution also proves a declaration-context certificate for all nested work: sibling
declarations are available at integration, deferred children inherit that context, and
stream items restart it. Lowering and registration frames now retain both immediate
contributor coverage and future child contexts through batch-aware dispatch. Permanent
registration refs are proved to lie in already exposed regions, including taskless
declarations. All-owner pending accounting, canonical parent/child links, producer
location transport, cursor resumption and startup source-language clauses also compile
with retained FIFO state. Failure origins distinguish direct task rejections from forwarded
notice heads. Healthy registered-owner accounting accepts inherited registration contexts,
and started-task retirement, healthy-counter replay, owner replay and cancellation replay
follow actual FIFO dispatch. Execution maps also certify the earlier or incoming
registration of every declaration parent. Child contributor availability follows defer
continuity without requiring a repeated declaration. Child lists remain unique and live
group memberships retain task registration order. Parent-registry closure, consumed
rejection retention, complete-or-retired task links and stored-value provenance also
compile through the revised dispatch. Singleton task-cache explanations remain distinct
from queued aggregate reports. Exact stream-item publication and buffered membership
preservation compile with FIFO controls. Structural retirement replay carries derived
registration frames when revealing task children. Cancellation retirement needs only
registration of live groups, which is proved for arbitrary internal work. Ownership
closure derives all child-availability obligations from retirement and region evidence.
Output shape, publication/closure adjacency, stream source order, buffered links and
registered membership exclusion compile through the ordinary FIFO runner. Contributor
and child-stream provenance, cancellation monotonicity and stream-release publication
witnesses also follow dispatch with retained pending notices. The per-handler and source-replay
publication ledgers cover explicit control forwarding and realized enqueue effects;
group/stream ref support
uses the same realized FIFO transitions. Prior-announcement accounting retains evidence for both live roots and pending
notices, deriving each queued control's history from enqueue effects. The normalized
failed-closure announcement theorem compiles without assuming source matching, accepted
starts or output admission. Closure uniqueness also compiles with separate removal and notification ledgers.
Pending refs are derived to be distinct retired groups; notification completion additionally
requires absence from the pending FIFO. Ordinary handlers reserve new notices and dispatch
consumes old heads. The normalized once-only closure result adds no source-law premise.
Stream-action order, task announcement tracking, root-preserving item integration and
value conservation also compile through realized dispatch. Successful and failed closure
announcement order retains pending notices across batch boundaries, and notice tracking
continues to distinguish active, cancelled and completed groups. Closing descriptors
retain registry provenance while their notices wait, and cancellation
report accounting carries actual output together with the remaining FIFO. Empty pending
state recovers actual-output reporting without moving controls across a batch. Stream
completion order, buffered-owner conservation, parent-link preservation and initial/fresh
root coverage compile with declaration contexts. Continued openness and failure-cut
licensing remain separate. Notice freshness uses derived pending-control retirement rather
than treating every removal as an already emitted closure. Buffered carrier publication
and complete canonical parent-link replay now retain the declaration registration frame;
stream notice metadata and producer provenance follow actual dispatch. Prepared carrier
replay begins after enqueue effects, and buffered item handlers retain child declaration
contexts. Notice registration, healthy produced-group coverage and inverse stream
lowering compile at those actual integration boundaries. Producer support and integrated
root coverage now apply directly to child task contributors, including inherited refs
without fresh declarations. Actual batch registry freshness, stream attachment replay
and item-release conservation retain the same FIFO state. The common normalized
publication ledger now uses the ordinary runner for both asynchronous and pending-startup
queues, with no separate first-batch failure parameter or forwarding accumulator.
Live-root replay carries the execution-derived registration context through successful
child preparation and actual FIFO dispatch. Source-success reachability omits internal
controls, which produce no successful task identity. Source-output blocks now preserve
each realized dispatch, including labeled internal notices and silent handlers. Only batch
termination is unlabeled; the trace agrees with the actual queue, publisher and atomic
output across the original host batches. The task-drain root-presence helper retains
the actual incoming-task lookup, and root-presence replay handles control forwarding
without changing live group records. Successful carrier origins and exact source-item
prefixes use those same dispatch blocks. Nonterminal output agrees with actual fixed-
snapshot replay, while termination remains a batch-boundary operation. A terminated
initialized queue is now proved to have an empty internal-notice FIFO as well as empty
roots. Arbitrary-publisher trace agreement uses the same ordinary runner. Task-success
completion accounting derives inherited owners from its registration context. Exact raw
output cuts retain the actual FIFO state; projected item/object offsets are derived from
those exact prefix equations rather than a separate replay proof. Owner existence carries
the same derived registration context through cache-aware batch/FIFO replay. Stream
completion tracking uses realized dispatch; item-group completion uses the executed item
certificate, and owner-notice ancestry retains the actual incoming-task lookup.
Distinct aggregate cause provenance now reaches every normalized group report and its
source-output block through the retained FIFO. `SourceBlocksHaveFailureTotals` uses the
complete retained rejection inventory, including callbacks later in the same host batch;
it does not assert that every cause has already been consumed at its report. The former
notification-prefix claim is removed. Causal/reporting cut licensing, startup adaptation
and end-to-end replay use separate availability and causal inventories.
`ReportingCutSelection` proves that first-occurrence
selection retains ordered candidate positions, produces fresh reporting entries, and
preserves an equal-or-earlier reporting cut for every causal candidate. `ReportingCauseCuts` places each exact aggregate cause at its actual atomic report.
`AvailableObjectFailureCuts` interleaves these positions with source settlements and
retains each occurrence at its first available cut. `ObjectFailureCuts` proves genuine
reachable failure provenance, exact positive aggregate counts and group invalidation by
every report position. `CompleteMixedFailureCuts` and `FailureInventory` use these availability cuts for exact
aggregate reporting. `SelectedGroupFailureInventory` preserves group invalidation when
causal selection removes redundant causes. `ReportCutAnnouncements` derives a previously
announced contributor for every report-cause candidate at its actual cut. `SourceHandlerBoundaries` retains actual FIFO queue/publisher cuts.
`FailureAnnouncementCuts` now derives a complete fresh reporting witness with previously
announced contributors for both callback and aggregate-report candidates.
`InformativeFailureInventory` selects from this common availability inventory and derives
ordered causal provenance, group invalidation and prior announcements. Historical
cancellation exclusion and end-to-end admission follow the selected causal inventory.
Buffered-owner and uncancelled-owner preservation
use derived registration contexts for inherited contributors. Notice-completion handlers
retain the actual incoming-task lookup, and stream registries follow dispatched FIFO
state, including internal failed-group controls. `FifoGroupCompletion` tracks announced groups
as active, pending, or actually completed. `GroupCompletionReplay` composes that evidence
over dispatched inputs and host batches; its terminal theorem requires the independently
proved empty pending FIFO before treating failed groups as emitted completions. Internal
controls also preserve stream-announcement inventory and source-settlement projections. `ConformanceBatchShape` now derives
the canonical nonterminal history and exact final termination marker from ordinary replay.
Batch and stream source boundaries retain explicit internal controls at their real FIFO
positions. Stream-announcement uniqueness composes over dispatched state, and object
producer support remains transparent through declaration wrappers. Terminal-block
projection now uses the shared ordinary runner, including queues with initial pending
controls. Cached-report candidates also lie within that exact nonterminal history.
`ConformanceFailureHistory` now transports the complete reporting witness and selected
causal inventory onto one canonical event history while retaining reporting availability
for every causal occurrence. `MembershipExclusionWitness` composes published-membership exclusion over
post-enqueue dispatch states and treats failed-group controls as value-free. Internal
owner-fold and drain boundaries retain the same dispatched handler slice for their
published-membership exclusion evidence. `ContributorStreamCoverage` now carries the derived
registration context through fresh item integration. `DeclarationParentOrder` derives
local parent-first declaration order directly from GetNewDeferMap insertion and stable lookup,
relative to the inherited map. Complete generated chunks may nevertheless be child-first;
parent-cut proofs use recursive registration rather than an unconditional empty-context
lowering claim. The
`DeliveryFailureReporting` fixture now consumes explicit internal controls at their actual
FIFO positions. It verifies that a host-batch boundary retains a queued aggregate notice
and does not terminate early, while cached and split outcome batches retain their
respective aggregate counts and exact output traces.
`ContributorCoverageReplay` derives healthy contributor root coverage through actual
FIFO dispatch and cache-aware host batches, carrying execution registration contexts.
`CompleteFailureOutput` preserves task-local cached causes through internal controls. Its
single-cause output lemma applies to ordinary task/stream handlers; aggregate internal
controls use the independently proved distinct-cause reporting inventory.

`TaskOutcome` still separates collected diagnostics from the selected task-boundary cause.
Execution-generated task failures select one primitive error. At group startup, each
retained started task contributes its cached rejection, in task registration order.
A nonempty collection closes only that group, skips its private tasks, and queues one
completion containing the sum of the selected counts. Pending tasks contribute nothing
and are not awaited. A newly received failure on an active group still reports only its
triggering task cause. Stream failure and delivered partial-data diagnostics are unchanged.

The queue stores rejections on `TaskNode`, with no group-level error or provenance cache.
`startGroup` returns `GroupFailureEvent` enqueue effects separately from immediate outputs.
Initialization and `dispatchGraphEvent` retain them in `State.groupFailureEvents`, a FIFO
projection of native internal queue entries. `handleGraphEvents` consumes the complete
observed dispatch order, including `GraphEvent.groupFailure` among task/stream outcomes.
An internal notice must match the current queued head; forwarding uses the stored payload.
There is no batch-end relocation. Termination requires both root collections and the pending
notice FIFO to be empty. Removal still occurs during startup, and the temporary `errors`
collection stays local to `startGroup`, as in GraphQL.js.
The host batch supplies available failure outcomes separately from FIFO notification
consumption. `cacheTaskFailures` updates only started computation nodes; `startTask`
exposes a supplied outcome when that computation starts. This finite availability adapter
specifies no promise microtasks, wall-clock timing or fairness. Input batching therefore
also determines which failures are available at a group start. A finite input batch is
not claimed to equal a native Queue generator batch.

`FailureWitness` continues licensing causal cancellation with the uncancelled premise.
`FailureReportingWitness` records available rejections, including causally redundant ones,
with fresh identities, reachable work and previously announced contributors.
`CausalFailuresAvailable` links each causal occurrence to reporting availability at or
before its causal cut, so later causal acceptance can reuse an earlier cached rejection.
`NodeFailureCauses` permits a nonempty set of
distinct supported task causes for a group; streams retain `NodeFailureCause`.
Neither relation permits collected nullable diagnostics or invented positive counts.

The `GraphQLJsAlignment` fixture checks both queues against native counterexamples:
cross-path registration and activation, skipped private work, cached multi-task sums,
completion order and shared-value wire ownership. `InitialFailureStartup` checks initial
synchronous versus asynchronous rejection availability. Positive terminal
scope reporting, healthy publication support and wire lifecycle remain separate contract
obligations; no new proof or source premise is assumed to discharge them.

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
The [definition correspondence](graphql-js-correspondence.md) maps every public queue
declaration to its upstream symbol, extracted code, or Lean-only responsibility.

## Executable pipeline

```text
Observed GraphEvent FIFO batches (outcomes, child work, internal failure dispatch)
    → State.handleGraphEvents: queue state + raw WorkQueueEvent batches
    → IncrementalPublisher: effective-owner selection + normalized events
    → spec response mapper: pending, incremental, completed, hasNext
```

Inputs describe settlements and internally queued notice dispatch, not publications. A settlement can remain buffered, emit
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
`streamItemWork?` project one shared `taskContext?` lookup in the original execution tree.
It validates the address, task kind, and item index, then supplies the exact deferred
contributors and lowered child work. `TaskLookup` proves the three projection equations
for arbitrary work, without generated-work or source premises. Queue task/stream records
contain bookkeeping, not
resolver computations or retained execution subtrees.

Generated work records ordered fresh declarations in `Execution.Work.declareGroups`,
separately from task contributors. The annotation follows immediate-field work and precedes
the plan's tasks. It adds no structural address edge or task count. Lowering preserves this
order; pruning promotes child frontiers without sorting numeric object references.
`Task.groups` contains only actual contributors. Raw fixtures must declare group candidates
explicitly, including taskless ancestors. `State.registeredGroups` prevents repeated descriptors
from recreating retired nodes; `State.cancelledGroups` distinguishes failed retirement from
successful shells during late registration.

### Host events

| GraphEvent | Payload and meaning |
| --- | --- |
| `taskSuccess` | Task occurrence, object data, path, counted errors, contributor descriptors, and child Work. |
| `taskFailure` | Task occurrence and its selected delivery-failure count. |
| `groupFailure` | Observed dispatch of an internally enqueued notice; must match the pending FIFO head. |
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
started task/stream descriptors, initial notices, pending internal failure events, and a termination flag. `GroupNode`
stores child links, task memberships, and pending count, matching GraphQL.js's group
bookkeeping. `TaskNode` stores its task, an optional settled value, a retained rejection,
and produced child streams. The rejection represents the cache on GraphQL.js's task
`Computation`; there is no per-group failure cache or stored failure-origin occurrence.
`startGroup` inspects group tasks in registration order using a local `errors` list.
Finite lists implement keyed maps and ordered sets.

`State.initialize` integrates immediate work, prunes taskless group shells, starts the
remaining roots, and records initial notices. Starting work records eligibility for host
events; it does not run a promise or iterator.

| Transition | Behavior |
| --- | --- |
| `taskSuccess` | Store a present task's value, integrate children, decrement surviving counters, and release groups through cached-failure inspection. |
| `finishGroupSuccess` | Publish stored values once, remove shared memberships, close the group, and promote children/streams. |
| `taskFailure` | Retain the task's rejection and close its active owners. Dormant owners keep the task and its pending count for later replay. |
| `startGroup` | Inspect all cached task rejections before starting private work; close the group and return its aggregate notice as an enqueue effect. |
| `drainReadyGroups` | Close successful zero-pending groups and inspect newly released groups; active failures await their FIFO task input. |
| `streamItems` | Integrate item children, activate roots, emit items and new notices, then drain ready groups after the carrier event. |
| `streamSuccess` / `streamFailure` | Close the active stream without retroactively cancelling work released by earlier published items. |
| `handleGraphEvents` | Expose available computation rejections and dispatch the observed FIFO, retaining new internal notices until consumed. Terminate when both root collections and pending notices are empty. |

`pruneEmptyGroups` tests empty task membership, not merely a zero pending count:
settled values or rejected computations may still await release.
`removeGroup` cancels dependent descendants while retaining tasks with surviving owners.
Missing stale child links do not consume its live-node traversal budget.

Both task handlers use task-node presence, as GraphQL.js does. Removing the final owner
removes that node, so later callbacks have no effect. A surviving dormant owner retains
its shared task even after another owner closes. Semantic failure/cancellation evidence
belongs to the independent history contract; it is not an extra runtime health gate.

### Initial activation and declaration order

GraphQL.js starts initial roots sequentially when its Queue starts. An earlier computation
can synchronously cache a rejection observed by a later root before `TASK_FAILURE` dispatch.
`InitialStartup.failures` supplies that observation. `State.initialize` exposes
it only when the task starts and stores any resulting notices in `groupFailureEvents`.
The original initial-announcement inventory remains intact even when startup removes a group.
Empty startup observations specialize to `State.initialize`; first-batch notifications do
not by themselves make a failure synchronous.

The ordinary runners retain pending notices across all batches and empty calls. No separate
startup tail or special first-batch forwarding is needed. `GraphEvent.groupFailure` supplies
its observed FIFO position and is accepted only for the current pending head. The source
still abstracts external callback enqueue timing; native source realizability is not proved.

Group creation refs are not a global activation order: nested immediate fields can register
new groups before the enclosing plan's earlier-created groups. Explicit `declareGroups`
annotations retain native `Work.groups` insertion order, including later release boundaries.
Both queues share this lowering and preserve its order through pruning.

### Proof modules

The following inventory describes the proved witnesses and their module organization.
Declaration annotations retain structural addresses, and replay arguments follow queued
state through actual FIFO dispatch. Numeric declaration sorting is absent.
`ActiveFailureCaches` and `FreshIntegration` preserve rejection-free groups and fresh
pending counts through the actual recursive installation traversal, including parent-link
updates and refused child installation.

[InitialStartupReporting](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupReporting.lean)
proves preservation of the exact initial notices, positive queued counts and distinct
supported task causes in the retained state FIFO. `BatchedNoticeHistory` preserves ordered
announcement evidence through actual dispatch, independently of pending failure controls.
[InitialStartupFrames](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupFrames.lean)
derives live-task ownership and the removal forest before and after initial activation.
Both frames retain the queued startup controls in the actual initialized state.
`CanonicalStreamCompletion` uses empty roots and an empty pending-control FIFO at
termination to discharge every announced stream.
The [InitialFailureStartup fixture](../../Tests/GraphQL/IncrementalDelivery/Fixtures/InitialFailureStartup.lean)
checks three shared roots: synchronous first/second failures produce counts `[1, 1, 2]`,
remove the third root immediately, and never start its private task. The asynchronous
specialization reports `[1, 1, 1]`. A nested case checks the declaration order of later
released roots. Universal startup conformance follows the ordinary retained-FIFO runner.

[InitialStartupReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupReplay.lean)
derives initialization and prefix closure from the ordinary runner with persistent
pending-notice state and explicit internal FIFO dispatch. Accounting and termination
must use those same actual input and output histories.

[InitialStartupAccounting](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupAccounting.lean)
derives canonical parent links, pending counters, unsettled owner links, source regions,
and producer registration at the startup-aware initial state. These certificates include
tasks skipped after an immediate rejection. Cache exposure does not count as a consumed
settlement; startup removal preserves the accounting of surviving groups. The preparation
equation retains queued failure controls, and registration frames carry the execution-derived
declaration context. An empty initial cache produces no queued failure controls.
`InitialStartupRetirement` and `InitialStartupRootCoverage` derive owner links,
cancellation retirement and surviving root coverage from recursive parent registration.
Pending notices and initial-envelope metadata do not alter those structural certificates.

[InitialStartupRetirement](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupRetirement.lean)
derives live supported roots, uncancelled owner links, and closed retirement through
synchronous activation. Its cancellation markers denote permanently retired groups.
[InitialStartupSourceFrames](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupSourceFrames.lean)
combines these certificates into `UncancelledReplayFrame` for the startup-aware initializer
and every admitted batch endpoint or FIFO prefix. These proofs use matched cached task
causes, execution-derived declaration contexts and actual source-start checks; they add
no output-accounting premise. The output
explanation and terminal-reporting construction for nonempty startup observations remains
separate from these state invariants.

[InitialStartupOutputBlocks](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupOutputBlocks.lean)
proves exact queue, publisher, and atomic-output agreement for the ordinary runner from
any initialized queue. `sourceBatchBlocks` and `sourceRunBlocks` retain pending startup
notices in queue state and label their actual dispatch entries. Only terminal bookkeeping
is unlabeled; no first-batch forwarding tail is added.

[InitialStartupBatchShape](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupBatchShape.lean)
derives exact atomic batching for startup-admitted output. The generalized output-shape
proofs retain nonempty payloads and batches, all initial aggregate reports, and one optional
final termination marker matching the concrete flag. `StartupFullAdmission` retains this
shape on its shared admission witness; `StartupConformanceCertificates` adds all terminal
accounting on that same history, matching and failure inventory.

[InitialStartupReportingAvailability](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupReportingAvailability.lean)
constructs one fresh reporting witness at the initial output cut from supplied synchronous
failures with initially announced contributors. Every initial aggregate has distinct,
reachable task causes in that same witness at all later output cuts. Reusing earlier
availability introduces neither duplicate reporting occurrences nor causal settlements.
[InitialReportingMerge](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialReportingMerge.lean)
combines this initial witness with any later licensed reporting witness, retaining earlier
initial cuts for repeated occurrences. The combined witness remains fresh and ordered,
preserves all later available causes and their causal-availability links, and supports every
initial aggregate. `StartupCompleteFailureInventory` and `StartupCausalFailureInventory`
supply the actual startup source reporting and shared causal inventory.

[InitialStartupAnnouncements](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupAnnouncements.lean)
derives historical contributor notices for startup-aware task activation, normalized
replay, and within-batch lookups. Every admitted task-failure notification has a contributor
announced before its actual handler boundary, whether eligibility comes from batch entry
or an earlier intermediate FIFO state. The owner can have closed earlier; the witness
records its historical announcement without assuming it remains open.

[InitialStartupCausality](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupCausality.lean)
selects informative causal failures from initial reporting availability at output cut zero.
Producer-free task descriptors and root-region exposure establish that each selected
failure was uncancelled by its selected predecessors. The resulting `FailureWitness`
preserves all initial group invalidation and proves every initial aggregate's group failed.
Reporting still uses all distinct available causes; causal selection changes no execution
or diagnostic total.

[InitialStartupCancellation](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupCancellation.lean)
connects actual initial cancellation markers to the licensed initial causal inventory,
including taskless descendants removed through canonical registration links. The proof
licenses only rejections inspected at announced roots; unused observations of dormant
tasks supply no cancellation premise. Causal selection preserves the resulting cleanup
evidence as well as contributor invalidation.

[InitialStartupOwnerAccounting](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupOwnerAccounting.lean)
establishes the healthy-owner replay ledger after synchronous initial activation. Surviving
groups retain exact counters and canonical records, cached rejections have announced task
support, and healthy contributors retain their unsettled memberships. The ledger keeps
consumed notification history empty while using initial reporting availability for its
failure coordinate; it assumes neither output admission nor terminal accounting.

[InitialFailureOwnerReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialFailureOwnerReplay.lean)
carries that ledger through source-valid host batches and their FIFO prefixes. The joint
retirement and region frame derives registration availability inside the induction.
Initial reporting causes remain in the available inventory as consumed notification
history grows; each FIFO cut additionally sees its entire current batch's failure snapshot.
State replay retains the original host batch boundaries and changes no public contract.

[InitialStartupOutputCuts](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupOutputCuts.lean)
uses the ordinary source-cut lemmas to locate labeled blocks in the actual batch/FIFO
trace. Composition preserves pending controls in queue state, exact preceding output
blocks and all actual input labels. No batch implicitly flushes an initial notice tail.
[InitialStartupFailureCuts](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupFailureCuts.lean)
uses these positions and historical contributor announcements to license source task
failures at their exact output cuts, including failures whose handlers emit no output.

[InitialFailureTotalsReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialFailureTotalsReplay.lean)
preserves distinct aggregate source totals through FIFO handlers and once-only startup
forwarding, using exact rejection matching independently of notification freshness.
[InitialStartupFailureTotals](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupFailureTotals.lean)
instantiates that proof with only initially announced reporting observations. These are
proof descriptors of available rejections; no synthetic inputs are added to replay.
Every actual failed-group output block retains its complete distinct cause collection
and exact sum, including later groups that reuse an initial cached rejection.

[InitialStartupObjectReporting](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupObjectReporting.lean)
constructs one fresh licensed reporting inventory for every actual group failure after
startup. Later source observations retain their exact output cuts and reachability;
repeated initial occurrences reuse their earlier availability. Every group aggregate,
including a delayed startup notice, has all its distinct positive causes and exact total
in this joint inventory. Causal cancellation licensing and stream reporting remain
separate obligations.

[InitialStartupPublicationFrames](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupPublicationFrames.lean)
derives empty value buffers, exact child-stream provenance, ordered group memberships and
the remaining publication replay invariants after synchronous activation.
[StartupPublicationLedger](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupPublicationLedger.lean)
constructs one occurrence ledger for actual seeded publisher replay. The ordinary
`NormalizedClosureLedger` theorem specializes the same construction to empty forwarding.
[InitialStartupPublicationLedger](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/InitialStartupPublicationLedger.lean)
derives exact payloads, buffered/prepared closure coverage and stream-producer release for
generated startup replay without additional source assumptions.
[StartupClosureCoverage](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupClosureCoverage.lean)
shows that forwarding controls preserve the existing source-handler ledger interface and
its exact value offsets. This erases only object-free controls from that proof interface;
the actual publisher, its owner selection and its output history remain seeded.

[StartupItemPublications](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupItemPublications.lean)
proves exact source-item payload order and occurrence uniqueness for startup replay.
[StartupPublicationMatching](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupPublicationMatching.lean)
interleaves those items with the same object ledger on the actual atomic output. Its joint
matching proves exact payloads, fresh publication occurrences, earlier-item publication
and object/item-prefix coverage while retaining buffered/prepared closure evidence.
Every supplied item is published under this same matching, and every group-carried stream
notice has its exact structural producer published strictly before the carrier. Full
owner and notice admission remains separate from this provenance construction.

[StartupStreamNoticeMetadata](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupStreamNoticeMetadata.lean)
derives stream descriptors for all actual startup notices through the seeded publisher
and atomic projection. Initial group cleanup preserves the registered stream catalogue;
forwarded failed-group controls introduce no stream notice. Metadata does not assume
notice freshness, open owners, abstract admission or fairness.

[StartupItemStreamRelease](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupItemStreamRelease.lean)
connects item-carried stream notices to the exact inclusive source-item prefix through
seeded forwarding and normalization. The common startup matching therefore publishes
each item-carried stream's producer by its carrier, while group-carried stream producers
are published strictly earlier. These producer facts do not assume notice eligibility.

[StartupStreamSourceOrder](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupStreamSourceOrder.lean)
retains source stream-action and completion subsequences through actual seeded dispatch
and normalization. Valid source closure order therefore rules out atomic stream references
after closure, and every emitted stream completion retains its exact original source
payload. No generated-work, start or output-admission premise is needed for the structural
source projection; closure order additionally uses source validity.

[StartupCompleteFailureInventory](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupCompleteFailureInventory.lean)
combines initial/later object availability and actual stream-completion cuts into one
fresh, ordered inventory supporting every exact group aggregate and stream-error cause.
[StartupCausalFailureInventory](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupCausalFailureInventory.lean)
selects informative object causes while preserving group invalidation at every output cut,
and constructs compatible causal and complete diagnostic inventories on that same replay.
Each causal entry retains reporting availability. Contributor announcements and exclusion
of prior causal cancellation are independent licensing obligations; these inventories alone
do not establish output admission or terminal conformance.

[StartupStreamAnnouncements](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupStreamAnnouncements.lean)
derives strict notice-before-reference order from initial activation and actual seeded
replay. It supplies prior contributor announcements for stream failures without assuming
openness or abstract admission.
[StartupAnnouncedFailureInventory](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupAnnouncedFailureInventory.lean)
licenses the complete mixed reporting witness and transports historical announcements to
every selected causal cut through reporting availability. The admission construction uses
this inventory together with the independently derived cancellation exclusion.

[StartupNonterminalCuts](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupNonterminalCuts.lean)
transports exact startup source cuts across removal of the sole unlabelled terminal block.
Silent source blocks and all initial aggregate reports remain. The ordinary
`ConformanceFailureHistory` bounds specialize these same proofs to empty forwarding.
[StartupConformanceWitness](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupConformanceWitness.lean)
instantiates the existing `ConformancePlan.Witness` with actual startup nonterminal output,
exact batching and `AnnouncedFailures`. It preserves the selected stream-cut partitions
and every original failure index. `StartupFullAdmission` extends this same witness with
cancellation exclusion and full publication/control admission.
Startup raw output is ordinary dispatch output from the initialized state; pending
initial reports appear only when their queued controls are observed. `StartupGroupClosureMetadata` retains exact contributor descriptors through
the seeded publisher and atomic projection. `StartupStreamOpenness` combines those group
roles with exact stream metadata, prior announcements and source closure order to prove
that every actual stream reference is open, including when initial failures are forwarded.
`StartupStreamAdmission` transports exact actual atoms to the shared nonterminal witness.
It derives nonfailure stream health, full successful and failed stream-closure admission,
and `StreamPublicationReady`, including the unique healthy longest-path wire owner.
`StartupGroupClosureAccounting` proves distinct permanent retirements for the initial local
failure tail and all later actual group closures. Pending initial refs are already retired
and are disjoint from earlier emitted closures; ordinary handlers cannot close them again.
The seeded raw-output permutation is used only for uniqueness and retirement, preserving
the actual publisher order. Atomic group completions therefore have no earlier group
completion with the same ref.
`StartupGroupClosureNotices` retains strictly prior group announcements through the actual
seeded batch and publisher. Delayed initial reports use their original initial notices,
independently of current root liveness. `StartupGroupOpenness` joins announcement,
nonrepeating retirement and generated ref-role separation. `StartupEventCertificates`
therefore retains full failed-group/stream admission, successful stream admission and
stream wire-owner readiness on the same witness as batching, both failure leaves and
the shared closure ledger. Full value and successful-group admission use the additional
producer and carried-notice certificates below.
`StartupSuccessfulRetirements` recovers each successful carrier's actual batch/FIFO source
cut and transports its uncancelled retirement through the rest of that batch and all later
batches. `StartupGroupHealth` combines this with actual final replay frames and the separate
initial/consumed failure inventories to derive `GroupSuccessesHealthy` on the shared
witness, even after later failures. Successful group admission therefore retains exactly
its task-accounting and carried-announcement obligations at the original output cut.
`StartupOwnerPublicationFrames` interprets the shared source-ledger slice at actual startup
batch/FIFO cuts. `StartupCarrierCoverage` covers every structural object contributor of
the raw successful carrier. `StartupCarrierOutputCuts` retains that carrier's exact strict
object count under the actual seeded publisher across host batches. Forwarded diagnostics
carry no object values; this does not identify publishers or erase host cache boundaries.
`StartupGroupAccounting` interprets those same prefixes under the shared matching, proving
`GroupSuccessesAccounted` and retaining group health on the common conformance witness.
`StartupRawBatches` projects the actual seeded first raw batch followed by later host
batches. It retains every diagnostic control in its real position and normalizes to the
actual startup atom history under the same publisher. Its object projection agrees with
the shared source-handler ledger; publication/closure adjacency, contributor provenance,
nonempty values and exact successful source occurrences are preserved. This is proof
evidence, not runtime queue state or a flattened host-input replay.
`StartupPublicationHistory` identifies the exact actual raw-normalized positions and
nonterminal prefixes. `StartupGroupPublicationSupport` uses publication/carrier adjacency
to retain each object's actual release group and its known, open, healthy status.
`StartupGroupPublicationMatching` connects that same contributor-bearing value and object
rank to the witness's exact task occurrence and owner refs. These release certificates
share the existing history, matching, source ledger and cuts used by the subsequent
producer, wire-owner and admission certificates.
`StartupPublisherRegistry` preserves stream-role separation and group notice freshness on
the actual raw startup output. Every active publisher group ref agrees with an observable
open ref at that prefix, including initially failed groups awaiting forwarded completion.
`StartupGroupPublicationOwnership` therefore derives the actual longest-path open wire
owner, retaining the healthy release group as separate support. The selected wire owner
may still be a different failed co-owner.
Value projections and exact strict-prefix counts use the actual raw dispatch positions
on the shared source ledger.
`StartupSourceEventFrames` retains both sides of each actual startup FIFO input.
`StartupAncestorProducerCoverage`, `StartupPublicationProducerOrder` and
`StartupItemProducerPrefixes` establish structural producer order, including shared-owner
blocks, same-handler activation and item-produced groups. `StartupPublicationItemProducer`
and `StartupObjectProducer` interpret those exact prefixes on the existing matching.
`StartupPublicationAdmission` combines this producer readiness with healthy release support
and longest-open wire ownership. Every actual object atom satisfies full event admission;
publication support for both value kinds also rules out reviving cancelled tasks.
`StartupNoticeHistory` protects the complete historical initial group-notice inventory,
including synchronously removed groups. `StartupGroupNoticeMetadata` retains exact
contributing descriptors through the seeded raw replay and actual publisher.
`StartupGroupNoticeFreshness` derives global group-ref uniqueness and per-carrier freshness.
`StartupItemStreamFreshness` preserves the exact strict stream-notice prefix, excludes
prior announcements using permanent registration, and proves combined item-carrier notice
refs distinct. The projection bridge keeps the complete projected prefix, not only its
length. Eligibility also uses the retained contents and ancestor readiness below.
`StartupStreamInventory` proves globally distinct stream announcements through actual
startup state transitions. `StartupStreamNoticeDependencies` retains each group-carried
stream's releasing dependency. `StartupStreamNoticeAdmission` and
`StartupStreamNoticeFreshness` derive full stream-notice eligibility for both carrier
forms, including healthy completed dependency support and the exact producer publication.
Both kinds of carrier have distinct combined child refs. These results use the existing
publication support and failure cuts; group-notice eligibility remains separate.
`StartupNoticeTracking` retains historical announcements using concrete cancellation
markers before notification dispatch. Each value/notice projection uses the actual
source-ledger cut, with identical raw positions and prefix counts. `StartupNoticeCarrierCuts`, `StartupNoticeItemPublication` and
`StartupNoticeControlCuts` retain exact producer ranks, notices and earlier completions.
`StartupNoticeAncestorCoverage`, `StartupNoticeAncestorAccounting` and
`StartupLeadingNoticeAncestors` account for every defer-ancestor contributor on the shared
matching. `StartupNoticeAncestorHealth` excludes historical failure from that successful
ancestry. `StartupNoticeAncestorCompletion` closes previously announced ancestors at the
actual carrier cut and derives full dependency readiness, including silent accounting of
unannounced ancestors.
`StartupPublicationCuts` supplies actual FIFO producer readiness, permanent registration
and membership exclusion from the same source-handler ledger. `StartupNoticeContents`
retains nonempty unpublished memberships at the pruning boundary before cached cleanup.
The proof-only exclusion lemmas accept the ledger's initial queue because their argument
uses indexed matching independently of initialization. `StartupGroupNoticeAdmission`
combines those contents with producer publication, freshness and full dependency readiness.
`StartupFullAdmission.startup_admissionCertificates` constructs batching, licensed causal
and aggregate reporting, and full admission of every nonterminal value and control on one
actual startup witness. The terminal constructions below reuse its exact matching and cuts.
`InitialStartupRootCoverage` preserves complete root paths through synchronous failed
activation. `StartupContributorRootReplay` composes these paths through source-valid replay
and proves retirement of every registered contributor at termination, without a health
premise. `StartupFailureReportReplay` retains initial local report origins as emitted
reports or pending FIFO notices across actual batches. `StartupTerminalFailureReports`
preserves those
positive scopes through the real publisher and nonterminal projection. Observed reports
establish semantic group failure using the same licensed explanation, independently of
hidden cancellation state. Registered-task and attachment-report accounting use this bridge
without assuming the desired terminal law.
`StartupRegisteredTasks` interprets uncancelled retired contributors on the original
publication ledger and matching. At terminal replay, every registered object task is
published or causally cancelled: each cancelled owner has an observed report establishing
semantic failure under the same explanation. Every unpublished registered object's
attachment path is covered by such a positive report. This argument needs no extra
assumption identifying raw cached failures with causal cuts. The following producer and
stream certificates extend this accounting to latent work.
`StartupObjectPublicationAcceptance` reflects each published object to its actual accepted
cached source lookup. `StartupProducedTaskRegistration` preserves that callback's complete
object-child registration through later host batches. `StartupItemPublicationReflection`
uses exact source-item counts and shared matching to recover every published item identity
as a successful source input, independently of item-value equality.
`StartupAvailableObjectTasks` therefore registers, accounts for, and supplies covering
terminal reports for every root or published-producer object task. Structural producer
induction then covers latent tasks; concrete tracking separately closes announced nodes.
`StartupStreamCompletion` activates every initial stream notice and proves that all
announced streams actually close at termination. `StartupGroupCompletion` retains each
protected initial or carried group in live or queued support until its own observed
completion. Initial removals remain pending across empty calls and prefixes. Terminal
tracking uses the empty final FIFO before transporting actual completion output through
normalization and atomization. `StartupTerminalNodes` therefore proves closure of
every announced ref independently of abstract terminal accounting; complete task accounting
then supplies the unchanged unannounced-node alternative.
`StartupStreamOrigins` and `StartupBufferedStreamFrames` retain exact source provenance
and buffered child inventories through startup-aware host batches.
`StartupProducedStreamCoverage` exposes buffered object children at their actual release.
`StartupObjectProducedStreams` and `StartupItemProducedStreams` therefore establish complete
stream notices and terminal closure for every root or published-producer stream, including
empty streams and children whose producing outer stream later fails.
`StartupTerminalTasks` combines these closures with registered-object accounting and
structural producer-rank induction to account for every generated task.
`StartupTerminalReporting` uses the exact completed-stream source inventory and actual
positive object reports, then propagates their scopes down producer attachments. Every
unpublished task therefore has a covering observable completion on the same witness.
`StartupConformanceCertificates.startup_replayCertificates` assembles exact batching,
explanation, terminal tasks, node accounting and cancellation reporting on this one witness.
`StartupConformance` transfers these certificates through the actual factory's admitted
input language using ordinary replay from the initialized state, which already retains
the pending startup notices. Its marker-reflection proof identifies complete abstract runs exactly with
the actual final flag. `createWorkQueueForScheduleConformsWithStartup_holds` proves all
four public clauses for arbitrary source-valid startup observations.
`StartupPublicationCertificates` retains the actual initializer's source-handler closure
ledger on that same witness, together with exact fresh value occurrences, earlier item
publications and the producer of every carried stream notice. `ObjectLedgerMatching` and
the proof-only `BufferedClosureLedger` accept an initial queue, defaulting to the ordinary
initializer. Removing termination preserves the exact source ledger, occurrence matching
and failure cuts; it does not replace startup replay with ordinary initialization.
`StartupRetiredHealth` derives retirement and root-ancestor health for initial failed root
computations together with consumed source failures. Permanent registration and fixed
failed outcomes supply the evidence, independently of whether an initial observation was
started or notified. `StartupObjectStreamSupport` preserves the actual successful producer
and retired dependency through startup-aware batch/FIFO cuts. `StartupStreamSourceBoundaries`
retains each stream action's source label, strict source prefix, later object-reporting
cuts and count of earlier items. The shared block projection lemmas accept the initial
notice tail; the ordinary statements specialize them to an empty tail.
`StartupObjectStreamHealth` combines those source cuts with retirement health, accounting
for initial observations without inventing consumed callbacks. `StartupStreamProducerReadiness`
derives producer publication from each stream's strictly earlier notice.
`StartupSuccessfulItemSafety` applies publication-position induction to the same matching
and selected mixed failure cuts. The shared `StartupPublicationCertificates` witness
therefore also has `SuccessfulItemsSafe` and `StreamValuesReady` on the matching used
by object admission and carried-notice eligibility.
`StartupObjectFailureSafety` and `StartupFailureSafety` license selected initial and later
object causes and actual failed stream items against their exact mixed predecessors.
The structural owner-selection lemmas in `MixedFailureHealth` are shared with the ordinary
initializer. `StartupStreamCompletionAccounting` places all contributing item publications
strictly before successful stream closure. `StartupFailureCertificates` retains these
results on the same actual nonterminal witness, closing batching, announced reporting and
`UncancelledFailures` together with the publication certificates.

### Checked startup properties and batch-aware replay

[GroupStartup](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/GroupStartup.lean)
proves implementation-specific reporting properties independently of the general queue
contract:

- `State.startGroup_reportsAllCachedFailures`: when the looked-up group has cached
  rejections, startup returns exactly one notice containing their entire sum and the
  state produced by immediate group removal.
- `State.startGroup_failure_noNewTasks`: started-task identities after failed startup
  form a sublist of those present before startup, so no private task is started.

These theorems take an explicit availability snapshot and apply to the actual reference
transition. `NodeFailureCauses` deliberately remains broader: its supported-subset rule
alone does not establish the reference's exact startup count.

[BatchReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/BatchReplay.lean)
defines `State.replayBatches` and proves `State.runNormalized_replayBatches`: publisher
normalization preserves that batch-aware state replay. `State.replayBatches_append`
composes complete batch histories without discarding their boundaries.

[StartupFrames](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupFrames.lean)
proves that exposing cached failures changes only task-node outcomes. Starting a group or
released work retains a sublist of the previous group records. These frames preserve
initial pending counts and unique memberships without assuming that activation cannot
remove failed groups.
The [GroupRefs](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/GroupRefs.lean)
invariant also survives explicit cache availability and the separate startup notices
through initialization, task/stream handlers and complete host batches.

Host batches carry cache availability as well as notification order. The reporting
fixture checks identical flattened notifications with two partitions: one available batch
reports two errors for C; three successive batches report one. This is distinct from
response batching, which coalesces already produced updates. `ValidGraphEvents` may still
check flattened payload/dependency order, but state and reporting proofs must retain the
availability boundaries. Conditional eventwise lemmas retain their fixed-snapshot proof
language; they do not supply a flatten-only state equivalence for the public
batch-admission domain.

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
   occur before queue termination, and report only started tasks/streams. Each event must
   be eligible at some dispatch boundary at or before its FIFO consumption within the
   same batch. This includes tasks started by earlier events and retired before their
   callback is consumed. Each dispatch uses the complete batch's available-failure
   snapshot, including notifications which become stale during that batch.

`schedule.ValidFor work startup` retains these laws for an explicit initial
observation. Nonempty observations additionally name distinct, matching producer-free
failures, use startup-aware start/stop replay, and require every actually started listed
rejection in the first available notification batch. Outcomes still have one fresh
notification; availability is not consumption. These are host-input laws, not assumptions
of output admission or correct error reporting. With an empty observation this contract is
exactly `ValidFor`. The existing conformance witness covers that specialization.

`State.acceptsBatch` accumulates earlier eligibility in a batch-local predicate; it adds no
runtime event queue or persistent start ledger. Eligibility from an earlier batch alone
does not admit a callback that is stale throughout the current batch. This is a finite
source-adapter rule, not a normative spec algorithm or a native GraphQL.js API.
The `WorkSchedulerBufferedFailureSnapshot` regression checks that a complete buffered
batch is admitted and reports both cached causes for its released child. Erasing the
notification that later becomes stale changes the child's count from two to one, so
callback filtering cannot generally preserve output by rebuilding availability from the
filtered batch.

`InputReplay.eventsStarted` is a stricter, proof-only eventwise language used by
conditional lemmas; public batch admission does not imply it. Its append and prefix
lemmas remain separate from the public batch check, whose corresponding lemmas retain
initial eligibility. `PendingAccounting` proves matching-handler and fixed-snapshot replay
preservation even for stale callbacks. Both the all-outcomes and successful-settlement
pending ledgers therefore cover the widened public source domain without a current-node
premise. Guard-accepted failure contributions remain a sublist of supplied failure
notifications; batch admission no longer equates these occurrence lists.

Task catalogue equations, integration lookups and membership-absence lemmas live in
independent proof modules, without depending on healthy-owner replay or publication
inventories. `StartedTaskRetirement` uses these facts to track an already started
computation through all handlers, cached startup and the success-only ready drain.
Its computation remains represented or has no live membership. Source producer provenance
and freshness preserve this distinction through an arbitrary valid continuation, excluding
identity reuse by later child registration. The FIFO-prefix lemma derives the same
disposition for each initially eligible task. This is proof evidence over existing queue
records, not an additional runtime ledger or a host-supplied endpoint assertion.

`HealthyCounterReplay` carries producer provenance beside the existing counter metadata
and uses started-task retirement at each actual FIFO prefix. Its public-admission replay
preserves exact healthy counters even for stale successful callbacks. `FailureRetentionReplay`
uses the same derived disposition and permanent task descriptor to handle stale failures:
their contributors cannot remain live, while surviving failed contributors retain their
rejection. `OwnerReplay` combines this counter frame with matching registered-owner
preservation. These batch proofs retain the original initial eligibility and complete
rejection snapshot; none derives strict eventwise membership from batch admission.

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
def createWorkQueueForScheduleConforms (startup : InitialStartup := {}) : Prop :=
  ∀ work (schedule : EventSource (List GraphEvent)),
    ExecutedWork work
    → work.isEmpty = false
    → schedule.ValidFor work startup
    → (createWorkQueueForSchedule work schedule startup).Conforms work
```

`ExecutedWork` means work returned by pure root execution, including its fixed outcomes;
it is not merely a plan. Nonempty work is required because ordinary execution constructs
no queue, while incremental initialization requires a nonempty notice frontier.
[`createWorkQueueForScheduleConformsWithStartup_holds`](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/StartupConformance.lean)
is the arbitrary-startup witness. The
[`createWorkQueueForScheduleConforms_holds`](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/Conformance.lean)
module supplies its empty-startup specialization. Both follow declarations and internal
FIFO dispatch. Their obligations follow this four-clause structure; terminal
accounting includes an actual covering positive-error completion for every cancelled task:

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
including exhausted stream boundaries. Initial contributor membership uses the
execution-generated declaration and registration evidence.

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

The current source comparison is pinned to PR #4870 at
[`299a279`](https://github.com/graphql/graphql-js/tree/299a2792ccb325b04cc8a01adc3c9ee162393eea).
The [complete definition map](graphql-js-correspondence.md) links the pinned WorkQueue,
IncrementalPublisher, Computation and Queue sources and distinguishes native operations
from extracted helpers, finite-source adapters and proof propositions. The draft remains
authoritative.

| GraphQL.js construct | Lean counterpart |
| --- | --- |
| `Work`, `Task`, `Stream`, `Group` | Same record names; lowering adds structural occurrence identities and explicit parent metadata. |
| `GraphEvent`, `GroupFailureEvent`, `WorkQueueEvent` | `GraphEvent` includes all native dispatch variants. Internal failure payloads are queued by startup and forwarded at their observed FIFO positions. |
| `GroupNode`, `TaskNode`, root/node collections | Same node names with explicit finite-list `State` fields. |
| `createWorkQueue` | `State.initialize` is the initialization core; `createWorkQueueForSchedule` additionally lowers work and exposes normalized outputs. |
| Integration, pruning, activation, and event handlers | Corresponding `maybeIntegrateWork`, `addGroups`, `pruneEmptyGroups`, `startNewWork`, task/stream handlers, and removal functions. |
| Local `startGroup.errors`, `finishGroupFailure`, `pushGraphEvent`, `handleGraphEvents` | Immediate removal returns an enqueue effect, retained by `enqueueGroupFailures`. Dispatch consumes the stored notice only at its matching FIFO position. |
| Publisher `buildResponse` (initial envelope) | `ReferenceWorkQueue.initializeIncrementalResponse`, composed with the shared `Execution.initializeIncrementalResponse`. |
| Publisher `_toPendingResults` | `Execution.getPendingEntry` with `ensureID`, called by the shared initializer and subsequent mapper. |
| Publisher `_handleBatch`, `_getBestIdAndSubPath` | `IncrementalPublisher.handleBatch`, `getBestIdAndSubPath`; owner normalization precedes shared `Execution.mapWorkEventBatch`. |

Modeling adapters:

- `NodeRef` values stand in for defer/stream object references; structural occurrences
  identify tasks. Finite lists replace maps/sets.
- Pure finite outcomes validate supplied events; errors are counts, not error objects.
- `Work.fromExecution` lowers explicit ordered declarations separately from contributors,
  as native Work does. Raw fixtures also declare registration candidates explicitly;
  permanent registration avoids duplicate descriptors, and cancellation history
  distinguishes late failed parents.
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

GraphQL.js retains rejected computation outcomes while another owner survives. The
finite queue retains those causes on `TaskNode`. A newly received task failure closes
active owners only, without decrementing dormant pending counts or removing their task
memberships. Starting another owner inspects all retained rejections before private work.

For two shared tasks, the second can settle first while both belong to a latent group.
When the group starts after both reject, its completion includes both causes in task
registration order. The task errors remain distinct from collected nullable diagnostics:

```graphql
{
  ... @defer(label: "R1") { first: bad }
  ... @defer(label: "R2") { second: bad }
  ... @defer(label: "P") { slow ... @defer(label: "C") { first: bad second: bad } }
}
```

With non-null `bad`, settle `second`, then `first`, then `slow`. C reports `first` and
`second`. The count-only fixture uses distinct raw boundary counts to check their sum;
it does not introduce detailed error identities. A failure still pending at C's startup
is excluded from that completed notice.

Settled unpublished successful values are retained too. Starting their task again does not
integrate child work or decrement pending a second time. Empty-shell pruning uses task
membership, and removed task nodes absorb later callbacks.

[WorkSchedulerRetainedOutcomes](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedOutcomes.lean),
[WorkSchedulerRetainedAnnouncement](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedAnnouncement.lean),
and [WorkSchedulerRetainedErrorCounts](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedErrorCounts.lean)
prove release and cancellation regressions with cached aggregate reporting.
[DeliveryFailureReporting](../../Tests/GraphQL/IncrementalDelivery/Fixtures/DeliveryFailureReporting.lean)
checks both cached causes for a latent owner, pending-outcome exclusion, FIFO notification
order and independent sibling aggregates, preserving collected diagnostics in finite Work.

### Cancelled-parent registration

Registration requires a live parent, after recursively visiting that parent if it is a
candidate in the same chunk. Both failed and successfully retired missing parents refuse
new children. `cancelledGroups` distinguishes these cases for failure accounting: a refused
child inherits a failed parent's marker, while successful retirement introduces no failure
marker. The repaired GraphQL.js implementation rejects new groups under removed parents. Its
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
settlement cannot close dormant D. When Q releases D, startup collects its cached X and Y
causes into one completion, after D's normal announcement. The concrete admission fixtures
prove that both unit causes contribute to D's report and exclude a third cause. An earlier
causally redundant rejection can contribute to reporting without becoming another licensed
cancellation cut.

The repaired GraphQL.js audit covers direct queue replay and validated queries. Late C
registration is rejected, and a latent failed group is completed only after announcement.
Cancellation and scope coverage remain independent of the selected numeric explanation.

### Wire and finite-stream projections

Explicit null labels follow the draft spec, whereas the GraphQL.js implementation
omits them. Empty/exact-count stream boundaries have pending/completed lifecycles without
item patches; see [exhausted streams](README.md#exhausted-finite-stream-boundaries).
The model does not claim agreement on every JavaScript error, cancellation, or
interleaving.

Contributor coverage through successful task handling, item preparation and ready draining
quantifies over a fixed supplied rejection snapshot. The item induction retains cancellation
and cache provenance under the same available-failure inventory. Integration edge provenance
and the item-state fold retain that snapshot as well. Actual contributor-coverage replay
now carries coverage, parent links, retirement and ownership through each host batch
under its full available-failure inventory. The batch endpoint supplies the no-stranded
healthy-contributor consequence without an eventwise state correspondence. Publication
membership exclusion likewise follows a fixed snapshot through raw replay and accounts
for value-free forwarded startup notices at the batch wrapper. Healthy ancestor paths
use the actual batch failure inventory and its source-history equality under start
discipline.

First-report placement preserves every distinct available task cause in a group report
and its summed boundary count. Stream reports retain their single-cause witness. This
placement result concerns reporting availability; it does not supply causal cancellation
licensing. Healthy startup links use surviving group records rather than equality of
the pre-startup and post-startup group maps. Eventwise cached-failure support follows
successful drains through child startup and retains an explicit empty-snapshot replay
premise. Full-handler retirement carries started-task provenance, registered-task
matching and membership soundness through cached startup. The combined ownership/ancestry
bridge derives its actual batch endpoint from the independent ownership and structural
retirement proofs. The streamed taskless-parent regression instantiates that bridge.
Closing-only host batches retain initial-frontier health through a fixed cache snapshot
and accepted FIFO notifications. Their normalized result uses the actual batch failure
inventory, with terminal flags transported separately.

Defer-only causal owner health follows informative selection on actual unfiltered source
blocks. Its construction retains separate raw reporting cuts, so redundant causal
occurrences can still contribute to aggregate reports. This proof does not require a
historical missing-parent callback. The separate eventwise prefix-health helper requires
its own empty-snapshot acceptance check.

Buffered child-stream completeness survives rejection cache updates, failed group startup,
successful release and item preparation under one supplied snapshot. Stream registration
provenance uses that same snapshot to establish fresh child-stream refs throughout
eventwise replay. Actual normalized batches retain the same complete child-stream links
through a joint producer-history/completeness frame. The frame handles each batch with its
own snapshot and requires matching/fresh source validity, without a start or output
admission premise. Retained-rejection cancellation at normalized endpoints uses the
actual batch failure inventory and the proved ownership/ancestry bridge. The retained-error
regression constructs an admitted two-cause aggregate history and proves that a third
reporting error cannot be manufactured from collected diagnostics, settlement reordering
or value batching. Mixed object/stream and silent-settlement fixtures use separate causal
and reporting inventories; rejected-publication cancellation uses the actual batch ledger.
Successful draining preserves an already rejection-free active frontier; it does not consume
pending FIFO failures. Startup checks establish rejection freedom for new roots. A waiting
active cached-rejection regression checks this boundary explicitly. Fresh-work integration,
task success, and stream-item preparation preserve the clear frontier when retained
rejection evidence excludes the incoming child identities. Generated-parent and delayed
stream-publication fixtures exercise those local handler laws. Actual host batches separately
exclude every consumed failed contributor from live active groups. Startup, registration,
retention and successful-settlement counter bounds preserve this exclusion through each
FIFO step. Exact rejection provenance then establishes rejection-free active groups at
complete batch boundaries, including joined batches with early cache availability. For
unique task keys, cache exposure has an exact per-task rejection-slot projection and is
idempotent. Starting with supplied cache availability and eager empty-cache insertion
align after the same exposure; this does not assert equality before exposure or a general
alternative-queue batch projection. Task startup commutes with a common cache exposure;
the resulting state relation is preserved through arbitrary sequences of task starts.
First-match task lookups retain values and held streams under exposure, and task removal
commutes with it. The live-owner bookkeeping frame can be recovered from an exposed
queue with unique task keys and transferred between queues with equal exposures. Fresh
node insertion and task-record replacement also preserve the exposed-state relation,
retaining values and held-stream metadata.

`EmptyFailureBatchLedger` provides a singleton-batch closure projection with the supplied
rejection snapshot, and permits flattening only when every batch's rejection snapshot is
empty. Started host boundaries supply the running-state evidence for the latter proof.
The shared counter regression separates one selected causal cut from two distinct cached
reporting causes, whose counts sum to the child's reported error count. Conformance
fixtures retain both causal and reporting inventory obligations, use actual normalized
states for terminal accounting, and preserve empty queued-notice forwarding blocks.
`ExecutedTaskErrors.nodeFailureCauses_count_le` bounds a generated group's report by a
complete list of distinct contributing tasks. The cancellation and late-parent regressions
allow two cached unit causes while rejecting a count of three from collected diagnostics.
The failed-co-owner fixture derives failure of the wire owner from causal evidence,
independently of its separately witnessed reporting availability. Retained-stream regression
proofs use the final host batch's exact closure-ledger slice and actual batch replay for
terminal completion, preserving the earlier batches' failure snapshots.

## Verification and limits

Initialization, response initialization, and source validity use one optional startup
observation, defaulting to empty. Definitions, proofs, and regression tests use this shared
API. Lowering uses only explicit declarations. Execution-derived declaration certificates
cover every immediate task contributor and primary parent, including child integrations;
no inference mode or extra source premise is needed. Raw queue fixtures use a test-only
builder that writes their ancestor declarations explicitly. Shared structural lookup retains
the exact task-contributor and child-work projections for arbitrary work, including invalid
addresses and item indices. Public query and conformance definitions and proof-side
initial packaging use direct `Work.isEmpty` checks. `executeRootSelectionSet_fromWork`
is definitional equality; count-based accounting uses the emptiness/count bridge only
where needed. Total finite record counts remain proof-facing measures.

Successful execution plans uniformly annotate their task branches, including empty
declaration lists. `DeclarationCoverage.fromExecution_empty_declarations` proves that
an empty annotation preserves every lowered queue record and task address. Allocation,
ownership, response-coverage, and alternative-executor proofs use the uniform form.

Terminal node closure uses only announced known nodes. The stronger proof-only
`ConformancePlan.NodeAccounting` specializes the shared `NodesTerminal` proof view,
retaining latent accounting for the separate task-redundancy result.
`terminal_iff_tasks_and_nodes` proves exact equivalence with the
public contract for arbitrary raw work, retaining its full cancellation-reporting clause.

The full build, tests, formatting checks, and lint pass with these interfaces. An audit
of 25 conformance, query, resource, lookup, and simplification witnesses finds only the
standard Lean axioms. Differential fixtures against the pinned GraphQL.js implementation
match all 28 queue histories and 72 initial executions exactly. Mutation checks detect
pending-notice, aggregate-error, and unsafe callback-projection defects. These finite
checks supplement the proofs; they do not establish runtime refinement.

The reference's startup frames, registration, group provenance and counter bounds account
for immediate failure removal. `TaskNodeKeys` derives unique computation identities, and
`TaskRejections` attributes every retained rejection count to an exact supplied task-failure
input through actual normalized batches. Startup preserves permanent catalogues but can
remove live group, root and task records. `InputReplay`, `PendingReplay`, `CancellationReplay`,
`HealthyCounterReplay` and `FailureRetentionReplay` follow actual host batches. Their
within-batch proofs retain one availability snapshot while advancing the consumed FIFO
prefix. Available failures support cache and cancellation facts; consumed settlements
advance counters and rejection retention. A zero pending count licenses successful removal
using the successful-settlement ledger, which excludes failed occurrences. These proof
inventories add no runtime cache, scheduler premise or flattened state bridge.
`FailureProjection.objectFailureContributionsForBatches` follows live task lookups at
actual consumption cuts. Buffered callbacks admitted at batch entry can become stale
before consumption, so this guard projection need not equal the full supplied failure
inventory. `admittedObjectFailureContributionsForBatches` instead follows the source
admission guard, retaining eligibility from batch entry. Checked batches make this
explicitly named proof projection equal the supplied task-failure inventory.
`AcceptedFailureEquivalence` uses this admission inventory for actual batch ownership.
`ActiveRejectionReplay` combines the disposition-aware retention and counter frames to
exclude consumed failures from live active groups at batch boundaries. A retired failure
callback has no remaining owner memberships, so ignoring its notification preserves that
exclusion. `ClosingFailureHealth` preserves its full admitted-inventory statement using
retained failures, active-cache exclusion and the protected initial dependency frontier.
The buffered-failure regression distinguishes the two inventory projections, preserves
both cached startup causes, and applies the general active-cache theorem. Conditional
empty-snapshot eventwise corollaries retain their stricter per-consumption start check.

`OwnerReplayClosure.runNormalized_ownerAccounting_of_started` derives healthy registered
ownership through actual normalized batches without a contributor-availability callback.
`OwnerRelease`, `OwnerAccounting` and `OwnerReplay` supply its transition and composition
rules. The joint induction derives object-child availability from structural retirement
plus supported failures, and item-child availability from fresh stream regions. Permanent
task registration supplies object-child availability even for a buffered callback whose
last owner has retired. `StartedTaskDisposition` distinguishes surviving task nodes from
retired memberships at each FIFO cut; source eligibility may come from batch entry.
`StoredLinkReplay` needs only matching and freshness to retain buffered links, including
ignored callbacks. `ContributorCoverageReplay` carries the same disposition and permanent
registration evidence to healthy live-contributor coverage under buffered batch admission.
`AncestorCertificates`, `AncestorRelease`, `RetirementIntegration`,
`MissingParentRetirement`, `UncancelledRetirement` and `UncancelledRetirementReplay` supply
the retirement evidence; `RegionRegistration` and `StreamAvailability` supply region
separation. `OwnerAccountingInInventory` keeps available failures separate from consumed
settlements within a batch; boundary `OwnerAccounting` joins those coordinates again.
`RetirementHandlers` carries execution-derived declaration contexts through object and
stream registration, deriving parent coverage at every integration. `RetirementReplay`
retains the joint owner/ancestry certificate through queued dispatch and notice consumption.

`StoredValues` preserves exact occurrence/value provenance across snapshots and actual
normalized batches. `PublicationInventory` retains distinct, fresh occurrence labels for
immediate object output; `TaskRegistrationReplay` preserves permanent registrations.
`StreamPreparation` names the actual item fold including accumulated startup notices.
`PublicationReplay.rawEventReplay` retains immediate output, while `rawBatchReplay` also
accumulates startup failures. Their projection equality and batch-wrapper theorem expose
FIFO output followed by startup notices; those notices contribute no object values.
`GroupNoticeProjection` separates raw carrier projections and exact successful-release
frontiers from aggregate failure-notice accounting. `NoticeAncestorRetirement` uses that
independent foundation for carried-notice ancestry. `StreamPublication` proves exact,
occurrence-unique item sources and input order through actual batch handling and publisher
normalization. `BufferedStreamEligibility` derives current stream liveness from batch-entry
eligibility and the source readiness rule excluding earlier stream completion. This
argument permits stale task callbacks without assuming stale item callbacks are executable.
`StreamRootFrames` supplies the foundational root-preservation facts independently of
publication correspondence. Exact source-item proofs require `ValidGraphEvents` alongside
batch admission. `ReplayPublicationLedger` advances its pending ledger from matching and
freshness, so its actual batch coverage includes ignored task callbacks.
`ItemStreamReleaseReplay` and `NormalizedItemStreamRelease` use the same item-only liveness
condition and retain exact inclusive producer prefixes. `SourceItemPrefixes`,
`StreamSourceBoundaries` and `BatchedItemProducerPrefixes` also use source readiness to
retain exact item counts through source blocks and actual FIFO publication prefixes.
`StoredValueRetention` preserves an exact buffered task lookup through
startup when a contributing owner survives and the task's own rejection is absent from
the snapshot. `DrainValueCoverage` composes the same survivor condition through each
successful drain step, with one occurrence-labelled publication inventory and a fixed
availability snapshot. `MissingParentHealth` preserves healthy ancestry across startup
removal; ready flushing uses successful counter debt to exclude failed memberships. Last-owner
startup removal can discard buffered data; the
`WorkSchedulerValueStartup` regression checks both removal and co-owner retention.
`ChildStreamRelease` derives settled producer values for stored child-stream
links, and `ChildStreamProvenance` preserves their exact structural producers through cache
exposure and startup removal. `TaskProducerOrder` retains producer order under a fixed
availability snapshot, and `GroupMembershipOrder` preserves registration-order memberships through
actual
normalized batches; neither invariant adds a source or scheduler premise. `OutputShape`
derives nonempty normalized batches and value lists from source readiness, including
observed internal failure dispatch. `RawPublicationClosures` proves that every raw object
publication has its successful group closure immediately afterward, including batches
that dispatch queued startup-failure notices. `PublishedMemberships` and
`MembershipExclusionHandlers` retain shared-membership exclusion for the same publication
ledger through snapshot-aware draining, activation and task/item handlers.
`StreamReleaseAccounting` uses that occurrence-labelled inventory to place each released
stream producer before its successful carrier through those transitions. `StoredTaskLinks`
preserves memberships for buffered values, while `TaskLinkDisposition` keeps each permanent
registration completely linked or retired through snapshots and startup removal.
`DrainClosureBoundaries` recovers exact output prefixes at live, active, zero-pending
successful groups. Rejection freedom is not part of this structural boundary witness.
`BufferedOwnerConservation` accounts for startup removal by proving every original group
record survives or is marked cancelled; its exact buffered-record conservation theorem
uses an uncancelled contributor and excludes that task's own available rejection.
`StoredLinkPreservation` and `TaskLinkDispositionHandlers` transport buffered and complete
task links through matching handlers. The latter derives `GeneratedStartedTaskLinks_holds`
through actual host batches, using the same per-batch pending ledger.
`StoredClosureCoverage` and `TaskPublicationBoundary` connect those invariants to indexed
successful carriers and inactive-group publications under the same snapshot.
`MembershipExclusionPersistence` carries registered exclusions through source-valid replay
with a fixed snapshot. `PublicationContributors` proves that immediate raw publications
name contributing groups while cache exposure and startup removal retain contributor
provenance. `StoredLinkReplay` establishes buffered memberships through actual normalized
batches. `StreamReleaseReplay` transports one publication inventory through fixed-snapshot
handlers and actual internal-notice dispatch. Startup-failure and termination
controls add no object values or successful release carriers. `DrainPublicationLedger`
constructs one inventory for every drain prefix, buffered-carrier coverage, stream release,
registration order and membership removal. Carrier-specific retention uses the later
group's surviving record through startup; cancellation can discard buffers whose owners
all disappear. `DrainAncestorCoverage` uses prefix conservation and cancellation
monotonicity to place uncancelled buffered ancestor data before a child value block under
the same snapshot. `StreamActivation` and `StreamAnnouncements` prove that active stream refs
come only from initial or emitted notices through snapshot-aware handlers and actual
normalized batches. `StreamReferences` establishes strictly prior stream announcements
for every actual normalized stream value or closure. Startup-failure forwarding contributes
no stream notices or stream references. `GroupActivationSupport` locates
each startup-failure notice in its released group refs. `GroupSupportSettlement` and
`GroupSupportReplay` carry contributor-ref support through immediate output and separately
queued notices, including actual FIFO dispatch and publisher normalization.
`GroupFailureNotices` keeps separate proof evidence for live roots, immediate failed
closures and queued startup notices. Actual FIFO dispatch, publisher normalization and
atomic expansion preserve strictly prior group announcements without assuming output
admission; continued openness and causal licensing remain separate obligations.
`ReleasePublicationLedger` joins owner-fold and drain output with the same labels and
snapshot. It carries owner conservation and membership exclusion at every internal
boundary, and uses a later carrier's surviving group to justify retention through startup.
`StreamActions` retains source stream-action order through snapshots and FIFO dispatch;
`StreamRegistry` preserves supplied descriptors through cache exposure and startup removal.
`CancellationMonotonicity` proves that every earlier cancellation marker remains present
through actual normalized batch states. `StartedTaskAnnouncements` retains historical
contributor notices through cache updates, startup removal and successful drains; each new
task start is justified by sound membership in an announced released group. The witness
requires prior announcement, separately from continued openness. `TaskAnnouncementReplay`
composes those facts through snapshot-aware handlers, actual internal-notice dispatch and
the normalized runner. Its actual endpoint owner theorem derives structural contribution
and historical announcement from source matching, with no extra start or admission law.
`StreamActivationCoverage` activates all registered released streams, including through
snapshots and startup removal. `StreamCompletionSource` preserves the exact descriptor,
outcome and error count of each source stream completion through batching and atomization.
`StreamNoticeMetadata` retains structural provenance for all actual normalized and atomic
stream notices. Startup-failure forwarding adds neither stream completions nor notices.
`StreamRootCoverage` covers every immediate stream notice with an active stream root
through the same snapshot-aware startup and drain. `ItemStreamRelease` retains each
item-carried child stream's producer within that carrier's own item publication inventory.
`GroupClosureRecords` retains the registration descriptor of each immediate or queued group
completion through actual FIFO dispatch, normalization and atomic expansion. The queued
provenance is collected before startup removes its group. `GroupNoticeMetadata` preserves
contributor notice provenance through fixed snapshots and actual forwarding. Its nonempty
item-group contents witness belongs to the pruning boundary before activation: cached
startup failure may immediately remove that announced group. `GroupClosureAccounting`
accounts for immediate and queued completions together at each actual transition. A
proof-only permutation moves queued controls past later immediate output while preserving
their distinct closing refs and permanent retirement certificates. Normalized and atomic
closure uniqueness therefore cover observed internal failure dispatch.
`GroupClosureNotices` proves strictly prior announcements for both successful group
closures and forwarded startup failures, through fixed-snapshot handlers, actual batches,
normalization and atomization. Root membership is transported by inclusion through startup
removal; it is not treated as unchanged.
`ChildStreamInventory` preserves distinct registered links through cache exposure and
startup removal. `StreamItemRootCoverage` covers item-carried stream activation under the
same snapshot; `ItemStreamReleaseReplay` carries item-producer support through actual
FIFO replay and notice forwarding, with the exact source item inventory.
`ItemStreamNoticeFreshness` retains unique item-carried stream notices disjoint from the
entry registry throughout the snapshot-aware item fold.
`ChildStreamInventoryReplay` preserves the link inventory through actual handler and batch
states. `ImmediateStreamCoverage` proves that every fresh stream supplied by any item
appears in that carrier's notices, including with repeated raw descriptors.
`StartupRootCoverage` proves that subtree removal during activation preserves an active
covering root for each surviving target. `GroupClosureCoverage` measures survival after
activation and first proves released-frontier coverage before startup; `DrainRootCoverage`
composes those facts through the actual successful drain and its fixed rejection snapshot.
`PromotionPaths` retains edge and root ancestry through that same snapshot;
`OwnerFoldCoverage` carries delayed frontier coverage through actual startup and draining
without inserting activation into the single-pass task-owner fold.
`GroupNoticeTracking` accounts for every announced group as active, completed or recorded
as cancelled through the actual snapshot-aware handlers and FIFO dispatch. Item
preparation retains each old or noticed ref in the union of active and cancelled refs;
it no longer asserts that startup leaves every noticed ref active.
`ParentLinkUpdates` preserves canonical edges between surviving startup records by
inclusion. `BufferedStreamRelease` conserves buffered child streams through successful
drains and startup removal when the supplied rejection snapshot excludes their successful
producer occurrences; cancelled owners remain explicitly excluded from conservation.
`IntegrationPathCoverage` preserves earlier paths through registration and pruning, then
uses the derived integration forest to preserve root coverage for targets surviving actual
item startup. Unconditional path retention through failure removal is no longer asserted.
`BufferedStreamHandlers` extends the same stream-conservation certificate from newly
prepared successful values and earlier source buffers through owner folding, activation
and draining, with snapshot exclusion of those successful producer occurrences.
`ParentLinkHandlers` threads the same canonical parent-link completeness through cache
exposure, matched child integration, startup removal and actual settlement handlers.
`InitialRootCoverage` derives the integrated finite forest and transfers the pruned
frontier's paths through actual startup before projecting the initial metadata fields.
`ParentLinkReplay` preserves complete canonical links through actual batch snapshots and
normalized replay. `GroupNoticeFreshness` excludes prior and same-carrier group closures
from notices through snapshot-aware handlers and FIFO dispatch; concrete retirement
accounts for startup removal before its notification is forwarded.
`DrainClosureBoundaries` also certifies that cancellation recorded immediately after an
indexed success's child activation remains recorded at the full drain endpoint.
`ActiveRootPresence` uses that stronger certificate to retain live-root metadata and prove
ancestor completion at each actual notice carrier under the fixed snapshot.
`BufferedStreamItemHandlers` composes empty-publication owner-conservation certificates
through actual item preparation, startup and draining. Its dispatcher preserves exact
successful buffers through cache exposure when their occurrences are excluded from the
rejection snapshot; no unconditional lookup-survival premise is introduced.
`FreshRegionCoverage` transfers healthy fresh item-region paths through actual startup
under the supplied snapshot, using the derived integration forest and endpoint survival.
`RootPresenceReplay` projects the startup state component in its existing default-snapshot
replay witness. This eventwise helper does not itself establish an arbitrary-batch bridge.
`LiveRootReplay` separately derives the full live-root and retirement frame through
arbitrary fixed-snapshot handlers and actual normalized batches. Generated matching and
concrete initialization suffice; accepted starts and output admission are unnecessary.
`CancelledGroupReporting` proves cancellation-report provenance through actual startup
and successful draining using both immediate and queued completion inventories.
Task-local rejection positivity supplies aggregate positivity. Permuting the local queued
controls past later immediate output preserves each report membership; no runtime pending
report ledger is introduced. `SuccessfulGroupReporting` carries the same two-channel
completion inventory through complete task-success and stream-item handlers, including
late refused registration and child activation. `FailureReportReplay` composes all
fixed-snapshot FIFO handlers and retains positive reports or pending startup notices
for every cancellation marker. Complete reporting additionally requires an empty pending
FIFO; it no longer identifies flatten-only replay with batch state.
Source matching supplies positivity for every available task-failure count.
`CancellationReportNormalization` carries those exact positive completion origins through
the actual normalized batch fold. Atomic expansion and terminal-only filtering retain
every report. This uses generated matching and concrete queue invariants, without source
start discipline, output admission or a flattened execution-state bridge.

`TaskOwnerExistence` preserves a live contributing owner for every retained computation
through cache exposure and snapshot-aware startup. Healthy startup starts tasks against
the requesting live group; failed startup removes unsupported tasks. The same owner and
membership frame survives successful release draining without a rejection-free premise.
`TaskOwnerHandlers` now composes that frame with live roots and structural retirement
through actual fixed-snapshot handlers and normalized batches. Generated matching alone
suffices for owner replay; pending accounting, flattened acceptance and start discipline
are unnecessary for this structural fact. Existing proof wrappers retain their callers
while deriving the stronger matching-only result.
`BufferedOwnerExistence` also preserves buffered-owner existence directly through cache
exposure, failed startup removal and snapshot-aware item preparation. This weaker fact
requires neither owner health nor a rejection-free startup.

`TerminationFrames` keeps registration, cache exposure and startup termination facts
independent of publication-ledger proofs. Immediate failed-group removal preserves the
flag, and actual initialization leaves it false until batch handling decides termination.

Item-preparation certificates now accept arbitrary prior queues and fixed rejection
snapshots. `FreshGroupPaths` preserves live roots through registered item integration;
`GroupNoticeMetadata` supplies the prepared notice frame, and
`UncancelledRetirementReplay` supplies structural retirement at the actual drain entry.
These local results need matched generated work and concrete internal invariants, without
a flattened replay or new source assumption.

`RootClosureFrames` isolates protected failure cleanup and exact notice-completion
tracking from the recursive drain. Supported failed-group removal cannot silently remove
a different announced root; the support may come from a populated startup group rather
than prior activation. Snapshot exposure preserves that structural certificate, and
permuting retained controls preserves completion membership.
`StartupRootCompletion` tracks protected newly announced roots through immediate removal
and their queued controls. `ProtectedRootCompletion` composes successful release with
that startup result and every actual drain prefix. Immediate and queued controls are
permuted only for membership accounting; both retain their concrete transition origins.
`NoticeAncestorCompletion` uses retained-or-cancelled root tracking through snapshot-aware
preparation. The leading-item helper excludes cancellation at preparation exit; callers
must transport that fact backward from their actual handler endpoint. It no longer
assumes item startup leaves every prior root active or preserves cancellation by equality.
`NoticeCompletionHandlers` projects the state and immediate-output channels at its
existing eventwise task and item drain carriers, keeping queued startup controls separate.

`RetiredHealthStability` certifies its existing eventwise replay with an explicitly empty
availability snapshot. The obsolete normalized wrapper that treated flattened acceptance
as actual batch acceptance is removed. Health stability across actual batch boundaries
still needs its own availability-aware argument; the eventwise helper adds no host-source
assumption and does not discharge that obligation.
At a fixed failure inventory, `RetiredRecordHealth` now preserves uncancelled-retirement
health through cache exposure and actual startup folds. Failed startup creates cancelled
retirements, so every uncancelled retirement inherits its prior health evidence.

`CancellationRetirement` derives permanent retirement for every cancellation marker
through registration, cache exposure, subtree removal and startup. Live-group registry
coverage justifies refs collected by removal. Consequently a cancelled ref cannot name a
live group record. `CancellationRetirementReplay` extends the invariant through matching
handlers, item preparation and actual normalized batches. Its exact drain-carrier theorem
excludes every ref retired before that drain, including earlier cancellations. Source
matching suffices; no accepted-start premise, source law or runtime ledger is introduced.

`ItemPreparationLedger` retains publication inventory, registry, stream-release metadata
and cancellation-aware owner conservation through actual item startup.
`BufferedPreparationCoverage` transfers prepared closure/value certificates only for
contributors that can carry a later success or survive at the endpoint. Permanent
retirement and the task registry justify the corresponding earlier owner presence. These
helpers replace unconditional old-buffer retention. `StreamHandlerPublicationLedger` now
uses them for complete snapshot-aware stream-item coverage, endpoint value conservation,
stream release and every bounded drain-owner/membership prefix.
`TaskHandlerPublicationLedger` similarly preserves the single ledger across prepared task
values, owner processing and snapshot-aware drains. `HandlerPublicationLedger` now
performs actual cache exposure before constructing the matching handler ledger. Its
prepared-state predicates name that same cached queue; source provenance excludes
buffered successes from the rejection snapshot when transferring old-value certificates.
These handler results lift through actual source blocks and aggregate failure accounting
in the constructed conformance witness.
`ReleaseAncestorCoverage` now orders buffered ancestor values at exact snapshot-aware
owner/drain carriers using the same prefix ledger. Its generated eventwise wrapper
retains the default empty snapshot; actual batch lifting remains separate.
`ReplayPublicationLedger` carries one fixed rejection snapshot through each actual host
batch. Its prepared-state certificates start after cache exposure, and its publication
slices count only immediate object values; queued startup failures and termination
controls consume no labels. `BatchPublicationCleanliness` derives the required separation
of successful object outcomes from available rejections from existing source validity.
The ledger retains cancellation-retirement evidence through each handler and uses the
actual batch fold rather than a flattened replay with an empty snapshot.
`ReplayValueConservation`, `ReplayOwnerConservation` and `BufferedCarrierReplay` retain
that same snapshot through prefix slicing, owner retirement and later successful
carriers. Newly settled values use the actual prepared map after cache exposure.
`RetiredHealthClosure` uses zero pending debt in a successful-settlement inventory to
exclude failed tasks from ready closure; startup removal preserves the resulting
uncancelled retirement and root-ancestry health at the fixed failure inventory.
`RetiredHealthFrame` carries the same fixed-inventory health through snapshot-aware
startup and every bounded successful drain, deriving each emitted carrier's health from
its exact zero-pending closure cut and the independent successful-settlement bound.
`PreparedCarrierReplay` and `NoticeRegistrationReplay` use the same cache-exposed
preparation and actual immediate output when locating values and newly announced refs.
`FlattenedClosureLedger` retains snapshot-aware ledger slicing and batch object-value
erasure; its former empty-snapshot flattening theorem has been removed because batch
cache availability can change startup state before FIFO failure notifications.
`BatchOutputReplay.rawBatches` projects the actual batch state fold together with its raw
outputs. `RawValueLedger` preserves contributor-bearing values through that projection,
and `ReplayBlockOrder` composes their existing ledger slices against the actual final
registry. These proofs retain each batch snapshot and queued notice forwarding; they do
not identify their state or value order with an empty-snapshot flattened source replay.
`NormalizedClosureLedger` threads cancellation-retirement evidence through actual
batches and preserves the joint object ledger during publisher normalization.
`ObjectLedgerMatching` relates that ledger to actual raw batch output, and
`StreamProducerMatching` uses the same labels for producer support, item order and
handler-local closure coverage. Source validity and accepted starts supply the state
invariants; output admission is not assumed.

`GroupStartup` labels the existing local error collection with proof-only task occurrences.
It proves that startup notices, including those accumulated by `startNewWork`, satisfy
`NodeFailureCauses`: a nonempty list of distinct supported member-task counts sums to the
reported total. Independent positivity lemmas show that each startup notice has a
positive aggregate when cached and available task-local counts are positive; they need no
owner-membership or distinctness premise. These labels add no runtime group cause cache.
Complete handlers and observed FIFO dispatch preserve this accounting in the reporting
inventory, separately from licensed causal cuts.

The complete reference proof target covers aggregate failure-notice accounting,
concrete queue conformance, retirement invariants and the actual-factory query bridge.
The public correctness statements retain their premises and use separate causal and
reporting inventories on the same observed history.

The successful drain's normal form states that remaining active groups have nonzero
pending counts. It does not assert rejection-free active groups: an already available
rejection can await its FIFO notification on an active pending group. Startup of a newly
released group instead removes it immediately and returns a separate aggregate notice.
The drain regression checks both transition boundaries, including stale root entries.

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

`SelectedFailureCuts` identifies informative causal cuts whose contributors remain
uninvalidated by preceding selected cuts. This proof inventory can continue licensing
cancellation, while redundant available rejections belong to the separate reporting
inventory. `FailureReportingWitness` requires freshness, reachability, ordering, bounds
and prior contributor announcement for that inventory. Reporting causes use distinct
retained tasks and their selected boundary counts.

`StartupFailureSources` proves that group startup and recursive ready draining return
aggregates of distinct exact contributing task rejections from the supplied source.
`GroupFailureSources` records the proof-only occurrence list and its summed count;
`GroupFailureSourceCause` remains the single-task relation for task-local cache facts.
The runtime group and queued notice acquire no cause cache. `HandlerFailureSources` carries that provenance through prepared task values, owner
settlement, streamed child registration, cache exposure and both output channels of the
actual handler. Immediate failures have singleton inventories; startup notices preserve
aggregate causes. `BatchFailureSources` follows the actual FIFO batch fold, forwards startup notices in
order and preserves their counts through normalization. `GroupFailureSource` supplies
distinct source-backed, reachable, unpublished task causes whose counts sum to each
actual atomic group report. Reporting-cut placement, licensing and admission remain
separate pending obligations.
`FailureTotals` converts the aggregate source inventory into positive
`NodeFailureCauses` evidence over available source failures; the task-local singleton
lemma remains separate. `BufferedStreamReplay` retains its eventwise empty-snapshot
scope and now states acceptance in that same domain, without using full-batch acceptance
as a flattened replay premise. Actual-batch stream conservation remains a separate bridge.
`SourceOutputBlocks` traces immediate FIFO handlers with their full batch snapshot,
then records deferred startup notices in an unlabeled control block before termination.
Its multi-batch annotation agrees with the actual queue state, publisher state and exact
atomic output. Control blocks introduce no source settlement or causal failure label.
`FailureAncestorHealth` preserves ancestry for immediate task-failure notices at their
active-owner cut. Its immediate-drain statement is vacuous because the ready drain emits
only successful closures and values; ancestry of separately queued startup failures needs
its own release-time argument.
`TerminationShape` preserves the termination flag through cache exposure, successful
owner release, item integration and recursive ready draining at the actual snapshot.
Immediate handler output contains no terminal marker; startup notices remain a separate
channel and the batch wrapper alone emits termination.
`SourceItemPrefixes` retains exact item-label counts across immediate source blocks and
object-free deferred control blocks. `FlattenedOutputReplay` now equates normalization
with actual `rawBatches` output, including startup forwarding and terminal controls;
it no longer equates actual batches with empty-snapshot flattened input replay.
`SuccessfulCarrierOrigins` retains a successful carrier's actual preceding batch list,
selected batch, FIFO input prefix and full batch snapshot. Its source provenance does
not require accepted starts. `BatchClosuresCovered.atBatch` recovers that actual batch's
consecutive slice of the existing publication ledger and its snapshot-aware handler
certificates, keeping queue state and label offsets aligned.
`GroupFailureBlocks` proves aggregate source totals at each actual annotated report
boundary. Immediate handler reports use the current FIFO input. A deferred startup
report's unlabeled forwarding block follows all labels in its batch, so every collected
source cause belongs to that block's retained prefix. Rejection provenance is advanced
through the same batch transitions; no cache availability is identified with earlier
notification consumption.
`SuccessfulHealthFold` retains the successful-settlement pending bound alongside health,
release ancestry and output evidence. `SuccessfulTaskHealth` threads that bound and the
same snapshot through startup and ready draining, preserving fixed-inventory health for
the actual task-success state and its immediate carriers.
`TerminalRoots` projects empty terminal root lists through actual batch replay and
composes notice tracking with monotone cancellation markers on `rawBatches`. Announced
refs at termination are completed or concretely cancelled; eliminating silent
cancellation remains a separate generated-work completion obligation.
`StreamCompletionReplay` now preserves stream notice completion through fixed-snapshot
handlers, actual FIFO dispatch and `rawBatches`. At termination, actual empty stream
roots force a concrete stream completion for every initial or carried notice; no flattened
source-state bridge or generated-work assumption is used for stream tracking.
`TaskGroupCompletion` derives exact announced-group completion for an arbitrary
structurally valid task-success handler at its actual snapshot. Successful owner closures
use immediate output; failed startup children use queued completion notices. Permuting
those controls past later immediate drain output preserves a proof-side inventory;
actual replay retains their observed FIFO positions. `ItemGroupCompletion` proves the
corresponding stream-item preparation and handler
result, including empty-wrapper pruning, sequential startup failures and ready draining.
`GroupCompletionReplay` composes both channels through fixed-snapshot FIFO handlers,
tracks startup notices in the pending FIFO and preserves completion through actual
raw batches. Its generated-work bridge derives the initial root frame independently;
empty terminal roots and an empty pending FIFO force completion without an output
admission or accepted-start premise for tracking.
`ObjectFailureCuts` now transports each report's full distinct cause inventory to the
visible source-candidate cuts at its actual block boundary. Generated positivity gives
`NodeFailureCauses` for that inventory. Candidate visibility remains separate from
selecting and licensing causal cancellation or constructing reporting witnesses.
`CompleteFailureCuts` derives positive aggregate totals from those actual source blocks;
`CompleteMixedFailureCuts` retains the same distinct causes after adding stream cuts.
Reporting uses unfiltered source availability. Presence-selected causal cuts cannot
replace that inventory when startup reports several cached rejections.
`FailureInventory` merges unfiltered object availability with stream cuts and proves an
ordered, distinct reporting inventory with exact aggregate group totals. Its provenance
and successful-publication exclusion are derived without assuming causal licensing.
`CausalFailureInventory` separately records selected group invalidation and stream causes;
its prior-announcement and cancellation checks license causal cuts. A complete reporting
inventory instead supplies `FailureReportingWitness` from prior announcements and
freshness, including tasks already covered by cancellation.
`FailureAnnouncementCuts` derives prior contributing announcements at every actual
source reporting cut. Its block inversion includes silent inputs, cache snapshots and
preceding batches; normalization and atomization retain the same notice prefix. A buffered
failure whose task has retired uses its batch-entry contributor announcement; a task
started within the batch uses the announcement at its actual FIFO cut. This establishes
prior announcement without imposing current task membership on source admission.
`CacheEligibility.handleGraphEvent_accepts_of_emitted` derives current eligibility when
an immediate output actually exists, since stale callbacks emit nothing. Batched carrier
and ancestor-coverage proofs use this output guard rather than strengthening source
admission. `StreamActions.acceptsBatch_streamAction_live` instead obtains current stream
liveness from item readiness or fresh completion identities. Stream-action safety uses
that source-order result; informative object-failure licensing uses permanent task
registration from the actual source frame, including stale failure notifications. Merging
those object cuts with supported stream cuts constructs an actual reporting witness and
aggregate totals without assuming output admission or causal cancellation licensing.
`RetiredHealthHandlers` threads snapshot-aware task and item preparation through the
fixed-inventory health frame. Stream release and notice-ancestry helpers now require the
independent successful-settlement bound and disjointness needed by zero-pending closure;
their callers must derive these from source accounting. Immediate failed-closure ancestry
remains separate from queued startup reports.
`RetiredHealthReplay` derives the corresponding ancestry and missing-parent facts for
eventwise replay without an additional cache snapshot. Successful-settlement accounting
supplies the independent bound, and accepted eventwise failures identify the retained
source inventory. Actual batch health still requires its own snapshot-aware induction;
the eventwise result does not supply a flattened batch-state bridge.
`SourceHandlerBoundaries` composes handler annotations under one fixed snapshot and
locates each actual atomic output in its original host batch and local output position.
That batch may include unlabeled startup reports as well as immediate handlers and a
terminal marker; no theorem identifies all of these with flattened source handlers.
Its snapshot-aware immediate-output inversion also retains the exact earlier atomic
prefix and intermediate publisher for a selected handler atom.
Block-cut inversion also retains silent source handlers and their complete earlier
annotation prefix. `TaskAnnouncementReplay` supplies an owner announced before a
within-batch task lookup, starting from the actual preceding normalized batches and
threading the current batch snapshot through the FIFO prefix.
Source-failure cut inversion retains the exact rejected occurrence, boundary count and
labeled block even when no atom is emitted. Labeled batch prefixes exclude the unlabeled
forwarding and terminal suffix, retaining the immediate handler annotations exactly.
`StreamSourceBoundaries` recovers each stream atom's own source label through those
actual blocks. Deferred startup controls have no stream action. Its earlier item bound
and visible object inventory use retained source availability; they do not identify a
flattened pre-handler queue or supply causal failure licensing.
`FailureAncestorReplay` and `NoticeAncestorHealthReplay` derive immediate-output ancestry
for ordinary outcomes at those same eventwise cuts, using retained source failures and the
successful counter bound. Queued startup reporting is outside those immediate-output
certificates. `FiniteGraphEvents` includes observed group-failure controls in its finite
completion-token bound. The `SuccessCounterReplay` fixture supplies explicit notice dispatch,
checks the aggregate count and validates the actual availability-based causal inventory
separately from its source-only selection example.
Producer-publication ordering transports the exact cancellation projection through notice
enqueueing. Defer-only guard health uses the same availability inventory as causal selection.
`MembershipExclusionReplay` preserves publication inventories and removed memberships
through actual dispatch. `StartupRawBatches` uses ordinary raw replay from the initialized
queue and derives its exact normalized atoms and contributor provenance; the separate
seeded-tail runner is removed.
Stream-item projection and stream-notice metadata share generic ordinary-runner proofs in
`StreamPublication` and `StreamNoticeMetadata`. Startup modules specialize those proofs
to the retained initial queue, preserving exact item order and descriptor provenance.
`InitialStartupPublicationLedger` uses that ordinary replay ledger directly.
`StartupCarrierOutputCuts` maps each normalized carrier to its actual raw position with
exact equality of preceding object counts, using the shared normalization projection.
Startup diagnostic totals retain the initial reporting observations as evidence while
threading queued-report provenance through ordinary dispatch. Root exposure transports
structural locations across declaration wrappers; cancellation and owner accounting derive
the required registration context from executed work.
Startup stream announcement, source-order and source-boundary proofs now specialize
the ordinary normalized runner. Explicit control dispatch retains its actual source label;
it introduces no stream action or item and requires no separate startup accumulator.
Failure announcement cuts use the ordinary source-block trace. Normalized cancellation
reporting retains emitted-or-pending explanations for prefixes; completed replay derives
an empty pending FIFO before claiming every explanation appears in actual output.
Startup group closures retain queued registration descriptors and use the common
active-or-pending notice support invariant. Ordinary dispatch preserves exact group
metadata and stream release dependencies without a seeded-output membership projection.
Startup closure uniqueness derives the initializer’s distinct, retired pending notices
and reuses ordinary notification accounting. Publisher-registry correspondence likewise
uses actual raw replay, permanent retirement and the shared pending-notice invariant.
Startup cancellation reporting follows the same emitted-or-pending inventory across
host batches. The terminal bridge consumes the empty-FIFO consequence of termination
before projecting positive reports into the actual nonterminal atom history.
The finite nonblocking source bridge identifies its admitted history with the exact
initialized runner output before composing the output-prefix extension.
`NormalizedItemStreamRelease` supplies item-carried producer support for any initialized
queue with accepted batches. Ordinary and startup replay share this proof; source stream
completion accounting uses their common payload-preserving projection.
The eventwise cancellation contribution helper follows actual dispatch endpoints.
Informative owner-health cuts use available rejection evidence, and queued group controls
are excluded from object-producing handler cases.
Startup source frames retain an earlier eligible dispatch boundary and the actual
post-dispatch queue. Initial owner accounting, stream producer provenance and permanent
group-notice registration follow the same ordinary replay and declaration contexts.
Startup contributor coverage, successful retirement and group-notice metadata use
ordinary FIFO state and output projections. Buffered owner and object-stream frames
retain eligibility accumulated at earlier dispatch boundaries in the same host batch.
Structural descriptor regressions unfold declaration-transparent navigation explicitly.
The generated shared/private failure-scope fixture retains ordered declarations and
supplies the queued broad-group report as an observed control before termination.
Startup object reporting combines callback cuts with causes exposed by actual aggregate
reports, retaining each occurrence at its first available cut. Initial reporting observations
license provenance separately from consumed source labels. The reporting witness derives
reachability and prior contributor notices at those unchanged cuts and preserves exact
aggregate counts; no runtime cause cache or source-admission premise is added.
The shared startup conformance witness combines those reporting cuts with separately
selected causal cuts and actual stream failures. Removing the optional terminal marker
preserves every cut’s index, descriptor, announcement and reporting availability.
Startup object-produced stream health uses retained initial observations and the whole
source inventory, including causes exposed before their callbacks. Uncancelled retirement
persists through the remaining run, whose registered-failure certificate excludes invalidation.
Buffered stream frames and item notice provenance retain declaration-aware registration.
Produced-stream conservation crosses enqueueing through its buffer projections.
Startup publication certificates interpret the ordinary normalized history and its
nonterminal prefixes with the same object and item occurrence ledgers.
Startup object causal safety obtains root failures from initial observations and later
failures from permanent registration in the retained source replay. Informative owner
selection excludes prior cancellation at the original causal cut even when reporting
availability preceded the callback.
The common startup failure witness licenses both object and item causes over that
retained inventory. Stream admission, producer readiness, successful-item safety and
publication matching specialize the ordinary runner at the same nonterminal prefixes.
Startup group health uses that retained failure provenance. Group carriers and notice
ancestor accounting map unchanged normalized prefixes to the actual raw object ledger.
Startup publication provenance, ownership and fresh notice proofs use the same actual
raw batches and normalized carrier positions. Callback availability is recovered at an
earlier accepted dispatch boundary; terminal registered-task reporting consumes the
actual termination premise. Identity-only bridges to a separate startup ledger are removed.
Object and item producer order now use those raw carrier positions directly. Permanent
child registration follows actual dispatch, and the startup stream announcement inventory
transports only initialization metadata before ordinary batch replay.
`ExposedGroupCausality` and `ObjectStreamSafety` use the same eventwise start predicate
for retired-group and object-produced stream health; they do not infer that predicate
from actual host batch acceptance.
`StreamNoticeRegistry` retains old and newly announced stream refs through cache exposure,
five-component item preparation, successful ready draining and fixed-snapshot handler
replay. Registry preservation does not depend on source matching or generated work;
queued startup failures carry no stream notices.
`StreamAnnouncementRelease` preserves the consumable notice inventory through cache
exposure and both startup outcomes. Ready draining consumes each successful producer's
stored stream links before later activation; queued group failures add no stream refs.
`StreamAnnouncementHandlers` composes that inventory through successful task owners,
five-component item preparation and cache-exposing dispatch. Each immediate carrier
consumes fresh links; separate queued group reports do not alter stream freshness.
`StreamAnnouncementReplay` retains that inventory through actual host batches and
normalization. Forwarded startup reports and terminal markers carry no stream notices,
so initial and later stream announcements remain globally distinct.

`SelectedGroupFailureInventory` preserves causal group invalidation under selection of
unfiltered source candidates. It does not require healthy ancestry or retain every
aggregate reporting cause; reporting totals use their separate availability inventory.
`InformativeFailureInventory` derives an ordered, distinct causal inventory from the
same source candidates and supported stream cuts. It retains prior announcements and
group invalidation without requiring selected causes to reproduce aggregate reports.
`ConformancePlan.Witness` carries both causal cuts and reporting cuts. Its availability
obligation proves the reporting witness and the at-or-before link for each causal
occurrence; control admission reads those same reporting cuts. The checked explanation
and source-adapter edges now retain that joint witness.
`ConformanceBatchShape` retains immediate output and forwarded startup reports before
the unique optional terminal marker. `FailureLicensing` uses causal inventory metadata
for its cut-safety reduction; aggregate reporting totals are not causal premises.
`ConformanceFailureHistory` constructs both inventories on the canonical nonterminal
history using the same actual stream cuts. Causal object selection is a subinventory of
source reporting availability, so every causal occurrence is reportable at its original
cut. Removing the optional final marker preserves all cuts, prior announcements,
reporting freshness and the at-or-before link.
`MembershipExclusionWitness` clears the original publication ledger through cached
handlers, actual batch endpoints and later registration. Its canonical witness covers
every FIFO cut using the preceding raw batch outputs, the selected batch snapshot and
its consecutive ledger slice. It preserves earlier exclusions without flattening queue
state or choosing a replacement publication matching.
`MembershipExclusionBoundaries` retains owner-fold and drain-prefix exclusion for its
explicit empty-snapshot replay language. Its offsets read immediate output; queued
startup notices supply no object publication. `AtomicBatching` derives singleton values
from each explanation's chosen reporting witness.
`ItemNoticeContents` locates a leading child notice at its actual pruning boundary,
before cached startup can remove that child. The common ledger excludes prior object
publications at that boundary.
`ContributorStreamCoverage` carries supported caches, started-task provenance and sound
membership through item preparation, so startup cancellation retains its failure
provenance. Structural coverage uses the actual integrated removal forest and surviving
contributor, without assuming activation leaves cancellation history unchanged.
`DrainPublicationLedger` constructs one publication ledger with exclusion both after each
iteration and after its flush before cached child startup. Its established prefix interface
is a projection of this stronger result; the startup certificate uses the same labels.
`ReleaseMembershipsCleared` and `StreamDrainMembershipsCleared` carry that certificate
through the joint task and item-handler ledgers. Owner-fold prefixes are prepended using
their existing membership exclusions, retaining the original publication matching.
`DrainClosureBoundaries` also retains the exact selected ready record at each successful
carrier. The eventwise membership-boundary wrappers combine older handler labels,
owner-fold output and this same local startup certificate into full-history exclusion.
`DrainNoticeContents` recovers the selected pre-flush queue and its exact successful output
prefix. Child contents and full-history exclusion are witnessed after pruning and before
startup; a failed child need not survive startup to justify its earlier notice.
`OwnerReplayClosure.ownerAccounting_atBatchPrefix` supplies ownership, structural
retirement and region provenance at actual FIFO cuts. It replays preceding batches with
their own snapshots, while the current batch's full failure inventory remains separate
from its consumed source prefix.
`NoticeAncestorDrainPublication` reconstructs the exact post-carrier iteration from its
selected flush. Prefix owner conservation and ancestor retirement place buffered values
before the notice; this argument needs no child-content or group-ref support premise.
`StreamReleaseOwners` follows successful ready draining under its supplied cache
snapshot. Every released stream retains the flushing group as a defer dependency;
separate queued startup failures introduce no stream carrier.
`StreamReleaseOwnerReplay` carries this dependency evidence through immediate cached
handlers, forwarding queued notices and actual normalized batches.
`MixedFailureHealth` derives direct-safe owners from the causal selection of raw source
blocks and supported stream cuts. It does not equate that selection with aggregate
reporting totals. `StreamReleaseHealth` retains its explicit empty-snapshot replay
premise; actual batched health requires a separate bridge.
`TaskOwnerHandlers.replayGraphEvents_taskOwnerFrame_of_matching` derives structural
owner metadata under any fixed cache snapshot from source matching alone. It imposes no
additional acceptance or rejection-provenance law. Its actual batch-prefix construction
also retains live-root and retirement frames while replaying the FIFO prefix with its
supplied snapshot. `PendingReplay.pendingLedger_atBatchPrefix` independently supplies the
all-owner ledger at that consumed source cut. Live-root frames persist through cache
exposure and item preparation, before the stream carrier and final drain.
`UncancelledOwners` separates actual cancellation markers from notification consumption:
each unsettled registered task keeps
every uncancelled contributor live and linked. Initialization and local registration,
cache exposure, pruning, settled flushing, startup, rejection and ready-drain preservation
are proved. `UncancelledReplay` derives the certificate through generated registration
and actual source replay. A local fresh-failure
lemma now excludes invalidation of an uncancelled retired record when its ancestors are
also uncancelled, using this owner certificate instead of a notification-indexed ledger.
`GroupRemoval` separately identifies the cause of each newly added cancellation marker.
`UncancelledMarkers` proves local ancestor-marker closure through causal failure removal.
Permanent parent registration and live-parent safety recover a live record's ancestor
markers. Together these certificates establish uncancelled child-registration availability
for a fresh producer, without using failure-indexed healthy-owner accounting. The owner
certificate persists through scope integration when uncancelled contributors are available.
Ancestor-marker closure persists through scope integration, successful task flushing and
empty-shell pruning, using the permanent parent registry and live-parent safety.
`UncancelledSettlement` threads the success-only pending debt through the real contributor
fold, startup and ready drain. Its task handler consumes a success only after child
registration. `UncancelledStartup` preserves ancestor markers when cached rejection
startup immediately removes a group; a selected fresh contributing cause licenses the
removal without waiting for the queued notification.
`UncancelledClosure` carries these certificates through successful contributor folds and
recursive ready draining. Zero pending debt licenses each flush; the same closing record
supplies its ancestor markers before child startup. The shared `ParentCutFrame` and
`RootReplayFrame` proof bundles expose their existing structural preservation helpers for
this composition. They add no runtime metadata or source-contract requirement.
`UncancelledHandlers` composes task settlement, cached rejection notification and fresh
stream-item integration. `UncancelledReplay` derives the combined certificates over actual
valid started host batches, with each whole-batch cache snapshot and success-only consumed
ledger. Permanent registration retains each consumed failed task. These facts restore
`runNormalized_retiredHealth`: failed tasks cannot contribute to uncancelled retired scopes
or live-root ancestry. Its failure inventory follows actual batches; the old flattened
state bridge is unnecessary. The cancellation-aware replay helpers compile under buffered
source admission, including downstream reference conformance and the query bridge.
`UncancelledReplayFrame` exposes the derived source-accounting bundle and its preservation
helpers for reuse by other implementation proofs; it is proof evidence over existing state.
`UncancelledRetirementStability` proves that an uncancelled retired ref cannot acquire a
later cancellation marker, even through arbitrary subsequent host batches. Registration
cannot remark an old registered ref, while failed-group collection visits only live
records. This structural persistence requires no source or output-admission premise.
`SuccessfulRetirement` certifies successful carriers at their actual handler cuts and
carries their known uncancelled retirements through the remaining FIFO inputs and later
batches. `SuccessfulReleaseReplay` combines this durable structural result with final
actual-batch retirement health. The eventwise helpers retain explicit empty-snapshot
acceptance and immediate-output projections; the normalized theorem uses the actual
per-batch failure inventory. `SuccessfulSettlementAcceptance` likewise pairs raw
eventwise replay with its explicit empty-snapshot start check and immediate carrier output.
`ProducedTaskRegistration` and `RegisteredCarrierCoverage` use the same raw replay domain
for registration and strict-prefix contributor publication. `SuccessfulItemSafety` uses
selected causal cuts from the actual source-labelled blocks, retaining their original
positions independently of diagnostic reporting. `SuccessfulItemCertificates` retains
separate selected causal cuts and complete reporting cuts in that same witness. Structural
retired-contributor registration uses the explicit empty-snapshot eventwise start domain.
`StructuralCarrierCoverage` and `RetiredContributorPublication` compose those eventwise
registration and conservation witnesses on the same immediate-output ledger. Raw carrier
origins retain per-handler output positions and strict publication counts; the ancestor
publication and child-stream release proofs use that same empty-snapshot eventwise domain.
Task and stream producer-prefix proofs follow immediate output through their successful
folds and drains. Task-notice ancestor coverage retains startup’s queued notices separately
and transports noncancellation backward using monotone cancellation markers.
The source frame also retains cancellation retirement and is constructed at each actual
batch/FIFO prefix by `uncancelledFrame_atBatchPrefix`. `GroupClosureSettlements` uses that
cut's success-only owner accounting to place root-contributor successes before their
carrier, retaining the real batch partition in its witness. `ReleasedObjectStreamHealth`
uses final batch-end region exposure and retired-record health for its dependency guard;
it no longer replaces that state with an eventwise replay of flattened inputs.
`ObjectStreamSupportReplay` carries actual active object-stream support through individual
handlers and host batches. Each such stream retains a contributing uncancelled retirement
and an already consumed producer success; publication and notice provenance establish both
at activation. The certificate is available at actual FIFO cuts, independently of later
internal-notice dispatch.
`ActiveObjectStreamHealth` transports that uncancelled retirement through the complete
actual source run. Final retirement health then excludes fixed rejected causes even when
their reporting availability precedes notification. Source-block provenance retains the
original batch partition and FIFO prefix. `ObjectFailureCuts` derives complete-source
rejection evidence for both callback and aggregate-report availability.
`InformativeObjectFailureSafety` uses complete-source registration and source-item safety;
it does not require the rejection callback to precede the report cut.
`InformativeStreamFailureSafety` uses the same complete-source rejection evidence for
its object-produced stream guard. Together
with actual-cut stream health, the object and stream licensing proofs construct one
`MixedFailureWitness` over selected causal cuts and the separate complete reporting list.
The mixed guard-health regression exercises a stream failure followed by a deferred failure.
The internal reporting certificate retains the complete aggregate-count inventory as well
as availability and causal linkage. `FailureEventAdmission` uses causal invalidation for
node failure and the independent reporting inventory for group totals; stream totals
retain their single causal item. Positivity follows from the actual aggregate sources.
`StreamEventAdmission` composes those failed controls with successful stream closure on
the same witness. The failure-history regression retains separate causal and reporting
lists for both split and combined host batches. The drain-notice regression separates startup
removal from observed internal failure notification and follows the resulting
successful-carrier
positions. Its fixture-specific ledger agreement is derived from source provenance and
distinct payloads, rather than an equality between batch and flattened replay states. Item-handler notice prefixes and the
all-handler producer/ancestor bridges use immediate outputs with fixed-snapshot starts.
`StreamPublicationAdmission` retains the same original source-block causal selection
when combining successful-item safety with publication readiness. `GroupEventHealth`
uses permanent region exposure and durable retirement at the actual final batched state.
Mixed object causes enter the corresponding per-batch accounting ledger; no flattened
queue-state equality is used to establish successful-carrier health.
`SourceRegistrationCompleteness` retains unconditional child registration only for the
strict per-consumption eligibility domain. Actual source admission can include an ignored
object success whose task has retired. `SourceRegistrationAccounting` records registration
or a concrete certificate that every object-producer owner is cancelled; roots and
consumed item producers retain unconditional registration. `UncancelledReplayFrame`
preserves this certificate, producer ordering and source provenance through actual batch
and FIFO cuts. The buffered-success regression supplies a valid admitted batch that
refutes unconditional registration of every consumed success.
`StructuralRegistrationFromRetirement` uses producer-rank induction and uncancelled
ancestry to rule out that cancellation alternative for each structural contributor.
`ActualSourceFrames` exposes the actual before/after frames and eligibility at an earlier
dispatch boundary in the same host batch. Its resulting frames retain actual FIFO state.
`SuccessfulOwnerReplay` transports each consumed publication slice through that dispatch;
earlier eligibility supplies task disposition and permanent registration at consumption.
`ObjectStreamSupportReplay` uses the same prefix evidence to retain stream support while
pending internal notices change.
`ObjectPublicationAcceptance` reflects published object values to processed
source cuts using the successful carrier's durable uncancelled owner. Arbitrary supplied
successes are not assumed to have run. `ObjectStreamSupportReplay` uses these
prefix-derived source frames to retain retired producer support under buffered admission;
only item callbacks require current stream liveness in its release-support step. `ContributorRootReplay` and
`BufferedStreamSourceFrames` derive their supplementary path, link and child-stream
conservation facts from actual prefix frames, including callbacks retired within a batch.
`BufferedStreamBatchCuts.batchTail_conserves` derives suffix frames from the original batch
entry and its full rejection snapshot. It does not restart the admission checker at a
midpoint where buffered callbacks may already be retired. `BatchedNoticeHistory` derives
its ordered announcement inventory from source-prefix frames under buffered admission.
Actual child-stream release and item-notice ancestry use those same cached source cuts.
`ActualSourceFrames` carries registrations from a processed object-source cut through the
remaining FIFO inputs and later batches. Terminal object and item accounting uses those
actual registrations; item-success registration follows source-ordered stream liveness.
`SuccessfulOwnerAccounting` keeps consumed successful values published or buffered for each
uncancelled contributor. `SuccessfulOwnerReplay` carries that invariant over actual
buffered host batches and FIFO prefixes, retaining exact slices of one shared publication
ledger. A fresh callback with an uncancelled contributor has a live task node: retirement excludes its memberships,
while uncancelled owner accounting requires one. This derives live handling only for
the successful-value obligation that needs it. Ignored callbacks with no uncancelled
contributor do not create a new publication or buffer obligation.
Together with structural registration, retirement places every contributor in that
same-cut ledger prefix.
`SuccessfulCarrierCoverage` gives strict coverage before the immediate successful carrier.
`CarrierOutputCuts` preserves its real batch/FIFO origin and exact object-value offset,
and `BatchedCarrierCoverage` interprets that cut in the original publication ledger.
`AtomicCarrierCoverage` transports this result through publisher normalization and atomic
expansion without replacing actual batching with flattened source replay.
`BatchedPublicationProvenance` carries release adjacency, contributor ownership and exact
successful-source provenance over actual batches. `BatchedPublicationHistory` identifies
canonical positions and prefixes with normalized actual raw output. `GroupPublicationSupport`
uses those origins to retain the separate healthy releasing group and selected wire owner.
`GroupPublicationMatching` identifies that same raw value with its original occurrence
under the shared matching. `BatchedFailureReporting` transports cancellation explanations
over actual batches as emitted reports or pending FIFO notices, including deferred startup
notices. Turning this inventory into actual normalized reports requires an empty pending
FIFO; a prefix need not have forwarded every explanation yet. The normalized terminal
reporting bridge `NormalizedFailureReports` derives that empty FIFO from concrete
termination. `TerminalFailedContributors` and `RetiredFailureReports` use the resulting
actual positive reports; their prefix variants do not assume early forwarding.
The immediate-output cut also covers item carriers. `NoticeCarrierPrefixes` retains strict
object and inclusive item ranks at the same actual raw batch position; its source boundary
keeps the original batch/FIFO split and the item fold’s full rejection snapshot.
`BatchImmediateBoundaries` identifies the exact FIFO atomic-output prefix, including
preceding internal failure controls, separately from an optional terminal marker.
`AtomicHandlerBoundaries` recovers the corresponding actual publisher,
source handler and strict object offset, retaining silent FIFO inputs and earlier batches.
`RetiredGroupAccounting` uses final actual-batch source and publication frames to account
for healthy silent retirements. `EndpointFailureAccounting` connects the same final
per-batch failure inventory to the canonical causal cuts for the failed alternative.
`RawNoticeCompletion` retains immediate notice-carrier prefixes in its empty-snapshot
eventwise domain. Its item proof transports noncancellation back to the prepared state
before applying ancestor completion, accounting for possible startup removal during preparation.
`BatchedPublisherRegistry` derives actual-batch notice freshness, stream-role separation
and value shape. It identifies the publisher registry with open group notices on each
raw batch prefix; `GroupPublicationOwnership` uses that agreement for the selected
longest-path owner while retaining the independently healthy releasing contributor.
`GroupPublicationProducerOrder` uses strict actual-batch carrier coverage and registration
order within the same raw value block to publish reused-owner producers first.
`RawNoticeHistoryCompletion` preserves exact immediate output prefixes and source-start
checks in its empty-snapshot eventwise domain.
`BatchedPublicationCuts` retains producer readiness, permanent registration, membership
exclusion and the exact handler ledger suffix at one actual FIFO source cut.
`SnapshotMembershipBoundaries` carries those prior and local labels through owner folds
and ready-drain flushes before cached child startup, using the same supplied snapshot.
`RetainedNoticeContents` packages the concrete nonempty task record, producer prerequisites
and nonpublication evidence. `SnapshotGroupNoticeContents` derives that package at each
actual owner-fold or pre-startup drain boundary. `GroupCarrierNoticeContents` connects
the same ledger and source cut to the canonical group-success atom, retaining all original
source-run blocks and actual host-batch cache availability.
Item-origin inversion uses the same snapshot through every preceding item.
`AtomicItemNoticeContents` derives retained unpublished contents at the introducing
pruning boundary, before startup removal, with producer prerequisites from the original
source and publication labels from the original FIFO cut. Recorded contributor source
proofs use the actual batch failure inventory and unfiltered source-run blocks.
`ExactOutputCuts` retains complete strict output prefixes at actual batch/FIFO cuts.
`SnapshotNoticeCompletion` and `ActualNoticeCompletion` compose notice tracking through
cache exposure, owner folds and recursive drains. `CanonicalNoticeCompletion` uses those
cuts for both group and item carriers, preserving their common notice/closure projections.
A leading item receipt uses only closures preceding its preparation frontier.
`SnapshotNoticeFreshness` excludes protected earlier refs and separates actual handler
carriers under the supplied snapshot. `BatchedNoticeHistory` transports unique notice
inventories, permanent registration and retired ancestry through actual FIFO and host
batch boundaries. `CanonicalGroupNoticeFreshness` projects that same inventory through
publisher normalization and atomization.
`StreamNoticeRegistry` retains earlier stream announcements through actual host batches;
canonical item stream freshness uses their exact FIFO source cut. Group and stream
completion project the actual raw batch inventories. `FullPublicationAdmission` and
`FullControlAdmission` retain all source-run blocks when constructing the shared
nonterminal admission witness.
`StoredStreamReplay.batchPrefix_streamProducersSeen` derives stream provenance at real
FIFO cuts. `ProducedStreamNoticeCoverage` uses that provenance to recover every successful
item producer’s child-stream notice through actual dispatch, without a synthetic forwarding
tail. Registered terminal certificates use the actual
normalized final registry and the causal inventory for failure visibility.
Published object and item producers expose actual child registrations for terminal
accounting, including children removed by cached startup. Processed object callbacks use
`TaskAt.executionGroup_registered_after_batch_object`; consumed items use
`ProducerRegistrationAccounting.item_registered`. These retain the same final queue and
publication matching as the conformance witness.
`BufferedStreamSourceFrames` combines source provenance, buffered contributor links and
registered child-stream inventories. It conserves protected child streams across actual
FIFO handlers and host batches, excluding licensed cached rejections from successful
buffers before each transition. `BufferedStreamBatchCuts` derives the frame at an actual
FIFO prefix and conserves its remaining links through the rest of that host batch and
all later batches, retaining diagnostic forwarding and the actual terminal flag.
Their replay frames also retain pending controls through every dispatch boundary.
`ActualProducedStreamCoverage` derives complete child-stream notice coverage for a
successful object with a finally uncancelled retired contributor. The continuation begins
after actual dispatch, retaining the pending FIFO. `RawCarrierCoverage` and
`RegisteredCarrierCoverage` preserve publication counts through that same dispatch.
`ObjectProducedStreamNotices` applies it to the same canonical matched occurrence and
actual raw carrier, without requiring flattened replay or a separate notice premise.
`ProjectedOutputCuts` gives one positional batch/FIFO decomposition for arbitrary output
projections. `CarrierOutputCuts` specializes it to object values, so item-prefix bridges
can reuse the same batch-boundary reasoning without duplicating queue replay proofs.
`ActualSourceFrames` retains source evidence on both sides of an actual FIFO input.
`SnapshotItemPrefixes` follows item-first handling under that input’s full rejection
snapshot. `BatchedItemProducerPrefixes` combines registered-region provenance with exact
item counts to place producers before object blocks or by notice-carrier completion.
`GroupPublicationItemProducer` and `NoticeItemPublication` interpret those same prefixes
on the canonical matching.
`TerminalRegisteredTasks` uses actual final region inventory, contributor coverage and
empty terminal roots to account for registered tasks and producer-free groups. Permanent
root-task registration is transported through the actual normalized batch state.
`ProtectedNoticeReplay` follows the success-only ready drain with one fixed rejection
snapshot. Successful closure and subsequent startup preserve ancestor protection and
exclude reannouncement from every immediate output prefix.
`RootPathContinuation` transports an existing root path or permanent retirement through
cached startup, FIFO dispatch and actual host batches. Pending-notice changes preserve
these paths, and notice forwarding introduces no new group receipts. `OldRootCoverage` uses that
alternative at an actual batch/FIFO cut and empty final roots to exclude surviving
covered refs, including refs whose health is lost later.
`GroupAncestorProducer` retains each raw object origin’s actual batch/FIFO boundary.
Already-active releasing groups use root ancestry, uncancelled ancestor markers and the
same-cut publication frame to place ancestor producers strictly before the object atom.
`NoticeAncestorRetirements` certifies uncancelled task-bearing ancestor retirements at
successful release frontiers. The owner-fold and bounded-drain lemmas retain that evidence
through subsequent cached startup and closure. `UncancelledClosure.ClosureContext` is a
shared proof frame for the source-derived retirement and successful-ready obligations.
`UncancelledHandlers.taskSuccess_certificates` derives both marker preservation and the
notice-ancestor certificate for actual task success under the supplied rejection snapshot.
The existing marker-preservation theorem remains a projection of that stronger result.
`TaskNoticeFreshness` follows immediate owner-fold and successful-drain output in its
eventwise domain, keeping startup’s separately queued reports outside notice projection.
The item-integration and stream-receipt certificate lemmas derive the same uncancelled
ancestor retirement at each pruned frontier and carry it through cached startup, later
items and the final ready drain. Certificate transport uses only projected group refs;
it does not constrain payload values or introduce synthetic source events.
`SourceNoticeAncestorRetirements` derives that certificate for each actual handler from
its source frame and licensed cache snapshot. Complete structural registration and
success-only owner accounting then recover the consumed success of every task-bearing
ancestor contributor, independently of causal failure cuts and aggregate diagnostics.
`NoticeContributorAccounting` connects that success to the same-cut publication ledger: it
is already published, remains an exact buffer with a live contributor, or is this handler’s
incoming success. Each branch retains the same occurrence and source-derived ownership.
`HandlerPreparedFrames` derives parent and root certificates at the actual task and item
preparation phases, using the actual started-task lookup and its inherited declaration
context. The strict drain-carrier publication lemma accepts that phase’s
supplied rejection snapshot; its eventwise empty-snapshot interface is a specialization.
`TaskNoticeContributorAccounting` locates exact ancestor buffers after actual task
preparation. Source freshness and licensed rejections preserve earlier successes, while
the current success installs its own value with its structural owners.
`TaskNoticeSnapshotPublication` and `StreamNoticeSnapshotPublication` place those buffers
before their precise owner-fold or drain carrier. Leading item notices use the prepared
notice certificate and zero-step conservation, so they require prior publication already
at handler entry. `BatchedNoticeAncestorCoverage` preserves those strict positions through
the actual batch/FIFO ledger; `GroupNoticeAncestorAccounting` interprets them on the
canonical witness without flattening the source state.
`LeadingNoticeAncestors` uses the same actual source boundary and entry ledger for
item-carried notices. The item freshness proof retains the queued-startup channel, and
internal drain notice separation follows success-only ready selection at a fixed snapshot.
`SourceCarrierAncestorAccounting` derives earlier producer success and uncancelled
ancestor retirement from the actual carrier's source frame. Task and stream snapshot
publication lemmas preserve its exact cached buffer, including same-handler activation.
`BatchedAncestorProducerCoverage` composes that strict handler prefix with earlier batches;
`GroupObjectProducer` interprets it using the original canonical matching and object rank.
`ObjectPublicationAcceptance` recovers the exact successful source from that ledger and
locates its accepted cached task lookup in the actual batch/FIFO cut. Structural carrier
retirement independently establishes registration at the release handler endpoint.
The callback's eligibility may come from any earlier boundary in that batch; its source
frame transports task disposition and permanent registration to the consumption cut.
Group notice freshness and per-carrier uniqueness retain these declaration contexts
through actual item folds. Defer/stream role separation includes declaration-only records.
`EndpointFailureAccounting` carries every source rejection through first-availability
deduplication before selecting causal cuts, preserving final invalidation.
`ActualSourceFrames` also derives final child registration for every consumed successful
producer, including stream items, from the actual normalized replay frame.
Per-carrier uniqueness and eventwise notice separation retain the distinct queued-startup
channel. Publication-admission certificates preserve the original source-run blocks for
causal cuts, including blocks with no notification-visible causal event.
`NoticePublicationExclusion` interprets retained task memberships at the concrete pruning
boundary before cached startup can remove a node. `GroupNoticeTaskProvenance` retains
sound memberships and exact task descriptors through success-only drain prefixes under
the supplied snapshot; queued startup diagnostics remain a separate channel.
`NoticeTaskProducers` transports registered producer prerequisites through that same
success-only drain. `UncancelledAncestorPaths` joins live supporting ancestors to live
descendants using canonical parent links and uncancelled retirement, independently of
failure-inventory health. A missing parent would already have retired the live supporter.
`UncancelledProducedGroupCoverage` derives a live produced group's path from its
unsettled, uncancelled producer supporter and the registered task's declaration context.
The target comes from the child task's structural occurrence, covering inherited
contributors as well as newly declared groups. `ContributorRootReplay` retains those paths
through actual dispatch and pending-notice updates.
`SuccessfulReleaseReplay` obtains retirement from actual notification accounting, including
the retained pending-notice invariant. `FreshLiveRegionCoverage` uses the live subset
of a fresh parent-closed region as proof evidence, preserving the actual unfiltered
registration and pruning. `ContributorRootPaths` composes old paths and those fresh paths
through stream-item preparation and the final drain, without a failure-health premise.
`ContributorRootReplay` derives this coverage for actual accepted FIFO handlers and
normalized host batches. Empty terminal roots therefore retire every registered
contributor. `TerminalFailedContributors` combines that retirement with success-only
owner accounting: a consumed failed contributor cannot retire uncancelled. Existing
cancellation-report provenance then supplies its positive terminal completion, including
startup removals whose queued diagnostics are dispatched later.
`CoveredFailureReports` specializes this result to an actual accepted FIFO failure cut;
root-path and prior-health premises are no longer needed for terminal reporting.
`TerminalFailureOrigins` reports every record invalidated by the actual batch failure
inventory by selecting its consumed failing owner and inheriting that owner's real report
through canonical ancestry. The remaining healthy-failure lookup helper is restricted to
its empty-snapshot eventwise domain.
`CachedFailureReplay` uses final permanent registration and actual-batch retirement
health to identify absent failed contributors as cancelled. Task provenance is recovered
at the actual batch/FIFO failure-input cut from the corresponding source frame. `NonblockingReadiness` derives healthy active roots
from actual batch-end presence, rejection freedom and ancestry health, then specializes
the independently proved exact healthy counters. Neither proof flattens queue state.

The proof map includes `SelectedFailureCauses`, `SelectedGroupFailureInventory`,
`InformativeFailureInventory`, `InformativeObjectFailureSafety` and
`InformativeStreamFailureSafety`. The constructed accounting and admission witnesses
separate causal licensing from available aggregate reporting. Group notices, terminal
reporting and publication safety share the same observed history and publication matching.

`TaskNodeKeys` and `ActiveRejectionReplay` establish computation-key uniqueness and
exclusion of consumed failures from active owners. Parent-first installation preserves
ref properties, and actual dispatch preserves rejection retention and successful counter
accounting. Within-batch callback eligibility is recovered from its earlier dispatch
boundary. Available cached failures remain separate from consumed failure inputs.
The reference proof aggregate builds with these invariants and the startup conformance
witness, and the full regression suite passes.

Startup stream completion and produced-stream coverage use the ordinary raw replay and
publisher projections. Stream announcements retain their active roots until an observed
stream completion; enqueued group controls add no synthetic stream output. Full admission
uses the same nonterminal history as publication and failure certificates.

Closing-only replay includes observed group-failure controls. `ClosingFailureHealth`
transports its protected frontier through dispatch enqueue effects and uses the actual
dispatch state for the consumed-failure fold.

The proof is restricted to finite execution-generated work and valid host sources.
It does not establish completion from every admitted prefix, host fairness, eventual
resolver settlement, an infinite-run semantics, or refinement of the actual GraphQL.js
runtime. The [semantics guide](semantics.md#remaining-research-frontiers) separates these
open questions from the conformance proof boundary.
