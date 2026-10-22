# Reference-backed alternative work queue

[WorkQueueAlternativeImpl.lean](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean)
defines a small alternative to the reference queue. It shares `Execution.Work`,
`ExecutionGroupValue`, `StreamItemValue`, graph events, work lowering, successful release,
publication owner selection, and response mapping. Its main algorithmic differences are
scope-local registration projections and inline last-owner disposal.

`FusedHandlerFrames` derives startup and ready-drain ownership from the actual task
lookup and execution declaration certificates. Task-child registration uses the derived
context for inherited contributors; stream-item preparation uses the generated source
certificate. Eventwise task replay and stream-item source frames supply those same
execution-derived declaration contexts. Handler and replay proofs retain internal failure
controls through their actual FIFO dispatch. `RegistrationHandlerDispatch` proves the
single-event bridge, including internal failure controls. `RegistrationDispatch` now
compares the actual queue and emitted work events: enqueue effects enter the shared queue
before the next FIFO entry, and cache exposure commutes with that enqueue. The batch
bridge proves exact residual queue correspondence, including pending controls, without a
batch-end failure accumulator. Inline host effects remain a separate observation channel.
`RegistrationBatchReplay` now establishes exact generated host-batch correspondence
using the same empty-root and empty-FIFO termination test. `RegistrationTermination`
preserves aligned semantic/reader flags across internal controls. The host-effect
projection continues to omit cleanup while proving actual handoff and receipt identities;
internal group controls introduce neither of those effects.

`RegistrationNormalizedReplay` lifts the actual batch bridge through the shared publisher
and the ordinary retained-FIFO runner. `CallbackControlHistory` independently derives
batch-entry head permission for pending controls from the unchanged enqueue/reduction
relation and source freshness. `BatchCallbackProjection` now requires nonrepeating closure
identities for its batch-admission helper, and its exact-filtering frame records control
permission alongside task tracking and active streams. The callback/source bridge uses
the same batch-local earlier-boundary eligibility as the reference. The source-law frame
derives internal-control permission
from the unchanged enqueue/reduction history. Producer support follows realized dispatch,
including notice enqueue effects. Cache exposure commutes with recursive group registration
by a traversal proof that preserves the exact visited refs and root frontier.

Initialization uses the same optional startup observation as the reference. Conformance,
observable equivalence, resource, and query witnesses use the unified API and the unchanged
independent correctness contract.
The structural key-renaming root now includes declaration annotations, including exact
commutation of transparent address lookup. Its focused build and unified-startup
initializer projection pass. `ScheduledWorkRefinement` retains the same ordered declarations
under its key map and preserves normalized structural lookup. Proof-side shared, planner
and scheduled executors retain the execution annotation. `ScheduledPositivity`,
`ScheduledKeyRegions` and `KeyTailExtension` carry declarations through positivity,
allocation bounds and extension of an existing key map. Buffered stream-root preservation
now follows actual FIFO dispatch, including internal
group-failure controls, which do not close streams. Queue equivalence and resource replay
follow the same dispatched boundaries.

The alternative shares the reference's recursive parent-first `addGroups` traversal,
including live-parent refusal and immediate child-link attachment. The
`GraphQLJsAlignment` fixture checks both queues' initial wire-ID order and complete
payloads for generated child-first declarations. Parent-cut registration and handler
frames now follow the recursive traversal, using execution-derived parent coverage.
The frames retain permanent retirement of cancelled refs and task declaration contexts;
they do not assume candidate lists are already parent-first. Realized enqueue effects
and internal failure controls preserve the same evidence. Buffered producer-support
projection also handles these controls as producer-free inputs. Handler and replay proofs
use these frames and the callback eligibility domain described in the
[reference guide](implementation.md).

`RegistrationActivation` proves that source installation commutes with cache-aware
reference group startup, preserving both immediate removal and queued aggregate notices.
Its initialization projection explicitly requires an empty rejection cache;
`RegistrationInitialization` derives that fact from real root registration and pruning.
`FusedRemovalInterruption` independently preserves the reader guard through removal and
startup, including failure branches. Arbitrary live-state fused-removal correspondence
remains a separate obligation; initial correspondence does not establish it.
`RegistrationScopeCompletion` retains the catalogue-based active-task completion bridge
with the empty availability snapshot used by this registration phase.

`FusedStartupProjection` proves exact queue and queued-notice correspondence for a
single cache-aware group start and its complete group fold. It derives the literal
removal frame from live-owner and membership evidence, then transports that frame through
every actual startup. `FusedReleaseProjection` lifts this result through source-first
installation and the delayed active-task fold, preserving the complete release queue and
queued notice order. Its premises describe the actual queue after those task starts.
The registration and dispatch proofs derive these premises at actual generated batch
cuts, retaining each whole-batch failure snapshot. The reference-side `GeneratedReferenceRemovalProjection_holds` witness now builds over
the actual batch owner frame and removal forest. The alternative registration and
release proofs transport those facts through delayed activation and fused cleanup.

Both initializers retain ordered fresh declarations from `Execution.Work.declareGroups`.
Pruning preserves registration order without sorting numeric refs. Synchronous initial
rejections remain explicit `InitialStartup` observations, and initialization stores resulting
notices in the shared queue's `groupFailureEvents`. Original announcements survive immediate
startup removal. Ordinary replay retains pending notices across batches and empty calls.
`InitialStartupProjection` proves equality of the actual initialized kernels, including
queued startup notices. Native initialization cleanup effects remain a separate comparison
boundary. `SuccessfulBufferRetention` carries declaration contexts through successful
closure, activation and failure cleanup; `FailurePathTransport` distinguishes immediate
closures from newly queued removal notices.

Both queues retain collected diagnostics separately from selected delivery causes.
At group startup they collect every cached task rejection before starting private work,
remove a failed group immediately and queue one aggregate notification. The alternative
uses its fused removal at that cut, preserving inline cleanup and temporary target order.
Startup returns `GroupFailureEvent` notices separately from immediate work events and
inline effects. `GraphBatchResult.handleGraphEvent` realizes those enqueue effects in
`State.queue.groupFailureEvents` before the next FIFO entry. Both runners forward an internal
notice only when its matching `GraphEvent.groupFailure` entry is consumed, preserving its
position among task/stream outcomes. Termination requires no pending notices. The local
`startGroup.errors` collection retains its upstream name and role.
Already active task failures retain the single-trigger owner pass.

[GroupStartup](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl/GroupStartup.lean)
proves `State.startGroup_reportsAllCachedFailures` for the actual alternative transition:
the one returned notice contains the entire cached sum, and the resulting state and
cleanup targets are exactly those of fused removal. No later activation occurs on that
branch. This local theorem is independent of the broader conformance and equivalence proofs.

Public definitions admit initially eligible callbacks whose tasks retire within a batch.
Generated replay, factory equality, response replay, conformance transport and query
correctness witnesses compile over this widened source domain. Native resource coverage,
recording and reader-safety witnesses follow the supplied rejection snapshots at actual
FIFO cuts. Callback/source projection preserves actual cached batch boundaries.
`RegistrationTaskCompletion.State.addTask_complete_eq_reference` recovers reference
registration after the active-task start with an empty availability snapshot; its new
computation record has no rejection. This local lemma does not establish startup or replay
equivalence. Concrete host refinement remains a separate boundary.

`StartupFailureCut` derives queued failure paths for owners removed during startup and
proves that those failed subtrees are absent before notification forwarding. The local
`DrainFailureCut` and `UnsettledTaskDrain` witnesses follow successful draining plus
cached startup removal; their failure alternatives name actual queued notices.
`StartupFailurePath` excludes both earlier and later successful carriers from each
failed subtree in the handler’s cleanup view. The enclosing pending-buffer cut witnesses also compile: their failure inventory combines
immediate failures and queued startup notices, while publication filtering still uses
immediate successful output. Eager registration evidence comes from actual cached batch
replay; the cut construction then follows the reference handler directly. The generated
release-failure regression checks immediate removal, separate queued notification and
same-transition source cleanup. Receipt preparation now follows the same retention-or-abort
classification across all items; later preparation preserves already emitted cleanup targets.
Incoming-task registration derives its pending and rejection evidence from actual cached
batches. `FusedUnsettledTaskDrain` carries the native owner-or-abort classification through
successful draining and failed child startup. `FusedTaskFailureProgress` handles the
separate failed-task owner fold; its regression includes a shared task with no computation
node. `IncomingTaskOwners` derives the all-handler unsettled-owner and incoming-owner
path witnesses from actual batch accounting and eager registration. Its failure inventory
also includes queued startup notices. Incoming coverage uses the retained declaration context;
internal notice consumption changes no unsettled task outcome. Resource-record witnesses
are transported explicitly through enqueueing at the actual dispatcher endpoint.
`FusedTaskHandlerProgress` derives activation
frames at the actual batch boundary and handles startup cancellation before the ready drain.
`UnsettledTaskProgress` uses immediate-removal accounting for publishing handlers and
proves that internal failure notices preserve task catalogues and cannot publish values.
Incoming-task and all-handler unsettled-task witnesses compile, and their focused
regressions pass. `TaskRecordPreservation` extends the same owner-or-abort result to
pre-existing task records, including owner loss during stream-item preparation. Its
registration proof uses certified stream-child declarations; the final record-or-abort
witness retains pending internal controls at the dispatcher endpoint. Internal notice
consumption preserves the observed task-completion history. Its
regression and the dependent dispatch resource-representation witnesses compile.
`TerminalResourceInvariant` derives endpoint roots from the same batch source frame and
live-contributor coverage, transports that evidence through actual notice enqueueing,
and uses the joint empty-roots/empty-FIFO terminal guard. `ResourceInitialization` derives
initial task records from execution-generated contributor membership.
`SingletonFailureSnapshot` proves that exposing a failure
immediately before its own notification preserves the complete native dispatch and resource
observation; the singleton terminal-resource regression compiles over that equality.
Arbitrary-width resource accounting, recording, and reader safety use the same retained
FIFO state and actual cached batch boundaries.

`ActivationRegistrationFrames` follows native fused removal directly to preserve whole
surviving group records under structurally matched tasks and sound memberships.
`SourceRegistrationFrame` carries those derived source facts through registration,
pruning and cached startup, without an activation-refinement premise. `StartupTaskProgress`
proves that a fresh linked task either keeps a live owner or contributes its abort to the
actual startup cleanup targets. It allows failure of any subset of the task's owners.
Its supplied-snapshot progress theorem excludes only the tracked task's own failure;
other available rejections remain visible during every start. `FusedUnsettledTaskDrain`
threads the same availability through successful release, child startup and recursive
draining, preserving the original empty-snapshot interfaces as specializations.
The available-task disposal regression checks inline abort of an unfinished companion
while the cached rejected computation is not aborted again.

`ActivationCatalogues` proves directly that native removal and startup retain permanent
task and group descriptors under any failure-availability snapshot. `ReceiptCatalogues`
uses those field facts for the actual item-preparation fold, without assuming that its
live owners survive cached startup.

`StaleCallbacks` proves empty-snapshot callback dispatch preserves the queue and returns
no immediate or queued startup notices. Ignored item receipts still acknowledge their
source. These local no-op lemmas do not justify removing a callback from a nonempty
cached-failure snapshot. `RetiredTaskNodes` and `RetiredTaskReplay` prove that a missing
computation with no remaining group memberships stays retired through a source-valid
continuation, under arbitrary cache availability. Source freshness and producer provenance
exclude re-registering the occurrence; an old notification may still appear in that
continuation. These are structural foundations for callback projection, not a completed
batch-output preservation witness. `RetiredFailureSnapshot` additionally proves exact
reference-handler equality after removing one such retired failure entry from availability.
The proof includes cached group decisions, fresh child registration, both output channels
and successful draining; it does not remove the corresponding FIFO callback.
`FailureCacheStability` and `FailureCacheReplay` prove exact rejection retention after
notification consumption. At the end of a source-valid finite batch every surviving
failure slot agrees with that batch's availability snapshot, so repeating exposure is
inert. This result permits stale notifications and requires no live-membership premise;
it does not equate availability with consumption at an earlier FIFO cut.
`CallbackSnapshotReplay` and `RetiredCallbackProjection` compose these results into exact
reference batch equality when callbacks retired before batch entry are filtered. The
premises name retired computation nodes, absent group memberships, fresh child identities,
and independently established raw/retained source laws. They assume no output equality.
`CallbackTaskFrames` and `CallbackTaskHistory` derive the relevant task evidence from the
unchanged interleaved enqueue/reduction relation. Every pending task remains represented
or globally unlinked across actual cached batches, and a stale callback at batch entry
therefore has retired memberships. Fixed producer provenance excludes re-registering that
occurrence in supplied child work. Callback records and history constructors live in
separate foundational modules so this argument does not depend on projection correctness.
`BatchCallbackProjection` defines batch-entry filtering and proves its admission and exact
batch result from those structural facts. `BatchCallbackWorkLaws` independently derives
retained work legality and stream cursors from entry-time producer support. Producer support
is threaded through the actual cached fold and then transferred to its identical raw endpoint.
The generated regression checks that this projector retains the original X=2 aggregate.
`BufferedStreamRoots` preserves active streams under arbitrary failure snapshots, and
`CallbackStreamHistory` derives stream activation at each consumed batch's entry from the
same interleaved history. Neither proof restricts batch width or requires draining the
whole pending callback buffer at once.
The batch projector reuses the source work laws' distinct internal control identities
when proving admission. It introduces no additional source law. Registration and stored
owner certificates also cover internal failure dispatch, which adopts no child work.
`CallbackProjectionSource` constructs retained work laws at every actual cached boundary;
`CallbackProjectionHistory` derives exact whole-history queue/publisher replay and source
admission. The unchanged interleaved history supplies both results with no extra source or
output premise. `BufferedCallbacks.projectBatch` and `projectHistory` expose this batch-entry
projector. Existing interleaved-history replay, source-validity and conformance statements
compile with their original assumptions. Same-batch and cross-boundary regressions retain
distinct projected inputs, and stale receipts remain in the original host inventory.
Replay preserves queued internal controls across silent calls; its terminal boundary
requires empty roots and an empty pending-control FIFO. `StopRootTopology` and
`PublicationExclusion` track the actual dispatch of those controls.
The optional native boundary-buffer helper requires entry-time permission for all supplied
callbacks; arbitrary raw-state filtering is not an unconditional native refinement.

Use this page for the algorithm and proof map. The [porting guide](porting-guide.md)
covers concrete representations, execution optimizations, and native obligations.
The [reference implementation guide](implementation.md) documents only the baseline.
The [complete definition map](graphql-js-correspondence.md) identifies upstream
counterparts and Lean-only responsibilities for both public queue modules.

The shared reference kernel also preserves retired task occurrences through explicit
internal-notice dispatch; this invariant compiles independently of alternative replay.
Exact consumed rejection slots and removal of retired entries from supplied failure
snapshots also compile through the revised dispatch. The retired-callback projection
uses a queue/output pair and realizes startup enqueue effects at every retained FIFO
entry, preserving both emitted output and the pending notice queue. Callback task
frames preserve structural membership, producer history and computation-key uniqueness
through that same dispatch. Initial all-owner accounting uses the execution-derived
declaration certificate, shared with reference initialization.

## Comparison with the reference

Both implementations target the same finite WorkQueue contract on generated work.
The alternative changes selected transitions and adds explicit host-effect observations;
it does not redefine execution or response mapping.

| Responsibility | Reference | Alternative |
| --- | --- | --- |
| Work and accounting records | Shared execution lowering and queue records | Reused unchanged |
| Task registration | Register and start eligible tasks during integration | Classify in one owner loop; return temporary active/rejected subsets |
| Child-work activation | Integrated work starts through the shared queue primitives | Complete integration/handoff precedes rejection disposal and delayed activation |
| Failed-group removal | Collect affected group references, remove records, and retain tasks with live owners | Shrink the affected subtree and capture last-owner cleanup before unlinking |
| Successful release and publication | Group flush, ready draining, normalized owner selection, and response mapping | Shared rules, with inline failed-removal effects |
| Host lifecycle | Work termination and finite publication histories | Additional receipt, cleanup, stopped-reader, and completion observations |
| Queue contract | Generated work, source validity, and executable-start discipline | Same premises and observable contract |

Shared behavior includes task-presence settlement checks, producer ancestry protection,
per-item child activation, and longest-path live wire-owner selection. `NativeHealth`
proves that absent-task settlements are ignored; its proof boundary uses retained task
rejections rather than an executable ancestor-health guard. Registration activation
commutation likewise follows group lookup and task-start order. Proof-only context/planning,
lazy-computation, empty-scope, and sequential-error refinements do not change either public
executor. Concrete implementation correspondence belongs in the porting guide.

Both Lean queues abstract readiness by scanning roots and retain finite registration,
failure, and ID history. Those shared mathematical representations need not become native
containers. The alternative does not add a second executor, work tree, general collection
framework, persistent resource ledger, or stream-index history.

## Representation and operation names

`State` contains the reference `queue` and a `stopped` flag. Work termination means
semantic completion; stopping the graph reader can instead mean interruption.
`TaskRegistration`, `IntegratedWork`, cleanup targets, and effects are transition results,
not extra persistent indices.

| Definition | Meaning |
| --- | --- |
| `State.queue` / `initialize` | Shared queue accounting and startup registration |
| `addTask` / `maybeIntegrateWork` / `startNewWork` | Owner classification, complete scope integration, and delayed activation |
| `cancelGroup` / `cancelTask` / `cancelStream` / `cancel` | Subtree, task, source, and whole-queue cancellation operations |
| `removeGroup` / `finishGroupFailure` | Real ownership removal with last-owner disposal |
| `taskSuccess` / `streamItems` / `taskFailure` | Registration-bearing success/receipt handlers and failed-task settlement |
| `GraphBatchResult.workQueueEvents` | Dispatch's accumulated work-event array |
| `State.queue.groupFailureEvents` | Pending internal failure FIFO; consumed only at observed matching dispatch positions |
| `HostEffect.adopt` | Relinquishing the accepted producer's complete exposed work |
| `HostEffect.acknowledge` | Completion of consumption for one stream-item receipt |
| `abortTask` / `cancelSource` / `abortStreamQueue` | Computation abort, source cancellation, and stream Queue abort |
| `responseFinished` | Starting the once-only response completion hook |
| `ResponseStreamCursor` | Initial response construction, guarded batch mapping, and abrupt closure |

`HostEffect` records inline operation order. It is neither a command buffer nor wire output.
Cancellation reasons, promises, exceptions, reentrancy, and asynchronous settlement are
outside these finite labels. The replay wrappers are observation adapters, not additional
runtime queues.

## Registration and activation

`addTask` visits the ordered contributor list once. For each existing group it installs
the membership and increments pending only when that occurrence is not already linked.
The same fold returns one of:

- `active`: at least one live contributor is a root.
- `registered`: at least one live contributor exists, but none is a root.
- `rejected`: every contributor record is absent.

A failed-but-live dormant group counts as registered. Rejection is an owner-presence
decision, not a healthy-owner test. Registration does not create computation nodes.

`maybeIntegrateWork` registers groups, tasks, and streams in that order. It returns released
roots and only the newly active/rejected task subsets, preserving scope order. Dormant tasks
need no temporary output list.

After complete integration and handoff, `startNewWork` installs all released roots/sources,
disposes rejected tasks, starts newly active tasks, then starts contributors of released
groups. It consumes the classification instead of scanning owners again.
An unstarted rejected task contributes its abort identity without evaluating latent work.

`taskSuccess` stages the result, registers child work once, settles its direct owners using
the reference success fold, activates released work, and drains ready groups.
`streamItems` completes registration, handoff, rejection disposal, and activation for each
item before the next item. Thus item order and child activation barriers remain explicit.

## Failure removal and cleanup

`removeGroup` performs one shrinking affected-subtree walk:

1. Find and delete the live group/root record.
2. Visit only that group's task memberships.
3. Use each permanent task descriptor to test whether all contributor records are absent.
4. For a last-owned task, capture its task/held-stream cleanup before `removeTask` unlinks it.
5. Visit the group's children in order.

A surviving contributor, including a failed-but-live one, prevents disposal. Missing references
consume no live-node fuel; each live visit removes a record. The finite budget totalizes
raw graphs. Native ports use an explicit stack, not repeated length scans or proof fuel.

One temporary first-encounter cleanup prefix spans an entire handler: rejected item tasks,
multiple failed owners, and cached failures in the ready drain. Cancelled references retain
reverse-preorder bookkeeping for the reference projection; it is not a native scheduling rank.

`taskFailure` retains the task's rejected outcome and removes active owners. Dormant owners
keep their memberships and pending counts for computation replay. The already rejected
input is not aborted again. `drainReadyGroups` shares reference task-order replay and
successful release, carrying cleanup targets across replayed failures before dispatch
expands them to host effects.

Successful publication transfers released child work. Ordinary successful unlinking must
not cancel that work. A source failure cancels its producer without aborting the stream
Queue or cancelling already admitted descendants.

### Acquired-resource boundary

Queue reachability is not a complete acquisition inventory. Unadmitted item work, unfinished
scopes, producer-owned suffixes, and pending cleanup remain host responsibilities.

Proof-only resource observations distinguish unacquired, producer-owned, queue-owned,
cleanup-requested, and released identities. Normal completion releases the settling
computation; adoption transfers independently supplied inventories; actual cleanup labels
license requests. A request is not asynchronous release.

Task coverage additionally tracks genuine unsettledness in the same input history.
Permanent catalogue entries and completed buffered values are not automatically unfinished
native leases. Generated prefix proofs derive live representation or same-dispatch abort
without requiring a computation node or adding source laws.

Concrete regressions live under
[`Tests/GraphQL/IncrementalDelivery/Fixtures/`](../../Tests/GraphQL/IncrementalDelivery/Fixtures):
`HeldSourceCleanup` checks raw last-owner disposal, `SharedOwnerFailure` checks
execution-generated shared work and source validity, and `RejectedTaskCleanup` checks
whole-work handoff followed by immediate rejected-task disposal.

Implementation-specific smoke tests and their invocation are described in the porting guide.

## Source contract, batching, and reader lifetime

`createWorkQueueForSchedule` accepts the reference
`EventSource (List ReferenceWorkQueue.GraphEvent)`. Conformance uses exactly
`ExecutedWork`, nonempty work, and `schedule.ValidFor work`.
No cleanup outcome, wire lifecycle, response equality, or stronger timing/fairness premise
is added.

Available host batches determine work-event publication batches; silent batches produce
no output. Source credits, callback buffering, graph batching, work-value grouping, response
mapping, and wire buffering are distinct. The model imposes no publication-per-host-event
rule.

For an item receipt, acknowledgement occurs after its FIFO consumption/handoffs and before
the ready drain's failure-cleanup suffix. It need not be the handler's last effect.
Partial native consumption requires finally acknowledgement and separate suffix disposal.

Terminal queue teardown clears accounting while preserving initial notices and true work
termination. Abrupt stop does not manufacture completion. The response cursor maps final
notices before clearing publisher records; the monotone ID counter survives. Explicit close
requests cleanup before starting the completion hook. Repeated close and later mapping are
silent. Hook invocation does not certify effect quiescence.

## Proof map

All ordinary theorems and proof-only helpers live under
[`Proofs/GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl/`](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl).
Public files contain definitions and statements only.

| Target | Witness or construction | Scope |
| --- | --- | --- |
| `replayMatchesReference`, factory equality | `RegistrationNormalizedReplay`, re-exported by `ReferenceReplay` | Exact generated normalized batches and residual projection |
| `responseReplayMatchesReference` | `ResponseReplay` | Shared publisher and actual guarded reader |
| `createWorkQueueForScheduleConforms` | `Conformance` | Unchanged reference contract and caller premises |
| Actual query observation/correctness | `QueryObservation`, `QueryCorrectness` | Same work, source, inputs, and factory; prefixes and complete outcomes |
| Literal removal safety and reference-state projection | `FusedRemovalSafety`, `FusedRemovalAccounting`, `FusedRemovalProjection`, `GeneratedFusedRemoval` | Raw finite safety; exact projection on independently derived generated frames |
| Real drain and failure-handler projection | `FusedDrainProjection`, `FusedFailureProjection`, `FusedHandlerFrames` | Compatible owner/forest frames at actual internal phases |
| Registration/handler correspondence | `RegistrationScopeCompletion`, `RegistrationTaskReplay`, `RegistrationStreamReplay`, `RegistrationDispatch` | Shared bookkeeping, delayed starts, exact generated handlers |
| Task/source retain-or-request progress | `FusedTaskHandlerProgress`, `PreparedSourceProgress`, `SourceRecordPreservation`, `TaskRecordPreservation` | All five actual handlers, including incoming and unstarted tasks |
| Compatible ownership histories | `ResourceHandoff`, `DispatchResourceInvariant`, `ResourcePrefixConstruction` | Initial/inter-input acquisitions, arbitrary-width FIFO prefixes, terminal and explicit-stop coverage |
| Reader/effect coverage and counts | `ResponseResourceSafety`, `ResourceEffectTrace`, `ResourceLifecycleCounts`, `ReaderLifecycle` | Same-run labels and legal histories; no invented acquisition or settlement |
| Callback/source projection | `BufferedCallbacks`, `InterleavedCallbacks`, `BufferedWorkProjection` | Exact cached replay and derived source laws for boundary buffers and unchanged interleaved histories |
| Context/planner optimization | `Semantics.PlannerExecution.rootExecutionExact_holds` and planner modules | Complete recursive completion and final supply; no public executor change |
| Lazy computations / empty sequential scope reuse | `LazyComputation`, `EmptyScopeReuse` | Finite non-reentrant observations and guarded same-item projections |
| Sequential execution, key mapping, origins, and error recording | `RecursiveExecutionConstruction`, `PairedOriginCoverage`, `RecursiveCutAccounting`, `RecursiveRecordingCorrespondence` | General finite object/list/defer/stream execution with one compatible witness |
| Native audit composition | `NativeAudit.AuditWitness.localSafety` | Checked reduction requiring related actual observations and complete native inventories |

The origin annotations retain all collected diagnostic origins in `Report`.
`RecordedCompletion.cause` separately follows the completion algebra's selected boundary
explanation, so exact erasure also preserves this metadata. Eager origin erasure and
literal/growing sibling comparisons retain it at each future task boundary. The origin inventory and its
length certificate remain additive. Work now retains both projections in `TaskOutcome`,
and the source contract uses its
[boundary reporting projection](README.md#collected-diagnostics-and-failure-explanations).
Recorded tasks retain `cause` beside the additive origin inventory. The scheduled
positivity certificate checks both collected diagnostics and the selected delivery
explanation; origin-only structural comparisons project the retained diagnostic report.
The proof-side `RecordedWork` and both origin executors retain ordered declaration nodes.
Erasure preserves those nodes, while their origin projection introduces no diagnostics.
Exact recursive recorded-work erasure, including deferred tasks, stream items, and final
allocation supply, is proved. Recursive recording correspondence supplies constructed
finite histories for the same cut and eager executions. The recursive work-refinement
foundation relates collected diagnostics and preserves selected cause metadata
separately, and derives refinement of delivered task outcomes. Recursive execution
constructors must establish both components. Selecting a completion explanation does not delete
collected or scheduled error records.

`registrationCore` and `registrationSnapshot` are phase-local proof views.
The algorithm does not construct snapshots, scan publications for cleanup, or allocate
proof histories. The registration snapshot follows task presence. Failure topology uses
the actual owner-removal block and task rejection state; held-source disposal is observed
after cleanup targets are converted to public handler effects. Registration cleanup skips an abort for a computation already storing a
rejection. Occurrence-indexed rejection provenance is proof evidence derived from input
replay and preserved through delayed registration, owner settlement, and activation.
A separate rejection invariant preserves this evidence through each interleaved receipt
item; membership-retention helpers keep their original registration frame.
Actual replay supplies its settled-occurrence set, and source freshness excludes any
previous rejection for an incoming task. Fresh returned tasks therefore receive the
registration abort without adding a runtime health check or a new source requirement. Optional failure-frontier lemmas describe topology; actual cleanup coverage
comes from the real transitions and cumulative effects.

The raw last-owner task-progress helper is restricted to computations without a retained
rejection. Removal traces preserve this evidence; an already rejected computation can
disappear without a redundant abort. The shared failed-owner retention proof and bounded drain thread this condition through
the entire actual rejection replay. Public abort effects are obtained from the resulting
cleanup targets. Generated unsettled-task progress derives the condition from source provenance and
freshness for all five actual handlers. Optional failure-cut topology follows the full
reported owner block: emitted roots are initially active contributors, their subtrees
are absent after the pass, and subsequent successful carriers cannot cross those paths.
These are derived implementation facts, with no stronger host-source law.

Task-resource representation includes the concrete unrejected-computation test as well
as a live group membership. A retained rejected task still represents group accounting,
but cannot witness a queue-owned computation lease. Initial identities and generated
fresh source replay derive this test through registration, failure passes, and drains;
the resource-prefix construction and represented stop-safety proofs are rebuilt on that
same history. No acquisition completeness or runtime failure-origin metadata is added.

Malformed raw states have deliberately weaker guarantees. Conflicting task descriptors,
missing memberships, ownerless records, or cyclic forests need not have exact reference
projection. The tests retain counterexamples to overstrong raw claims and construct the
generated restrictions independently. Finite-budget safety is not an exhausted-subtree
coverage theorem.
The fresh-item live-root coverage helper retains actual cache-aware startup. It uses
pre-startup coverage and the finite removal forest to preserve a covering active root
for every surviving target, even when failed startup removes other root regions.
`LiveAncestorCoverage` derives task-child contributor and parent coverage from the
registered producer's declaration context. Recursive registration preserves its ancestry
and cancellation frames without assuming declaration list order. Its child-contributor
coverage also handles inherited refs absent from the new declaration list.
`LiveStreamRootCoverage` similarly supports every candidate of a fresh parent-closed item
region. Stale internal controls preserve both queues when they do not match the current
FIFO head; matched forwarding announces no new stream source.
`LiveContributorStreamCoverage` threads declaration and cancellation certificates through
each prepared item. `LiveContributorReplay` preserves those paths across actual FIFO
dispatch, including pending internal controls and accumulated callback eligibility.
The prepared-source and available-source handler witnesses retain concrete source-record
locations through failure-control forwarding and enqueue effects. These steps change
pending notices without inventing resource acquisitions or cleanup effects.
`ResourceBatchReplay` follows the same dispatch fold and requires an empty pending FIFO
before observing terminal stop. `RegistrationSnapshot` carries the registered task's
declaration context through integration, projection and record clearing, so inherited
contributors need no synthetic declarations.
`GeneratedBufferDisposal` treats internal failure controls as distinct from registration
inputs when deriving ownership and cleanup for prepared child streams.
`RegistrationRelease` projects delayed activation through fused startup using the
concrete pre-startup task-owner frame and finite removal forest. Its item projection
requires those same frames after registration, pruning and the delayed active-task fold;
generated replay callers must derive them at that cut. Arbitrary malformed queue states
do not receive an unconditional startup projection.
Rejection provenance uses a weaker field frame: fused removal only deletes task nodes
at every finite budget. Cache-aware startup and delayed activation retain licensed
rejections directly, without needing full queue projection or a removal forest.
`FusedRemovalGuards` similarly proves interruption and termination field frames through
actual cached group startup, delayed activation and successful ready draining. Forwarded
startup notices remain distinct from immediate failed-task settlement output.
`FusedDrainProjection` preserves the reference queue, immediate events and queued startup
notices under the same supplied snapshot. The successful drain derives every child
startup frame before applying fused removal projection; cleanup targets remain the
alternative's separate output. Generated actual endpoints supply the initial owner and
finite-forest frames independently.
`FusedCleanupTargets` proves one duplicate-free cleanup prefix through successful ready
draining and cached child startup under the same snapshot. Queued failure notices use
their separate output channel.
`FusedHandlerFrames` derives task-success and prepared-item drain frames for its explicit
eventwise replay. Successful startup uses the returned queue projection, and independent
source bookkeeping supplies registered groups at that same empty-snapshot cut.
Task-success registration also derives owner and forest frames before cached startup.
Its retired-ancestor frame uses the generated child's declaration certificate and live
registry, including recursive parent-first installation and refused descendants.
`RegistrationTaskReplay` uses those concrete frames to project the ready phase and full
handler, retaining both immediate events and queued startup failures. Its generated-prefix
wrappers retain the explicit empty-snapshot acceptance premise.
`RegistrationStreamReplay` retains queued notices in the actual per-item accumulator and
projects each delayed startup using owner and forest frames at its pruning boundary.
The generated fold derives those frames for every item prefix; its final drain retains
both output channels under the same eventwise replay premise.
`RegistrationDispatch` composes those handler projections at accepted eventwise prefixes
and preserves queued notices. `RegistrationHostEffects` reads the actual effect component
separately: FIFO adoption, one receipt acknowledgement, unique cleanup starts and absence
of dispatch-time response-finished hooks retain their existing witnesses.
Interruption and semantic-termination frames quantify over the supplied rejection
snapshot. `RegistrationTermination` threads that same snapshot through the actual FIFO
fold and notice-forwarding wrapper, retaining aligned lifecycle flags. The ghost label
projection reads the separate host-effect component.
Startup retains cleanup targets already emitted by rejected registration, including
when cached failures remove further groups. Rejection abort, receipt acknowledgement and
fused failure-resource proofs read cleanup and host effects from their separate result
components; queued notices carry no host effects.
The bounded drain source-progress proof follows successful release into cached child
startup. Startup either retains an existing held-source record or returns its actual
cleanup identity; the cumulative target list preserves that request through later drains.
The same startup result covers delayed active-task installation. Failed-group removal
preserves existing stream roots, so released registered sources remain active through
startup. `FusedTaskSources` composes the owner fold with that actual startup classification
and ready draining: held sources retain their record, become active, or enter the emitted
cleanup-effect channel. Queued group notices are separate. Its eventwise source wrapper
uses explicit empty-snapshot acceptance.
The reusable task and stream classification lemmas also accept the derived source frame
at an actual queue state. `PreparedSourceProgress` constructs that frame after the real
earlier batches and applies the two classifications at the next-input boundary. Exact
prepared snapshots, ready-drain ownership and source inventories are derived there;
earlier batches need not admit or equal an eventwise flattened replay.
`SourceRecordPreservation` includes cleanup during item preparation: an old held buffer
may disappear during cached-failure startup, with its cancellation retained in the same
receipt’s effects. `ResourceBatchReplay` observes dispatch with the supplied batch snapshot
and records internal notices at their supplied FIFO positions. Termination requires an
empty pending FIFO, matching the actual dispatcher.
The source-record and resource-batch regression modules verify these preservation roots.
`RegistrationSnapshot` retains explicit preparation snapshots and uses immediate events
for its optional mathematical failure-frontier trace; deferred notices are separate.
The pending-buffer cut signatures use that immediate-event projection. The successful
retention frame follows the actual success-only ready drain; failure-path transport
embeds preceding immediate carriers in the complete closure certificate, which also
contains returned startup notices. These supporting lemmas do not by themselves prove
the remaining generated failure-cut construction.
`PublicationTransfer` derives prepared-buffer conservation from actual normalized source
accounting, stored-value provenance and source inventories. Successful handler retirement
licenses transfer without a flattened-prefix state bridge. `PublicationExclusion` uses
that retirement and allows startup to shrink the live group set; its successful-key
projection reads immediate carriers. The publication-transfer regression verifies notice,
active-root and cleanup reachability on the same dispatch.
Regression fixtures cover both shared-source transfer and cleanup during failed child
startup. Active cached failures remain pending until their FIFO notification.
Local live-contributor coverage also retains the supplied snapshot through task success,
fresh item preparation and the final drain. Its item frame derives complete parent links,
canonical fields and the finite removal forest before cached startup; these justify
uncancelled-parent safety after immediate failed-child removal. `LiveContributorReplay`
derives complete live-contributor coverage over actual normalized batches. Its task step
uses cancellation-aware owner links and ancestor-marker closure, avoiding healthy-owner
accounting at notification cuts. The shared source frame advances consumed successes
under each whole-batch snapshot. Buffered replay derives independent source frames at
each FIFO prefix, including inputs retired since batch entry; coverage preservation
does not require current callback eligibility. Its eventwise wrapper explicitly uses
empty-snapshot acceptance; normalized replay follows real batch boundaries. The executable fused
failure reduction checks receipt acknowledgement before FIFO failure cleanup and keeps
startup notices separate from immediate handler output. A registration regression records
the transient rejection-metadata difference under a nonempty snapshot: delayed activation
can expose a newly active task rejection before reference registration does. The same
cache exposure aligns those intermediate records, and the fixture checks matching queue
and wire output after the FIFO failure. This fixture does not establish a generated
whole-batch projection theorem. Scope completion proves the general comparison after
cache exposure: cache-aware delayed starts and eager reference registration yield equal
exposed queues and identical new-work notices. Unique pre-startup task keys follow from
eager scope completion and the fact that activation only appends task nodes. Release startup preserves
the exposed-state relation and the exact queued failure notices, using the concrete
pre-startup owner and removal-forest certificates for fused cleanup. Successful group
closure also commutes with cache exposure: the task flush keeps values and held-stream
refs, while its closing/pruning tail is independent of rejection slots. The recursive
reference drain preserves the exposed-state relation and exact immediate/queued output;
the fused drain transports that result through its concrete owner/forest projection.
The contributor
settlement fold preserves exposed queues, immediate output and release descriptors.
Live-owner bookkeeping certificates transfer through the same relation. Cache-aware task
success composes exact eager settlement completion, delayed activation, startup and draining
to preserve the exposed queue and both output channels. The proof notation for the
pre-drain phase retains the supplied snapshot. Reference scope registration also preserves
exposed queues and all release descriptors: group registration is independent of task
slots, eager insertion appends a common fresh slot, and held-stream updates preserve the
relation. Per-item stream registration preserves that relation and every carrier field,
including group/stream notices, item order and queued failures. Concrete ownership and
forest frames justify delayed startup after pruning. The complete item fold transfers
these local certificates at every reference prefix; the stream handler composes it with
the fused drain, preserving exposed queues and both output channels. Closing these local
certificates over actual source batches now supplies complete single-event dispatch
correspondence at each batch/FIFO cut. Local task and item startup certificates derive
from structural live-root, ownership and child-uniqueness frames, retaining the supplied
snapshot through item preparation. They impose no healthy-owner assumption. Common
exposed inputs also produce the same actual dispatch, including its inline effects.
The complete FIFO fold preserves the exposed queue and both output accumulators.
Its last dispatch recovers exact residual correspondence: all failures in that batch
snapshot have been consumed or are the last input, and freshness excludes them from new
child work. The actual batch wrapper forwards the same queued notices and preserves
exact wire output through termination; its cleared residual is the existing reference
projection. Normalized replay and the online reader now follow these actual batch cuts.
Factory equality depends only on replay correspondence; reference conformance transport
is isolated in `RegistrationRefinement`. When newly introduced child tasks are absent from the supplied snapshot,
local task-success and complete stream-receipt correspondence also preserve the exact
residual queue: cache-aware delayed child starts then equal ordinary eager completion.
This criterion is internal source evidence, not a new host requirement. Finish-hook
accounting follows each handler and FIFO batch with its actual availability snapshot;
queued startup notices remain separate from the inline cleanup-effect projection.
Generated task-failure disposal retains that effect channel when proving source cleanup.
The proof-only registration snapshot erases metadata from the actual item accumulator,
including its cumulative cleanup prefix. Its projection follows structural certificates
at actual normalized batch endpoints, without flattening their state or assuming
additional source admission. The next-input boundary retains exact preceding batch
replay and acceptance of the next supplied batch, with immediate and queued dispatch
outputs separate. It supplies no flattened-prefix acceptance or state equality. Stream
receipt cleanup and successful held-source transfer use the immediate/effect channels
separately from queued notices. Their eventwise preparation wrappers retain the explicit
empty-snapshot acceptance premise; batch-aware source/resource wrappers use the actual
whole-batch availability snapshot.
`GeneratedResourceBoundary` derives the actual resource observer's FIFO-prefix queue after
common batch cache exposure, together with its reader guard and independent consumed-task
ledger. `ResourceCacheExposure` transports the complete resource observation, including
ordered cleanup actions, across that exposed-state equality. These cuts retain availability
from the entire host batch without flattening its queue replay.
The same actual exposed cuts now carry complete structural source certificates and
rejection provenance bounded by the supplied source, including later FIFO notifications.
`ResourceCacheRecords` transports all active/buffered source records across common
exposure. Task-record transport excludes the tracked task's own available failure,
matching the unrejected-computation condition in the resource representation predicate.
Receipt-wide incoming and existing task progress also retain supplied availability through
every item registration, pruning and startup. Rejection provenance bounds the supplied
snapshot, so the tracked unfinished task either keeps an owner or receives an actual inline
abort. Rejected object registration and receipt cleanup projections preserve those targets
through the same cache-aware ready drain. Existing empty-snapshot proof interfaces remain
specializations of these local constructions.
`AvailableTaskSuccessProgress` extends prepared-task retention through object success to
arbitrary supplied snapshots. It transfers live-owner and forest certificates through the
derived cache projection, then composes actual startup and drain effects. The generated
eventwise task-success witness now specializes this construction to empty availability.
`AvailableStreamTaskProgress` supplies the corresponding receipt proof, deriving each item
certificate from structural source frames and retaining the complete snapshot through
preparation and draining. It also specializes the generated eventwise receipt witness;
the cumulative cleanup-start equality includes this same supplied availability.
`AvailableTaskHandlerProgress` composes all five handlers at an exposed source cut, using
cache stability derived at FIFO boundaries. Registration snapshots now retain supplied
availability in their receipt branch. `AvailableRegistrationFrame` derives their catalogue,
membership and source consistency from the independent pending ledger; larger exclusion
sets weaken only the proof obligation for remaining unfinished tasks. The generated
eventwise prepared-task root specializes this common local proof.
Existing task-record progress now composes cache-aware registration and handler progress
at the same source cut. The consumed ledger licenses settlement while a larger exclusion
set bounds available failures and protects the tracked unfinished computation. Actual
receipt owner loss remains an emitted abort. The eventwise existing-record witness
specializes this proof with its original premises.
`AvailableSourceStartup` proves active/buffered source-record progress through the complete
cached startup loop. It preserves the stored value and attachment even when rejection
slots change, or identifies the actual inline source-cleanup target. `FusedTaskNodeKeys`
supplies computation-key uniqueness through the concrete removal walker and group startup.
The available-source regression checks two newly exposed failures aggregating to five
errors while disposing the held source once and skipping both already-rejected tasks.
`AvailableSourceDrain` composes these record alternatives through every actual mixed-drain
step with supplied availability. Successful selection transfers the held source into active
roots; cached startup and later draining retain its record or its cumulative cleanup target.
This proof permits rejection-slot changes while preserving the source's value and attachment.
Actual resource FIFO cuts also derive unique computation keys and child-source inventories.
Scope integration preserves those keys; common cache exposure transfers inventories using
unchanged attachments and the same stream registry. No inventory completeness or endpoint
resource law is inferred from these structural certificates.
`AvailableTaskSourceProgress` derives task-success ready ownership, forest, key and inventory
certificates from the reference cache projection. Actual settlement then retains or releases
the prepared source, and cached startup/draining retain its record or emit source cleanup.
The existing generated prepared-source witness uses this proof for task success. Source-root
startup also retains supplied availability; record transport depends only on the lower-level
record and inventory definitions, independently of the observer layer.
`StreamItemSourceFrames` shares item-prefix certificates below the task/source ownership
proofs. `AvailableStreamSourceProgress` derives actual receipt-ready certificates through
common exposure, then accounts for source records and real cleanup in the complete receipt
trace. `AvailablePreparedSourceProgress` combines both registration-bearing handlers at an
exposed source cut. The existing generated prepared-source witness specializes this common
proof without changing its premises or conclusion.
`SourceRecordRegistration` preserves existing source locations through registration, including
updates to the same parent computation. `AvailableSourceRegistrationProgress` follows those
locations through the actual cached receipt fold and its cumulative cleanup targets.
`SourceRecordFailureProgress` accounts for direct failure removal while retaining stored
source attachments. `AvailableSourceHandlerProgress` combines all five handlers: each existing
source remains represented, completes normally, or enters that dispatch's actual cancellation
trace. The generated existing-source witness specializes this shared proof; its statement
and the public definitions are unchanged.
`AvailableIncomingTaskProgress` and `AvailableIncomingSourceProgress` construct record or
cleanup alternatives for actual adopted work at exposed FIFO cuts. `AvailableResourceProgress`
composes existing and incoming leases with the same observer effects. Its intermediate batch
invariant retains consumed-outcome freshness for every owned task, and requires records for
tasks outside the complete batch's outcome set. A later failure can already be cached while
its independent lease awaits notification. At the complete batch cut the two outcome sets
coincide, recovering the established full record invariant without changing its statement.
`RawResourceInvariant` transports those local proofs to actual observer cuts through common
cache exposure and the dispatcher's retained notice FIFO. Its resource-record frame is
unchanged by enqueueing internal controls. `FIFOResourceInvariant` composes the
supplied-snapshot fold and recovers full representation at batch completion. Before terminal
erasure it derives topology and absence of owned leases at the exposed pre-clear endpoint,
using the actual empty-roots/empty-FIFO guard. `BatchProducerIdentities` names the same
actual supplied-snapshot fold as the observer. Contributor coverage follows that batch's
admitted FIFO prefixes, independently of native acquisitions.
`ResourceEffectTrace` carries the same availability through producer-label projection,
per-dispatch action coverage and the complete observer fold. Internal failure controls
emit no producer-adoption effects. Queued group notices add no
resource effects. The reader effect-coverage and close-safety roots retain their statements.
Tuple regressions project immediate events, inline effects and queued notices separately.
The source-drain fixture releases a dormant failed child from a ready parent, then checks
post-acknowledgement cleanup. The unfinished-task fixture checks that cached failure removal
occurs at startup rather than during ready draining. Reporting fixtures retain aggregate
counts for all cached causes.

`StopRootTopology` derives root multiplicities from actual batch/FIFO notice sublists
and their unique generated inventory. `AdoptedSourceRecords` derives fresh source
registration from producer provenance at the same actual batch endpoint. Conformance
transfer uses the rebuilt reference witness through `RegistrationRefinement`. These
proofs retain the existing public premises.
`RegistrationActivationSafety` uses `ActivationFrame` at the concrete queue after active
task starts and before released group startup. It proves removal/subset behavior and
retains an exact buffered lookup only when a contributing owner survives.
`GeneratedActivationFrames` derives that evidence from the independently checked eager
settlement frame; it assumes no desired startup endpoint or additional host law.
`RegistrationTaskRetention` carries its registration frame through this actual startup
subset, and `StopTraversal` obtains root presence from actual normalized batch replay.
Registration accepts contributors from either retained registry entries or fresh declarations.
`AvailableRegistrationFrame` derives object-child coverage from the permanent producer's
declaration context; stream-child coverage follows the executed work's certificate.
Stream admission, adopted-source progress and generated buffer-loss cuts handle internal
failure controls explicitly: consuming a notice introduces no stream action or adoption.

`State.acceptsBatch` admits each callback when it was eligible at an earlier dispatch
boundary in the same host batch. Thus initially eligible notifications survive
retirement during the batch, and earlier events can start later callbacks' work. The
complete batch supplies the rejection snapshot throughout dispatch. This is shared source
admission, not additional native queue state or an eligibility ledger. The definition-level
`WorkSchedulerBufferedFailureSnapshot` regression checks this case: parent success releases
a child sharing two rejected tasks, and the first failure notification removes the last
live owner of the second. The full admitted batch reports both cached causes for that
child. Dropping the stale second failure reduces the child's count from two to one,
including after publisher normalization. Eventwise callback filtering therefore does not
generally preserve output under batch-wide cache semantics. The callback/source bridge
therefore filters at batch entry. It retains initially eligible callbacks throughout the
batch, and removes older retired callbacks only after deriving both missing computation
nodes and absent memberships. Generated work laws, source admission and exact publisher
replay are proved separately and composed on the same original interleaved history.

The execution refinements are not additional open modeling slices. Local and conditional
lemmas support the general recursive roots. Native object/container mutation, actual
callback histories, complete acquisitions, exceptional cleanup, rich error correspondence,
concrete costs, fairness, and infinite-source progress are not certified by these roots.

## Verification

Repository-wide verification commands are in the [development guide](../development.md).

Initialization, response initialization, and source validity use one optional startup
observation, defaulting to empty. Definitions, proofs, and regression tests use this shared
API. The full build, test build, lint, and changed-file formatting checks pass. The core
conformance, query, equivalence, and resource witness audit uses only Lean's standard axioms
(`propext`, `Classical.choice`, and `Quot.sound`).

Declaration wrappers retain key-renaming refinement and leave recorded diagnostic origins
unchanged. Both recursive and eager origin uniqueness proofs follow the declaration branches of
their recorded executors. Literal deferred-plan refinement retains declaration order,
bounds inherited declaration refs through the input context, and transports those refs
with the final constructed renaming map. General recursive plan refinement uses the same
declaration bounds and map transport. Origin, cut-accounting, and recording relations
follow declaration wrappers without adding diagnostic origins or cancellation sites.
