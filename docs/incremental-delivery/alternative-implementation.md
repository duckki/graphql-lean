# Reference-backed alternative work queue

[WorkQueueAlternativeImpl.lean](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean)
defines a small alternative to the reference queue. It shares `Execution.Work`,
`ExecutionGroupValue`, `StreamItemValue`, graph events, work lowering, successful release,
publication owner selection, and response mapping. Its main algorithmic differences are
scope-local registration projections and inline last-owner disposal.

The finite Lean model and its proof reconstruction are complete. Generated replay,
factory/response equivalence, conformance, query observation, resource-prefix coverage,
and reader safety have proof witnesses. The source contract and public eager executors
are unchanged. Refinement of a concrete host implementation remains a separate
project; passing differential tests does not establish it.

Use this page for the algorithm and proof map. The [porting guide](porting-guide.md)
covers concrete representations, execution optimizations, and native obligations.
The [reference implementation guide](implementation.md) documents only the baseline.

## Comparison with the reference

Both implementations realize the same finite WorkQueue contract on generated work.
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

Shared behavior includes ancestor health checks, producer ancestry protection, per-item
child activation, and longest-path live wire-owner selection. Proof-only context/planning,
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

`taskFailure` checks health before unlinking the already-settled input. Announced owners fail
through actual removal; dormant owners retain their pending/error update. The input task
is not aborted again. `drainReadyGroups` shares reference readiness and successful release,
and uses the same inline removal for cached failures.

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
| Callback/source projection | `BufferedCallbacks`, `InterleavedCallbacks`, `BufferedWorkProjection` | Enqueue-time eligibility, actual intermediate filtering, FIFO receipts, unchanged effective source |
| Context/planner optimization | `Semantics.PlannerExecution.rootExecutionExact_holds` and planner modules | Complete recursive completion and final supply; no public executor change |
| Lazy computations / empty sequential scope reuse | `LazyComputation`, `EmptyScopeReuse` | Finite non-reentrant observations and guarded same-item projections |
| Sequential execution, key mapping, origins, and error recording | `RecursiveExecutionConstruction`, `PairedOriginCoverage`, `RecursiveCutAccounting`, `RecursiveRecordingCorrespondence` | General finite object/list/defer/stream execution with one compatible witness |
| Native audit composition | `NativeAudit.AuditWitness.localSafety` | Checked reduction requiring related actual observations and complete native inventories |

`registrationCore` and `registrationSnapshot` are phase-local proof views.
The algorithm does not construct snapshots, scan publications for cleanup, or allocate
proof histories. Optional failure-frontier lemmas describe topology; actual cleanup coverage
comes from the real transitions and cumulative effects.

Malformed raw states have deliberately weaker guarantees. Conflicting task descriptors,
missing memberships, ownerless records, or cyclic forests need not have exact reference
projection. The tests retain counterexamples to overstrong raw claims and construct the
generated restrictions independently. Finite-budget safety is not an exhausted-subtree
coverage theorem.

The execution refinements are not additional open modeling slices. Local and conditional
lemmas support the general recursive roots. Native object/container mutation, actual
callback histories, complete acquisitions, exceptional cleanup, rich error correspondence,
concrete costs, fairness, and infinite-source progress are not certified by these roots.

## Verification

```sh
lake build
lake lint
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeConformance
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeFailureReduction
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeResourcePrefixes
```

Whole-project checks pass. Root-witness axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`; no proof holes or added axioms are required.
