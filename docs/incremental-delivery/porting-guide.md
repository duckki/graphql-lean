# Porting the alternative work queue

This guide accompanies
[WorkQueueAlternativeImpl.lean](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean)
and the [algorithm/proof guide](alternative-implementation.md).
It describes how to implement the same logical transitions efficiently without copying
Lean lists, fuel, snapshots, or proof histories into production.

Concrete correspondence here uses GraphQL.js PR #4859 as a baseline and the companion
`graphql-incremental-delivery-js` implementation as a porting example. The Lean definitions
and proofs stand independently of either repository's history.
Public failure-reporting definitions separate collected diagnostics from selected causes;
the abstract proofs and recording refinements await migration to these definitions.
Formal JS refinement, concrete cost bounds, native acquisition completeness, exceptional
cleanup, fairness, and infinite-source progress remain separate projects.

## Shared semantics and deliberate differences

Keep `Execution.Work`, `ExecutionGroupValue`, and `StreamItemValue` as the semantic
work/value model. Reuse reference lowering, successful release, owner selection, initial
notices, and response mapping. Native lazy computations and iterators may replace pure
precomputed outcomes, but must represent the same work and identities.

The public alternative models two explicit algorithm changes:

- Register each exposed scope once and return only newly active/rejected task subsets.
- Remove failed ownership and request last-owner cleanup in the same shrinking subtree walk.

It also observes complete ownership handoff, per-receipt acknowledgement, deduplicated
shutdown, record retirement, and guarded response completion. Context/planning, lazy
construction, and empty sequential-scope reuse refine shared semantics in proof modules,
without modifying the public executor or introducing another public Work tree.

The baseline already has release-ordered ready membership, ancestor health checks,
producer ancestry protection, per-item child activation, and seeded wire-owner selection.
Both runtimes remove individual closed IDs. Preserve these shared behaviors.

The reference Lean kernel uses root scans and finite retained catalogues. Native ready
Sets, weak failed membership, and open-ID Maps are common representation refinements,
not new public algorithms or automatic consequences of choosing a collection.

The original `ExecutedWork`, source-validity, and executable-start premises remain unchanged.
Never add desired cleanup, endpoint coverage, or wire equivalence as a host-source law.

## Names and native operations

In the companion JS port, registration/removal live in `WorkQueue.ts`, response lifecycle
in `IncrementalPublisher.ts`, and lazy computation/executor construction in `Computation.ts`
and `IncrementalExecutor.ts`. These are correspondence notes, not Lean dependencies.

| Lean definition | Native counterpart |
| --- | --- |
| `State.queue` / `initialize` | Queue closure records and initial registration/start eligibility |
| `addTask` / `TaskRegistration` | One owner loop classifying active, dormant registered, or rejected |
| `maybeIntegrateWork` / `IntegratedWork` | Complete scope registration and temporary active/rejected subsets |
| `startNewWork` / `disposeRejectedTasks` | Install released ownership, dispose rejected tasks, then activate |
| Shared `addGroups`, `addStreams`, `removeTask`, `finishGroupSuccess` | Registration, unlinking, and successful release |
| `removeGroup` / `finishGroupFailure` / `drainReadyGroups` | Actual failed-subtree disposal, including cached failures |
| `cancelGroup` / `cancelTask` / `cancelStream` / `cancel` | Subtree/task/source cancellation and whole-queue teardown |
| `CleanupTarget` / `uniqueCleanupTargets` | Identities and first-encounter temporary deduplication |
| `GraphBatchResult.workQueueEvents` | The dispatch accumulator |
| `HostEffect.adopt` | Relinquish the accepted producer's complete exposed work |
| `acknowledge` | This STREAM_ITEMS receipt's `consumed()` callback |
| `abortTask`, `cancelSource`, `abortStreamQueue` | Computation abort, iterator/source cancellation, Queue abort |
| `responseFinished` | Start the once-only completion hook |
| `ResponseStreamCursor` | Guarded initial/batch mapping and abrupt close |

Effects are ordered inline observations, not a command buffer to execute after child
computations start. `adopt` identifies the task/item exposing child work; `acknowledge`
identifies one receipt, not global source completion. Reasons, promise settlement,
exceptions, and reentrant execution are not encoded by these labels.

## Identity and data structures

Use stable native identities. An occurrence's address, path, and label are different
things; equal response paths do not imply equal tasks or stream items.

| Logical quantity | Concrete representation | Required behavior |
| --- | --- | --- |
| Task occurrence / delivery reference (`NodeRef`) | Object identity, arena handle, or request-local integer | Injective, stable identity through late callbacks |
| Group/task/source lookup | Hash map, dense slots, or fields on stable records | Same keyed membership and record contents |
| Parent and ordered children | Immutable parent reference plus vector | Acyclic coherent forest; sibling order |
| Group contributors | Insertion-ordered identity Set | Reciprocal owner membership and release/publication order |
| Task owners | Ordered immutable array | Unique contributor identities and direct-owner order |
| Pending/failure | Counter plus scoped error payloads | Failure distinct from pending and from zero counted errors |
| Staged value / held streams | Task-local optional value and vector | Single publication/release and producer barriers |
| Roots/readiness | Indexed insertion-ordered Sets | Same eligibility and release-order iteration |
| Stream items | Source Queue and local cursor | FIFO admission; no permanent accepted-index ledger |
| Failed identities | WeakSet or reachability-scoped membership | Prevent descendant revival while references remain live |
| Producer-owned work | Identity Set of unadopted resource-bearing work | Transfer only after full integration; dispose unaccepted suffixes |
| Cleanup deduplication | Temporary task/source identity Sets | One first-encounter operation block per identity |
| Publisher | Open-ID Map and monotone counter | Availability at mapping time; final record clearing |

Attach an opaque handle when execution allocates the native task/item record. A test/proof
bridge may associate it with a structural `Occurrence`, but the hot path need not repeatedly
hash full addresses. Different identity roles need not share a global integer space.
No NodeRef-to-rank indirection or ordered-store framework is required.

Rust/C++ ports can use arena handles with generation tags or reference-counted records.
Managed-language ports can use identity-based references/maps. A strong failed-identity
table is not automatically a WeakSet: retain failure knowledge while reachable work can
refer to it, then reclaim it at teardown or a justified safe cut. Enumeration or GC timing
must not decide scheduling.

An ordered Set may combine indexed membership with vector/linked order and tombstones.
Preserve newly appended ready entries. Sorted keys, settlement order, and global
registration-rank heaps are not substitutes for release order.

### Indexable operations and bounded traversals

Lean `find?`, `contains`, `filter`, and keyed record replacement usually denote map/slot
operations in a port. Expected constant-time identity lookup is a direction, not a proved
worst-case bound.

Retain the explicit traversals over relevant work:

- Register one newly exposed scope, installing parents before children and groups before tasks.
- Update one task's ordered owners or one completing group's contributor list.
- Follow relevant defer ancestry for health and dependencies.
- Remove one affected subtree or stop the reachable roots.
- Consume available FIFO items and their exposed child work.
- Examine a value's candidate wire owners or a producer's unadopted resource-bearing work.

Do not scan a full future Work catalogue, enumerate weak failure sets, or materialize every
stream index. Owner count and defer depth depend on query shape; they are not universally
bounded by the model.

Use explicit stacks. With an array-end stack, reverse-push children to preserve forward
task-before-child preorder. Do not translate Lean fuel into repeated collection-length
queries. Generated uniqueness and acyclicity justify exhausting the frontier.

Efficient mid-run native record reclamation is permitted if live observations and needed
registration/failure knowledge survive. It is not a new public garbage-collection algorithm.

## Registration, handoff, and last-owner disposal

`addTask` simultaneously installs live contributor memberships, updates pending counters,
and classifies the task. Keep only the active/rejected subsets as temporary integration
results. A failed-but-live dormant owner is registered, not rejected. No owner is tested a
second time merely to reconstruct the classification.

Complete registration precedes producer handoff. Install all released group/source roots
before disposal and callbacks. Dispose rejected tasks without evaluating them, then activate
newly active tasks and contributors of released roots. For stream items, finish this sequence
for each item before consuming the next one.

Producer ownership includes unfinished scopes, queued/unadmitted item work, and retained
resources after input sealing. Exhaustion or accounting deletion alone does not release
that inventory. Disposing an unaccepted outcome is producer-suffix cleanup, not adoption.

At failed removal, delete the owner record, inspect only its task memberships, and dispose
a task only after every contributor record is absent. Capture held streams before unlinking
the task. Failed-but-live co-owners still protect it. Direct failures and released cached
failures use this same path.

Keep one temporary identity-deduplication prefix across the dispatch's rejection and failure
sites. A native reentrant stop must preserve the current cleanup identities until unwind;
a finally block must not lose remaining targets after an earlier cleanup throws.

The failed input has already finished: retain its rejection for surviving dormant owners,
close active owners, and avoid aborting that rejected computation again. Successful
unlinking transfers released child work, which must survive later owner failure. Source
failure cancels its producer without aborting its stream Queue or cancelling already
admitted descendants.

The public model performs no prepared-state cloning, publication-key cleanup filtering, or
second failure-subtree traversal. `registrationSnapshot` and frontier views exist only in
proof modules; do not allocate them in production.

### Resource observations are evidence, not implementation ledgers

The proof-side ownership model distinguishes acquisition, producer ownership, queue ownership,
requested cleanup, and release. Normal task settlement, successful source exhaustion, and
asynchronous cleanup settlement are different observations.

Generated all-handler proofs retain task/source representation or license real cleanup.
Task coverage includes unfinished tasks without computation nodes; completed buffered values
are not pending computation leases. Initial structural identities and inter-input observations
compose through arbitrary-width FIFO prefixes and actual reader closure.

Native audits still need a complete acquisition inventory and same-run mapping of callbacks,
handoffs, completion, cleanup, and outstanding effects. Independent legal histories are not
enough. `NativeAudit.AuditWitness.localSafety` is a checked composition of that evidence,
not a proof that JavaScript constructs it. No production resource ledger or ghost history
is required.

## Credits, acknowledgements, and batching

Source Queue capacity is a cooperative backpressure threshold, not a hard bound for a
producer ignoring push waits. Release an original slot's credit at dequeue, before yielding
the item, not at integration or acknowledgement. Slow wire delivery must not prevent refill.
Serialize raw pulls; early completion may overlap in ordered promise slots. An unsettled
head blocks overtaking.

`SourceCredits.ContinuousSourceCreditSafety_holds` bounds reserved original slots plus the
one preparation awaiting its push for a single cooperating producer and fixed positive
capacity. It derives the bound from wait discipline rather than assuming a backlog bound.
Acknowledgement does not release credits. This is a per-source item-window result, not a
byte bound, graph-Queue hard bound, or whole-request memory guarantee. Multiple producers,
dynamic capacities, synthetic terminal entries, and exceptional callbacks need separate
correspondence.

Acknowledge each input receipt exactly once in native `finally`, including partial or
exceptional consumption. Never deduplicate acknowledgements by source identity.
Consumption means completed item integration/handoff, not merely generator yield.
Unconsumed work is not adopted and still needs producer-suffix disposal.

For a fully consumed Lean receipt, acknowledgement follows all item handoffs/disposal and
precedes ready-drain cleanup. It is not necessarily the last handler effect.

`ReceiptPrefixAdmission` relates a partial receipt to its consumed FIFO prefix. Nonempty
prefixes retain matching/freshness/readiness; zero consumption supplies only finally
acknowledgement, not a fabricated empty ready item event. These facts do not make an arbitrary
opaque schedule closed under trimming: the native source bridge must supply the consumed
prefix actually observed.

Keep source admission, callback buffering, graph batching, work-value grouping, response
mapping, and wire buffering separate. Amortize wire writes with available batches, without
per-wire-turn seals, artificial consumer grants, or an unbounded synchronous global drain.
Preserve failure/termination notices and publication licensing.

## Callback buffering and effective histories

An input may be validly enqueued before a different input retires its producer, then be
consumed stale later. Raw callback batches need not satisfy Lean's sequential
`inputsStarted` check. Do not weaken that contract or treat an earlier start as permission
to enqueue new work after cancellation.

Check eligibility at enqueue and recheck at each actual intermediate reduction state.
Streams require active source membership at enqueue, not just structural presence in Work
or adoption of a held source. Erasing a premature ignored item can shift the effective FIFO
cursor; raw work legality alone does not justify filtering.

`BufferedCallbacks` covers boundary buffers. `InterleavedCallbacks.CallbackHistory` covers
one FIFO enqueue/reduction run, including callbacks retained stale across batch boundaries.
The constructed effective history preserves shared queue state, ordered publications,
publisher replay, payloads, source cursors, and the unchanged effective source contract.
Consumed and pending receipts partition one unique enqueue inventory.

Semantic filtering does not erase native finally acknowledgement or disposal. Stale receipts
consumed inside an open batch still acknowledge. Closed-reader callbacks need separate host
finally/suffix evidence. The enqueue/reduction history is proof evidence, not another
production buffer or persistent receipt ledger.

## Reader closure and effect settlement

Map final notices before retiring publisher records. Remove individual closed IDs during
the run and clear the registry at final retirement; keep the ID counter monotone.

On abrupt close, cancel/abort and register pending effects before starting the once-only
response completion hook. `stopped` is distinct from semantic `terminated`.
A partial query does not become a complete history merely because its reader closes.

After closure, mapping must not allocate IDs, publish updates, or invoke finish again.
The guard does not release resources in late callbacks. Track pending pulls/completions,
rejected promises, iterator return, and cleanup exceptions until settlement.

`responseFinished` names hook invocation, not quiescence. The separate `CleanupTracker`
protocol allows registrations after response completion and permits async-finished only
after tracked effects settle. An empty tracked Set does not prove that all native effects
were registered or that no future registration can occur. The complete final no-late-effect
boundary remains a native obligation.

## Execution and library optimizations

These refinements are proof-only; public `Execution.getNewDeferMap` and execution algorithms
remain unchanged.

### Shared defer contexts and indexed planning

Share immutable ancestor suffixes through context overlays while preserving lookup,
fresh usage identity, and owner ancestry. Build only the plan-local ancestor index needed
for actual unfiltered field usages. Discover fresh parents once, stopping at a known node
only when the existing index is parent-closed.

Use half-open preorder intervals from a coherent acyclic forest. A node-only enter/close
stack assigns entry ordinals and reads the exit counter after descendants; do not precompute
subtree sizes or introduce runtime heights/ranks. Reverse-push roots/children for forward order.

Sort only the temporary selected-usage array. Delete dominated usages from the original
ordered owner set, retaining the first partition's original owner order, labels, and field
details. Sorting the stored representative changes semantics.

Canonical tuples or delimiter-separated exact decimal ordinals may index partitions.
They must separate identities across the whole plan, not just within each field.
Handle the empty tuple explicitly; delimiter-free concatenation, default intervals for unknown
owners, and crossing intervals do not justify the optimization. JavaScript Number precision
and decimal formatting require their own bridge; Lean natural arithmetic is not that bridge.

Use insertion-ordered field Maps only for unique response keys. The actual collector derives
that uniqueness; repeated raw keys do not license replacing append with overwriting writes.
Planner ordinals are neither queue ranks nor wire IDs.

`Semantics.PlannerExecution.rootExecutionExact_holds` composes constructed context, parent
discovery, ordered forest, stack intervals, stable filtering, serialized partition keys,
and field writes through complete recursive execution. It preserves the full completion
and final supply, with no caller-supplied forest or plan equality.

The observers prove structural counts, including two enter/close visits per node and one
parent read per fresh discovered node. These are not native Map/Array timing or allocation
bounds.

### Lazy computations

Construct deferred executors inside the computation function. Aborting before evaluation
then avoids executor acquisition. Early priming and result reads share the cache; they
need not have identical cancelled resolver-call prefixes.

`LazyComputation` proves at most one evaluation and abort callback invocation in its finite
non-reentrant call model. Clear the cleanup callback before invoking it, while preserving
the opaque cached result. A late pending callback may replace a rejected cache with a
fulfilled result: do not assume permanent cache poisoning. The closed reader still cannot
map that result. Its resources require separate disposal and settlement evidence.

### Successful empty sequential scopes

Reuse only active successful empty item scopes: no errors and all resource-bearing work
inventories empty. Errors, task-only work, empty stream boundaries, nonempty child work,
or overlapping early items end reuse. Keep independent sources/scopes separate.

Do not let mutable work/error arrays escape a reused scope. A guard-derived omitted work
field remains empty under later updates; a retained reference to an empty mutable array
does not. Exhaustion finishes idle state and cancellation aborts it; do not reset finished
state or pool active scopes globally.

`EmptyScopeReuse` preserves values, counted errors, occurrences, lowered child work, and
whole-reader batch results. Its allocation observer bounds scope allocations by item count;
a nonempty eligible sequence allocates exactly once. Native completion must establish the
awaited-field/no-late-callback barrier and preserve per-item context. These counts are not
runtime performance or all-allocation bounds.

## Errors and permitted short-circuiting

The ordinary and incremental public Lean executors eagerly complete sibling fields and
ordinary list items, aggregating errors even when a non-null failure bubbles. They do not
short-circuit sibling execution. Fatal initial plans and streamed-tail termination are
separate existing boundaries.

An implementation may cancel unfinished siblings after non-null failure. Error counts can
therefore differ from eager Lean execution: two fatal siblings can contribute two eager
errors but only one native error when the other was never executed. Exact queue comparisons
fed the same fixed Work, payloads, and batches still require identical counted errors.

Preserve already recorded errors separately from the delivery explanation. If a nullable
field fails and a later non-null field discards the same deferred object or stream item,
the failed completion reports the escaping cause. If the failure is caught inside data
that is delivered, that data patch retains all collected diagnostics. Ordinary execution
and the initial envelope also keep their collected counts. Work stores both projections
in `TaskOutcome`; recording inventories remain additive. Never clamp counts, manufacture
errors from skipped work, or count one originating error again during bubbling.

Follow GraphQL.js's task-computation replay: retain the rejected outcome with the task,
keep dormant owners' task memberships, and replay the rejection when an owner starts.
Group task registration order determines which cached rejection is replayed first; failure
settlement order does not. No per-group failure-origin occurrence is needed. Successful
results must not integrate work or decrement pending again when another owner starts.
The abstract contract checks causal provenance without imposing that bookkeeping on the
runtime. Detailed error identity and asynchronous refinement remain separate obligations.

The proof-only sequential policy covers general finite object/list/defer/stream recursion.
One compatible extending key map relates retained Work, changed counts, allocation gaps,
and causal cuts. Primitive-origin coverage explains exact gaps with positive reached cuts;
coupled recording histories preserve prior records and omit only unrecorded cancelled errors.
Local literal/atomic/conditional lemmas support these general roots; they are not additional
open modeling slices.

Skipped eager allocations can shift a surviving stream's numeric key and the final supply.
Compare through the constructed injective map, not literal key equality. Renaming alone
cannot equate different retained error payloads.

Native early/promise execution can report an error before its sibling settles, or complete
a sibling that pure sequential execution would skip. Rich error identity, actual starts,
recording/cancellation times, and asynchronous schedules must be related to the same native
run before claiming correspondence. A successful synchronous policy test is not an
asynchronous refinement theorem.

## Verification and remaining native boundary

```sh
lake build
lake lint
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeConformance
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeResourcePrefixes
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeRecursiveConstruction
lake build Tests.GraphQL.IncrementalDelivery.WorkQueueAlternativeRecording
node conformance/scripts/native-held-source-cleanup.mjs /absolute/path/to/graphql-incremental-delivery-js
```

The [proof map](alternative-implementation.md#proof-map) distinguishes closed abstract roots
from the checked native-audit composition. Native refinement must still construct:

- Stable object/container and parent/ready-order correspondence.
- Actual lazy/recursive execution outcomes, keys, primitive errors, and schedules.
- Complete acquisitions, producer handoffs/suffix disposal, and pending-effect inventories.
- Receipt/finally, reentrant/exceptional cleanup, and asynchronous settlement observations.
- One related queue, wire, ownership, receipt, and cleanup history for the same run.

Test shared/dormant failures, cached failures, unstarted rejection/close, successful transfer,
source failure, staged last-owner cleanup, partial receipts, late callbacks, preserved prior
errors, key shifts, monotone IDs, and empty-only scope reuse.

Measure concrete costs separately. Finite safety does not prove fairness, eventual cleanup,
infinite-source progress, identical wire chunks, complete native inventories, or a
request-wide memory bound.
