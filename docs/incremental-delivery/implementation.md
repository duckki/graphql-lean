# Reference work-queue implementation

The executable reference machine follows GraphQL.js `v17.0.1` at
[`9617473`](https://github.com/graphql/graphql-js/tree/961747301cf70e59aead2d7a5121779a79a52877).
Its authoritative target is the incremental-delivery draft at
[`045e193`](https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec),
interpreted through the independent [work-queue contract](semantics.md).
This is a proved Lean reference implementation, not a formal refinement of JavaScript
source or its async runtime.

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
Implementation `Work` has GraphQL.js-shaped `groups`, `tasks`, and `streams` collections:

| Record | Contents |
| --- | --- |
| `Group` | Delivery node and immediate defer-parent key. |
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
| `taskFailure` | Task occurrence and its fixed bubbling-error count. |
| `streamItems` | Stream descriptor and a nonempty ordered batch of item occurrences, values, counted errors, and child Work. |
| `streamSuccess` | Exhaustion after all modeled items. |
| `streamFailure` | Stream descriptor and the error count of its next failing item. |

`ExecutionGroupValue.deliveryGroups` is implementation metadata, not a wire field.
`GraphEvent.MatchesWork` checks it against the task's actual contributors before publisher
selection. Abstract admission derives ownership directly from Work and ignores this
annotation, as does response mapping after owner selection. Contributor lists alone do
not identify task occurrences; the proof separately constructs publication provenance.

### State and transitions

`State` holds active roots, live group/task nodes, registration and cancellation keys,
started task/stream descriptors, initial notices, and a termination flag. `GroupNode`
stores child links, task memberships, pending count, and an optional accumulated failure.
`TaskNode` stores its task, an optional settled value, and produced child streams.
Finite lists implement keyed maps and ordered sets.

`State.initialize` integrates immediate work, prunes taskless group shells, starts the
remaining roots, and records initial notices. Starting work records eligibility for host
events; it does not run a promise or iterator.

| Transition | Behavior |
| --- | --- |
| `taskSuccess` | Check task-level healthy ownership, store the value, integrate children, then decrement each surviving contributor in one pass. Flush released nonfailed zero-pending groups, start released work, and drain ready outcomes. |
| `finishGroupSuccess` | Publish stored values once, remove shared memberships, close the group, and promote children/streams. |
| `taskFailure` | Close announced contributors with errors and accumulate errors on unannounced survivors; remove the settled task's memberships. |
| `drainReadyGroups` | Close released groups with a retained failure or no unsettled tasks, including further groups released by those closures. |
| `streamItems` | Integrate item children, activate roots, emit items and new notices, then drain ready groups after the carrier event. |
| `streamSuccess` / `streamFailure` | Close the active stream without retroactively cancelling work released by earlier published items. |
| `handleGraphEvents` | Process the batch in order and emit termination when both root collections are empty. A terminated state absorbs later calls. |

`pruneEmptyGroups` tests empty task membership **and** absence of a retained failure,
not merely a zero pending count: settled values may still await publication.
`removeGroup` cancels dependent descendants while retaining tasks with surviving owners.
Missing stale child links do not consume its live-node traversal budget.

Both task handlers check `taskHasHealthyOwner` once before processing the settlement.
`groupIsHealthy` requires a live record and no retained failure in its ancestor chain.
An absent ancestor is acceptable only when its key is not cancelled. Unannounced does
not mean unhealthy. A finite traversal bound rejects cyclic raw parent links;
execution-generated ancestry is acyclic.

A settlement with no healthy owner removes task bookkeeping but contributes no errors,
pending-count decrements, or child work. Retained notification records still preserve
earlier accepted outcomes until normal release or ancestor cancellation.

### Publisher and shared replay

`IncrementalPublisher` separates live notices from wire-ID allocation. Closed IDs remain
allocated, but only open contributors participate in `getBestIdAndSubPath`.
The publisher normalizes ownership; the spec mapper allocates IDs and constructs entries.
Normalization preserves values, errors, order, and lifecycle events; it cannot repair
invalid accounting.

All executable views share `State.runWithPublisher`, the queue/publisher processing loop:

| Entry point | Result |
| --- | --- |
| `State.runNormalized` | Residual queue and normalized work-event batches for supplied host inputs. |
| `createWorkQueueForSchedule work schedule` | Observable `Execution.WorkQueue`, constructed from one initialized state and the source's admitted input histories. |
| `initializeIncrementalResponse` | Initial response, concrete queue, and publisher. |
| `State.run` | Response updates plus residual queue/publisher, including updated mapper IDs. |
| `replayIncrementalResponse completed inputs` | Initial result, updates, and concrete termination flag. |
| `ResponseStreamCursor.initialize`, `run`, `step` | Optional resumable packaging of the same initialization and replay. |

A silent input produces no response update. `replayIncrementalResponse_eq_cursor` in
[CursorReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/CursorReplay.lean)
proves that the finite runner and cursor have identical initial results, updates, and
termination flags.

The queue adapter admits normalized outputs realized by some source-admitted input
prefix. This existential describes a language of observations, not a selected future.
Completion is determined by the queue's terminal flag, not the host source's `finished`
predicate. Spec execution independently supplies response batching.

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
The theorem
[`createWorkQueueForScheduleConforms_holds`](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/Conformance.lean)
proves all four independent contract clauses:

| Clause | Proof route |
| --- | --- |
| `Initialized` | Source freshness and empty-input admission; generated initialization supplies valid initial notices. |
| `PrefixClosed` | Every output-batch prefix has an admitted input-prefix realization. |
| `AccountsForWork` | One joint replay witness establishes atomic admission and terminal accounting. |
| `TerminationMatchesWork` | Concrete termination gives complete accounting; an abstract run's marker forces the concrete terminal flag. |

### Initialization

`ExecutedWork.nodeKeyCoherent` and `ExecutedWork.initializes` derive coherence and
initial-notice correctness. Neither is a caller premise or hidden in the host-source law.

[Initialization](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/Initialization.lean)
proves structural eligibility and key uniqueness.
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
ordered failure cuts. All seven obligations must hold for that same witness:

| Obligation | Checked construction |
| --- | --- |
| `BatchShape` | `batchShape_holds` relates canonical nonterminal atoms to the actual normalized batches. |
| `AnnouncedFailures` | `announcedFailures_exists` supplies prior contributor announcements for the accepted failure inventory. |
| `UncancelledFailures` | `mixed_failureCertificates` licenses mixed object/item failures against their ordered predecessors. |
| `PublicationAdmission` | `mixed_publicationCertificates` supplies payload, freshness, producer/item order, effective ownership, and carried notices. |
| `ControlAdmission` | `mixed_admissionCertificates` supplies group/stream controls and their notices on the same history. |
| `TaskAccounting` | `terminal_generatedTasks_accounted` uses producer-rank induction: available tasks publish or cancel; unavailable descendants inherit cancellation. |
| `NodeAccounting` | `terminal_nodes_of_tasks` combines task coverage with actual completion of announced keys. |

`replayWitnessExists_holds` constructs all seven jointly.
`conforms_of_replayWitnessExists` transports them to the source contract, using the
derived initialization law. No obligation remains an unproved premise of public
conformance. Independently choosing an existential witness for each leaf would not
establish the conjunction.

The proof uses concrete registration, retirement, buffered-value conservation, accepted
failure inventories, exact publisher registries, and notice tracking. These are derived
implementation invariants, not requirements imposed on the opaque host source.

Lean checks the obligation definitions, reduction theorems, and construction witnesses.
This documentation's table is maintained manually; there is no generated status registry.
[WorkSchedulerConformancePlan](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerConformancePlan.lean)
checks the public target, the joint construction, all seven leaves on an empty-stream
case, and the reverse termination bridge.

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

The source comparison is pinned to
[WorkQueue.ts](https://github.com/graphql/graphql-js/blob/961747301cf70e59aead2d7a5121779a79a52877/src/execution/incremental/WorkQueue.ts)
and [IncrementalPublisher.ts](https://github.com/graphql/graphql-js/blob/961747301cf70e59aead2d7a5121779a79a52877/src/execution/incremental/IncrementalPublisher.ts).
The draft remains authoritative.

| GraphQL.js construct | Lean counterpart |
| --- | --- |
| `Work`, `Task`, `Stream`, `Group` | Same record names; lowering adds structural occurrence identities and explicit parent metadata. |
| `GraphEvent`, `WorkQueueEvent` | Host inputs and queue outputs, including value/item batches and stream failure. |
| `GroupNode`, `TaskNode`, root/node collections | Same node names with explicit finite-list `State` fields. |
| `createWorkQueue` | `State.initialize` is the initialization core; `createWorkQueueForSchedule` additionally lowers work and exposes normalized outputs. |
| Integration, pruning, activation, and event handlers | Corresponding `maybeIntegrateWork`, `addGroups`, `pruneEmptyGroups`, `startNewWork`, task/stream handlers, and removal functions. |
| Publisher `buildResponse`, `_handleBatch`, `_getBestIdAndSubPath` | `buildResponse`, `handleBatch`, `getBestIdAndSubPath`, with spec-facing response constructors. |

Modeling adapters:

- Stable keys and structural occurrences replace object identity. Lists replace maps/sets.
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

The reference machine deliberately differs from pinned GraphQL.js where its queue emits
failure completion for an unannounced group. Lean retains that group's error until normal
release or ancestor cancellation. Released settled groups drain after their notice
carrier, so pending and completion can share one response update without an additional
network round trip.

Settled unpublished successful values are retained too. Zero pending count alone is not
permission to prune a group. Accepted failures accumulate on surviving latent owners;
later settlements with no healthy owner contribute nothing. These refinements preserve
notification accounting without reviving cancelled computation.

[WorkSchedulerRetainedOutcomes](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedOutcomes.lean),
[WorkSchedulerRetainedAnnouncement](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedAnnouncement.lean),
and [WorkSchedulerRetainedErrorCounts](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerRetainedErrorCounts.lean)
check release, cancellation, error accumulation, and independently admitted output.

### Cancelled-parent registration

`cancelledGroups` distinguishes an absent failed parent from a successfully retired one.
Without that information, late child registration can create an apparently healthy owner
under a failed parent, allowing a fully invalidated shared task to contribute another
error.
The pinned GraphQL.js source-level audit reproduces late child registration and
unannounced
completion; its wire symptom differs because it also closes latent failed groups
immediately. These are recorded audit findings, not a JavaScript refinement theorem.

[WorkSchedulerLateFailedParent](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerLateFailedParent.lean)
checks generated work with failures, a later successful shared producer, and delayed child
registration. The cancellation registry prevents the invalid late contribution.
[WorkSchedulerReactivation](../../Tests/GraphQL/IncrementalDelivery/WorkSchedulerReactivation.lean)
checks permanent refusal of cancelled keys, while
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
failure, R's two-error failure, X's failure, then Q's remaining success. C is introduced
after P has failed. X's contributors are C, D, and R; Y's are D and S.

The reference machine marks C cancelled at registration. By X's settlement, C is
cancelled, D has Y's retained failure, and R has closed with its own failure. X therefore
has no healthy supporter and adds no error. D reports only Y's one error when Q releases
it. The regression rejects a two-error D completion under every abstract matching and
failure-cut explanation; R's distinct two-error contribution makes that rejection
observable even in the count-only model.

The pinned GraphQL.js audit uses both direct queue replay and a validated query. It
registers C after P's failure and emits C's completion without a pending notice. It also
closes D immediately on Y's failure without announcing D, so its wire output is not the
two-error-D counterexample. This separates the current Lean cancellation requirement
from the concrete JavaScript symptom.

### Wire and finite-stream projections

Explicit null labels follow the draft spec, whereas the GraphQL.js implementation
omits them. Empty/exact-count stream boundaries have pending/completed lifecycles without
item patches; see [exhausted streams](README.md#exhausted-finite-stream-boundaries).
The model does not claim agreement on every JavaScript error, cancellation, or
interleaving.

## Verification and limits

Whole-project `lake build` and `lake lint` pass. Public conformance, the implementation
bridge, and all 12 query-correctness witnesses have audited dependencies limited to
`propext`, `Classical.choice`, and `Quot.sound`, with no added axioms or proof holes.

Focused checks:

```sh
lake build Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation \
  Tests.GraphQL.IncrementalDelivery.WorkQueueImplementation \
  Tests.GraphQL.IncrementalDelivery.ReferenceCorrectness \
  Tests.GraphQL.IncrementalDelivery.WorkQueueInitialization \
  Tests.GraphQL.IncrementalDelivery.PublicStatements
```

See [development](../development.md) for full build, lint, and formatting commands.

The proof is restricted to finite execution-generated work and valid host sources.
It does not establish completion from every admitted prefix, host fairness, eventual
resolver settlement, an infinite-run semantics, or refinement of the actual GraphQL.js
runtime. The [semantics guide](semantics.md#remaining-research-frontiers) separates these
open questions from the proved conformance result.
