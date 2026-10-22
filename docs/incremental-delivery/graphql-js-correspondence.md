# GraphQL.js definition correspondence

This map compares the finite Lean queue definitions with GraphQL.js
[PR #4870][pr] at [`299a279`][head]. The pinned [WorkQueue.ts][wq],
[IncrementalPublisher.ts][publisher], [Computation.ts][computation] and [Queue.ts][queue]
are the reference sources. The [draft specification][spec] remains authoritative;
this comparison does not prove refinement of the asynchronous JavaScript runtime.

The inventories below cover every explicitly declared `structure`, `inductive`, `abbrev`
and `def` in the two public queue modules. Generated projections/constructors and local
recursive `where` definitions are covered by their enclosing declaration. Names in the
reference table are relative to `ReferenceWorkQueue`, except the `EventSource` source contracts. Alternative names are relative to `AlternativeWorkQueue`.
Each Lean name links to its declaration.

Native operations retain their upstream names. Publisher methods omit JavaScript's
private `_` prefix. Explicit state, input-language checks, replay wrappers and proof
propositions keep descriptive Lean names where upstream has no matching function.
`drainReadyGroups` keeps its name because its root scan combines native
`maybeFinishGroup` and part of `startNewWork`; renaming it would suggest identical control
flow and parameters.

## Cached failure path

| Step | GraphQL.js | Lean |
| --- | --- | --- |
| Retain a task's rejected computation | [`Computation.result()`][result] rethrows its cached rejected reason. `TaskNode` itself has no rejection field. | `TaskNode.rejection` projects that cache; `cacheTaskFailures` and `GraphEvent.availableFailures` are finite availability adapters. |
| Inspect a released group | [`startGroup`][start-group] collects thrown reasons in a local `errors` array, in task Set order, before any private task starts. | `State.startGroup` uses a local `errors` list over ordered task membership. There is no group-level cause cache or `cachedFailures` function. |
| Remove the group | [`finishGroupFailure`][finish-failure] calls `removeGroup` immediately and returns `GroupFailureEvent`. | Same names and return-event role; selected task counts are summed. |
| Queue its notice | [`pushGraphEvent`][push] appends that event to the internal `Queue<GraphEvent>`. | `startGroup` returns enqueue effects; initialization and `dispatchGraphEvent` retain them in `State.groupFailureEvents`, a FIFO projection of internally pushed notices. |
| Forward the notice once | [`handleGraphEvents`][dispatch] forwards `GROUP_FAILURE` after earlier queued entries. Group removal has already happened. | Same handler name; consume observed `GraphEvent.groupFailure` at its FIFO position. It must match the current pending head; forwarding uses the stored descriptor and count. |
| Fail an already active owner | [`taskFailure`][task-failure] calls `finishGroupFailure(..., [error])`. | `State.taskFailure` reports only the triggering task's cause; it does not aggregate every currently cached rejection. |
| Build the response | [`_handleWorkQueueEvent`][publish-failure] maps `errors` to GraphQL errors in `completed`. | Owner normalization preserves the count; [`Execution.mapWorkEventBatch`](../../GraphQL/IncrementalDelivery/Execution.lean#L926) constructs the completed entry. |

A computation can already be rejected while its `TASK_FAILURE` notification is still
queued. The finite host input batch exposes such outcomes before FIFO dispatch. This
availability is an explicit abstraction: a Lean input batch is not claimed to equal a
native Queue generator batch. Input batching affects cache visibility. Promise callbacks,
microtasks, Queue backpressure and asynchronous cancellation remain outside the model.
The complete observed FIFO includes internal `GROUP_FAILURE` entries. Enqueue effects
are retained across batches and empty calls, then consumed in their actual observed
positions among task/stream outcomes. Pending notices prevent premature termination.
This projects native internal queue state without simulating external callback enqueue
timing, promise scheduling or backpressure. The source cannot forge or reorder internal
notices relative to one another, but realizability of its interleaving by native JavaScript
remains a separate refinement obligation.

For the PR's parent-before-failures case, both implementations produce:

```text
GROUP_VALUES P
GROUP_SUCCESS P (announces C)
GROUP_FAILURE R1 [first]
GROUP_FAILURE R2 [second]
GROUP_FAILURE C [first, second]
WORK_QUEUE_TERMINATION
```

C is removed while processing P, before either queued task-failure notice is consumed.
Its private task never starts. The definition-level
[GraphQLJsAlignment fixture][fixture] checks this ordering, immediate removal,
notice provenance, cross-path activation, completion order, shared-value wire ownership
and both queue variants.
These cases do not establish general runtime equivalence.

Initial activation uses the same cache distinction. GraphQL.js's `started.then` loop
starts roots in declaration order, so a synchronous rejection from an earlier root is
visible to a later root. `InitialStartup` supplies that observation independently of FIFO
notifications; `initialize` retains queued notices in state. Ordinary replay
preserves them across batches and empty calls; no special first-batch forwarding is used.
[InitialFailureStartup](../../Tests/GraphQL/IncrementalDelivery/Fixtures/InitialFailureStartup.lean)
checks `[1, 1, 2]` versus `[1, 1, 1]`, immediate removal and skipped private work.

`Execution.Work.declareGroups` retains ordered fresh group declarations separately from
task contributor references. Native [`IncrementalExecutor`][executor] executes immediate fields before
appending its new groups to `Work.groups`; the annotation follows that order. A numeric
creation-ref sort cannot recover this order across response paths. Lowering preserves
declaration encounter order. `State.addGroups.go` follows native `addGroup` recursion,
visiting a parent from the candidate set before installing its child. Its temporary
visited refs prevent duplicate visits; a candidate-count depth bound totalizes the finite
walk. `State.addGroup` supplies the record-update portion: require a live parent, install
the group, then attach its child link. Roots and child links follow installation order,
and pruning preserves that order when promoting empty shells. The annotation adds no
structural address edge or work count. Raw fixtures also declare registration candidates explicitly; contributor lists do not
create declarations.

The fixture's overlapping `user` selections declare C before its parent P and before
unrelated A roots. Visiting P first and pruning its empty shell gives initial labels
`[C, A, A]` and IDs `0, 1, 2`, matching the pinned JavaScript query. It also checks nested
child-link order, duplicate candidates, and refusal beneath absent live parents. The
permanent registry prevents repeated raw-fixture descriptors from reinstalling retired
groups; failed-parent refusal propagates only the corresponding cancellation marker.

Conformance, equivalence, resource, and query-bridge witnesses retain ordered declarations
and explicit internal dispatch. The implementation guides record their theorem domains and
verification status. These finite-model results do not establish refinement of the
JavaScript async runtime. The independent correctness contract is unchanged.

## Checked abstraction boundaries

Host batch boundaries remain part of the availability observation. Different partitions
of the same task/stream outcome sequence can expose different cached sums; internal notice
payloads can consequently differ too. Flattening checks payload/dependency order, but is
not a state replay bridge for this availability-sensitive domain.

[BatchReplay](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueImplementation/BatchReplay.lean)
retains those boundaries and includes internal dispatch in its queued-state induction.
The reference and alternative `GroupStartup` proof modules preserve the exact cached sum,
immediate removal, and skipped private work. General source conformance is proved within
the finite host abstraction; native scheduling and callback realizability remain separate
refinement obligations.

## Record fields and identities

| Lean representation | Upstream representation / boundary |
| --- | --- |
| `Group.node`, `Group.parent` | Group object identity and `parent`; path/label metadata is carried by the delivery node. |
| `Task.occurrence`, `Task.groups` | Task object identity and `groups`; computation evaluation is supplied by host outcomes. |
| `Stream.node` | Stream object identity; host events replace its Queue and producer. |
| `GroupNode.group` | Explicit copy of the `groupNodes` map key. |
| `GroupNode.childGroups`, `tasks`, `pending` | Same native fields; lists represent ordered arrays/Sets. |
| `TaskNode.task` | Explicit copy of the `taskNodes` map key. |
| `TaskNode.value`, `childStreams` | Same native node fields. |
| `TaskNode.rejection` | Rejected reason cached by `task.computation`, counted; not an upstream TaskNode field. |
| `State.rootGroups`, `rootStreams`, `groupNodes`, `taskNodes` | Same closure-local sets/maps, represented as finite lists. |
| `State.tasks`, `streams` | Lean descriptor catalogues for resolving structural/reference keys; native objects directly carry these descriptors. |
| `State.registeredGroups` | Permanent first-registration identities; repeated explicit descriptors do not reinstall records. Work separates ordered fresh declarations from contributors. |
| `State.cancelledGroups` | Lean history distinguishing failed retirement from successful shells during late registration; no corresponding native registry. |
| `State.initialGroups`, `initialStreams` | Returned fields of native `createWorkQueue`. |
| `State.groupFailureEvents` | FIFO projection of internally pushed `GroupFailureEvent` notices in native `Queue<GraphEvent>`. External callback pushes remain source supplied. |
| Local startup-notice results | Enqueue effects realized in the pending FIFO before the next observed dispatch; no per-group cause cache. |
| `State.terminated` | Finite stop boundary corresponding to `stopGraphEvents` and `WORK_QUEUE_TERMINATION`. |
| `IncrementalPublisher.ids`, `active` | `_ids`/`_nextId` split into permanent finite ID allocation and a separate open-contributor registry. Native `_ids.delete` combines retirement with registry removal. |
| Error counts (`Nat`) | Counted projection of collected diagnostics or selected rejection contributions; error objects, identity, paths and locations are outside scope. |

`NodeRef`, task occurrences, resolver object references and wire IDs have different roles.
Their finite numeric representations do not imply shared identities. Generated task
failures select one primitive cause; raw queue fixtures also admit larger boundary counts
to distinguish aggregation from selecting or repeating a single count.

## Reference queue inventory

Counterparts in this table refer to [WorkQueue.ts][wq] unless explicitly attributed to
[Computation.ts][computation] or [IncrementalPublisher.ts][publisher]. “Extracted” means
an explicit Lean function for native inline code, not an extra upstream function.


### Records and lowering

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`Group`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L53) | Native type | [`Group`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L9) | Delivery node plus an immediate parent reference; object identity becomes `NodeRef`. |
| [`Stream`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L59) | Native type | [`Stream`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L25) | Delivery descriptor; later host events replace its Queue and iterator. |
| [`Task`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L64) | Native type | [`Task`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L75) | Contributor groups and structural occurrence; a supplied outcome replaces `computation`. |
| [`Work`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L73) | Native type | [`Work`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L35) | Finite group, task and stream collections; empty lists replace absent collections. |
| [`Work.combine`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L80) | Lean adapter | No standalone upstream function | Concatenate lowered collections without choosing completion order. |
| [`Work.fromExecution`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L92) | Lean adapter | Input to [`maybeIntegrateWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L318) | Lower explicit ordered declarations independently of contributor references; undeclared contributors add no registration candidates. |
| [`TaskResult`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L424) | Native type | [`TaskResult`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L67) | Resolved group value and newly exposed work. |
| [`StreamItem`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L430) | Native type | [`StreamItem`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L59) | Resolved item and work; an additional occurrence identifies the item for source proofs. |
| [`GroupFailureEvent`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L139) | Native type | [`GroupFailureEvent`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L163) | Same `group` and `errors` roles; `Nat` projects an error list to its counted contributions. |
| [`InitialStartup`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L148) | Lean host observation | [`Computation.result()`][result] during initial root activation | Names synchronous rejection availability when tasks start; no consumed notification or persistent per-group cache. |
| [`GraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L440) | Native type | [`GraphEvent`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L134) | Project all six native dispatch variants, including internally queued group failures; source admission checks notice provenance at the pending FIFO head. |
| [`GraphEvent.identities`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1043) | Lean contract helper | No runtime counterpart | Extract task/item outcomes and group/stream closure identities for freshness. |
| [`GraphEvent.successes`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1050) | Lean contract helper | No runtime counterpart | Extract successful producer occurrences for dependency checks. |
| [`GroupNode`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L112) | Native type | [`GroupNode`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L199) | Ordered children, task membership and pending count; carries its map key explicitly. |
| [`TaskNode`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L123) | Native type + cache projection | [`TaskNode`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L205) and [`Computation`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/Computation.ts#L10) | Value and held child streams match the node; `rejection` projects the computation cache, not a native node field. |
| [`NewWork`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L131) | Native type | [`NewWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L41) | New root groups and streams; the group/stream descriptors replace generic native types. |
| [`State`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L156) | Extracted state | [`createWorkQueue`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L211) closure locals | Explicit maps/sets and initial results, plus Lean registration/identity adapters; no native `State` class. |

### Bookkeeping and transitions

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`State.groupNode?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L183) | Extracted lookup | [`groupNodes.get`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L279) | Look up the live group by stable reference. |
| [`State.task?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L187) | Lean adapter | Native task object reference | Recover a task descriptor from a structural occurrence. |
| [`State.taskNode?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L191) | Extracted lookup | [`taskNodes.get`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L299) | Look up a started task by occurrence. |
| [`State.stream?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L195) | Lean adapter | Native stream object reference | Recover a stream descriptor from a stable reference. |
| [`State.putGroupNode`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L199) | Extracted update | Mutations of `groupNodes` entries | Replace a finite keyed-list entry instead of mutating its fields. |
| [`State.putTaskNode`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L209) | Extracted update | Mutations of `taskNodes` entries | Replace a finite keyed-list entry instead of mutating its fields. |
| [`distinctDeliveryNodes`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L219) | Lean adapter | Ordered `Set` insertion | Deduplicate delivery descriptors by stable reference. |
| [`State.addGroup`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L234) | Extracted record update | [`addGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L349), after visiting its parent | Require a live parent, install the group and attach its child link. Permanent registration/failure history adapts repeated descriptors. |
| [`State.addGroups`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L269) | Native operation | [`addGroups`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L336) and recursive [`addGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L349) | Preserve candidate encounter order; `go` visits candidate parents before children with temporary visited refs and bounded depth. Return roots in installation order. |
| [`State.addTask`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L301) | Native operation | [`addTask`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L386) | Link contributors, increment pending and start eligible work; deduplicate repeated finite descriptors. |
| [`State.addStreams`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L325) | Native operation | [`addStreams`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L399) | Hold task-produced streams or return independently released roots. |
| [`State.maybeIntegrateWork`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L351) | Native operation | [`maybeIntegrateWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L318) | Integrate groups, tasks and streams in that order; explicit state replaces closure mutation. |
| [`State.pruneEmptyGroups`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L364) | Native operation | [`pruneEmptyGroups`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L413) | Prune groups with no task members and promote child frontiers in registration order; finite traversal fuel totalizes raw graphs. |
| [`State.cacheTaskFailures`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L396) | Lean availability adapter | [`Computation`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/Computation.ts#L10) cached rejection | Expose available outcomes on already started tasks before notification consumption; no upstream function of this name. |
| [`State.startTask`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L405) | Native operation | [`startTask`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L493) | Install a task node once; host events replace computation execution and callback installation. |
| [`State.removeTask`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L454) | Native operation | [`removeTask`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L764) | Unlink memberships and delete the task node; later notifications are ignored. |
| [`State.removeGroup`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L470) | Native operation | [`removeGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L748) | Remove affected groups and last-owned tasks; retain finite cancellation history for late registration. |
| [`State.finishGroupSuccess`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L497) | Native operation | [`finishGroupSuccess`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L697) | Publish held values, unlink tasks, prune children and return released work. |
| [`State.finishGroupFailure`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L533) | Native operation | [`finishGroupFailure`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L739) | Remove the group immediately and return a `GroupFailureEvent`; notification is a separate step. |
| [`State.startGroup`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L541) | Native operation | [`startGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L466) | Collect all cached rejections in a local errors list before private work; return one aggregate notice as an enqueue effect. |
| [`State.startStream`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L561) | Native operation | [`startStream`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L524) | Record the started stream; subsequent host events replace async Queue iteration. |
| [`State.startNewWork`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L568) | Native operation | [`startNewWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L432) | Activate new roots/sources; successful readiness scanning is factored into `drainReadyGroups`. |
| [`State.initialize`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L593) | Extracted initialization | [`createWorkQueue`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L211) initialization block | Integrate initial work, prune shells, start roots with optional synchronous rejection visibility and retain original notices and queued failures; no standalone upstream `initialize`. |
| [`State.taskFailure`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L607) | Native operation | [`taskFailure`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L643) | Cache the rejection and close active owners with the single triggering task cause; dormant memberships remain. |
| [`State.drainReadyGroups`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L629) | Lean control-flow adapter | [`maybeFinishGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L615) + [`startNewWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L432) | Scan zero-pending roots and recursively release successful groups; native code visits affected groups and extends its start list. |
| [`State.taskSuccess`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L658) | Native operation | [`taskSuccess`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L585) | Retain the result, integrate its child work once, settle owners and release ready groups. |
| [`State.streamItems`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L692) | Native operation | [`streamItems`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L660) | Integrate each item and activate its work before the next; finite exhaustion arrives in a separate host event. |
| [`State.streamSuccess`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L717) | Extracted switch case | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544): `STREAM_SUCCESS` | Close an active stream; the finite model does not peek ahead with `queue.isStopped()`. |
| [`State.streamFailure`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L728) | Extracted switch case | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544): `STREAM_FAILURE` | Close the stream with its selected boundary count; input validity supplies a live stream. |
| [`GraphEvent.availableFailures`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L741) | Lean availability adapter | [`Computation`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/Computation.ts#L10) cached rejection | Read available task-failure outcomes in a supplied finite batch; this is not a native Queue or Computation API. |
| [`State.handleGraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L768) | Extracted switch iteration | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544) switch | Dispatch one observed FIFO entry; return immediate outputs and newly generated notice enqueue effects separately. |
| [`State.acceptsGraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1167) | Lean source check | No runtime counterpart | Check live started task/stream membership or an internal notice matching the current pending FIFO head. |
| [`State.acceptsBatch`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1183) | Lean source check | No runtime counterpart | Task/stream callbacks retain eligibility from any earlier dispatch boundary of the same batch; internal notices must match the current head. Retain the full batch rejection snapshot. |
| [`State.handleGraphEvents`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L800) | Native operation | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544) | Fold observed FIFO entries, realize enqueue effects and forward internal notices only at their matching entries. Terminate when roots and pending notices are empty. |
| [`State.enqueueGroupFailures`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L585) | Extracted enqueue effect | [`pushGraphEvent`][push] | Append internally generated notices to the pending FIFO; external task/stream pushes remain source supplied. |
| [`State.groupFailure`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L751) | Extracted switch case + source check | [`handleGraphEvents`][dispatch]: `GROUP_FAILURE` | Require the next queued notice, remove it and forward its stored descriptor/count. |
| [`State.dispatchGraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L791) | Lean effect realization | Handler calls to [`pushGraphEvent`][push] | Realize one handler's enqueue effects before the next FIFO entry; no standalone native function. |

### Publisher and replay

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`IncrementalPublisher`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L826) | Native class projection | [`IncrementalPublisher`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L35) | Explicit ID state and open contributor registry; closed ID allocations are retained separately from liveness. |
| [`IncrementalPublisher.getBestIdAndSubPath`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L834) | Native private operation | [`_getBestIdAndSubPath`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L265) | Choose the deepest open contributor; the shared Execution mapper computes the ID and subpath. |
| [`IncrementalPublisher.handleWorkQueueEvent`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L847) | Native private operation, factored | [`_handleWorkQueueEvent`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L162) | Normalize publication owners and update open notices; shared Execution code builds wire entries. |
| [`IncrementalPublisher.normalizeBatch`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L899) | Lean factoring | [`_handleBatch`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L124) event loop | Thread owner normalization independently of wire mapping; no standalone upstream method. |
| [`IncrementalPublisher.handleBatch`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L911) | Native private operation | [`_handleBatch`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L124) | Normalize owners and compose with [`Execution.mapWorkEventBatch`](../../GraphQL/IncrementalDelivery/Execution.lean#L926) to build a response update. |
| [`State.runWithPublisher`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L926) | Lean replay adapter | Queue iteration + publisher event loop | Replay supplied finite batches and omit silent output batches. |
| [`State.runNormalized`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L940) | Lean replay adapter | Queue iteration + owner selection | Seed the live publisher registry and expose normalized batches; residual queue state retains pending notices. |
| [`createWorkQueueForSchedule`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L951) | Lean factory adapter | [`createWorkQueue`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L211) | Expose the spec WorkQueue using an explicit finite EventSource language, not a selected future or async iterator. |
| [`initializeIncrementalResponse`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L982) | Extracted publisher initialization | [`IncrementalPublisher.buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44) initial envelope | Compose concrete queue initialization with shared Execution response/ID construction. |
| [`State.run`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L994) | Lean replay adapter | Queue iteration + publisher batch mapping | Replay supplied FIFO batches and construct wire updates; residual queue state retains notices across empty calls. |

### Input language and source contracts

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`taskContext?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1008) | Lean source lookup | No runtime counterpart | Shared address/kind/index validation, yielding deferred contributors and produced child work. |
| [`taskChildWork?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1027) | Lean source lookup | No runtime counterpart | Find expected task-produced child work in the precomputed execution tree. |
| [`taskGroups?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1032) | Lean source lookup | No runtime counterpart | Find actual task contributors for event validation. |
| [`streamItemWork?`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1038) | Lean source lookup | No runtime counterpart | Find expected item-produced child work in the precomputed execution tree. |
| [`GraphEvent.itemsBefore`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1056) | Lean contract helper | No runtime counterpart | Extract preceding items of one stream for order and exhaustion checks. |
| [`GraphEvent.Fresh`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1064) | Lean source proposition | No runtime counterpart | Require unique task/item outcomes and group/stream closure identities. |
| [`GraphEvent.MatchesWork`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1073) | Lean source proposition | No runtime counterpart | Check fixed task/stream results, contributors and child work; an internal notice names an actual group with positive errors. |
| [`GraphEvent.Ready`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1103) | Lean source proposition | No runtime counterpart | Check producer dependencies and stream item order against the observed history. |
| [`InitialStartup.MatchesWork`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1141) | Lean source proposition | No runtime counterpart | Require distinct matching producer-free rejection observations without consuming their notifications. |
| [`ValidGraphEvents`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1150) | Lean source proposition | No runtime counterpart | Inductively combine matching, freshness and readiness; no additional runtime ledger. |
| [`inputsStarted`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1200) | Lean source check | No runtime counterpart | Replay start/stop requests without assuming output accounting or correctness. |
| [`EventSource.ValidFor`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1230) | Lean source proposition | No runtime counterpart | In namespace `EventSource`: fresh prefix-closed input language with matching, fresh, ready and started inputs, plus matching optional startup availability and first-batch inclusion of started rejections. |
| [`EventSource.NonblockingFor`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1257) | Lean optional source proposition | No runtime counterpart | In namespace `EventSource`: another input is admitted at every unfinished queue prefix; not host fairness. |

### Correctness and query observation

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`ExecutedWork`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1276) | Lean domain proposition | No runtime counterpart | Witness that finite work was produced by root execution. |
| [`createWorkQueueForScheduleConforms`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1292) | Lean correctness proposition | No runtime counterpart | State conformance for nonempty executed work and a valid startup-aware source; witnesses retain ordered declarations and internal dispatch. |
| [`ImplementationNonblocking`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1310) | Lean progress proposition | No runtime counterpart | State finite continuation under the explicit optional nonstalling source assumption. |
| [`replayIncrementalResponse`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1327) | Lean replay adapter | [`IncrementalPublisher.buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44) + subsequent iteration | Observe initial response, finite updates and concrete termination from a pure completion. |
| [`queryScheduleMatches`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1346) | Lean observation proposition | No runtime counterpart | Relate derived query work and admitted inputs to actual finite replay, with optional completeness. |
| [`ImplementationCorrect`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1369) | Lean correctness proposition | No runtime counterpart | State query-local conformance and actual-factory observation for the default empty-startup factory; witnessed by `implementationCorrect_holds`. |

### Optional cursor

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`ResponseStreamCursor`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1412) | Lean optional reader | No upstream cursor class | Package explicit queue/publisher state for online finite observation. |
| [`ResponseStreamCursor.initialize`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1417) | Lean cursor adapter | [`buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44-L89) initial envelope | Package the shared initialization result without another response algorithm. |
| [`ResponseStreamCursor.run`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1426) | Lean cursor adapter | Subsequent-results iteration | Package the shared finite replay result as a resumable cursor. |
| [`ResponseStreamCursor.step`](../../GraphQL/IncrementalDelivery/WorkQueueImplementation.lean#L1435) | Lean cursor adapter | One subsequent-results observation | Consume one supplied batch and suppress silent updates. |

## Alternative queue inventory

The alternative shares the reference's supplied FIFO inputs, batch-local startup notices,
cache visibility, publication normalization and response mapper. Its registration projections, inline
last-owner disposal, resource/receipt labels and reader guard are intentional alternative
algorithm choices. Matching an upstream purpose here does not claim identical source code
or a proved refinement of host cleanup behavior. See the
[alternative implementation guide](alternative-implementation.md) for those boundaries.


### Shared records and observations

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`Work`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L32) | Shared alias | Reference work lowering input | Alias `Execution.Work`; not a second work tree or the native flattened `Work` record. |
| [`ExecutionGroupValue`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L33) | Shared alias | Publisher `ExecutionGroupValue` | Reuse the same finite group value and diagnostic counts. |
| [`StreamItemValue`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L34) | Shared alias | Publisher `StreamItemValue` | Reuse the same finite stream item and diagnostic counts. |
| [`GraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L35) | Shared alias | [`GraphEvent`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L134) | Reuse all six reference variants, including observed internal failure controls. Startup returns notices as enqueue effects before their later dispatch. |
| [`State`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L38) | Alternative state | [`createWorkQueue`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L211) closure + reader stop boundary | Reference queue accounting plus an explicit stopped flag; no native State class. |
| [`CleanupTarget`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L54) | Alternative observation type | Task/stream identities used by cancellation | Temporary target vocabulary, not a persistent resource ledger or native type. |
| [`HostEffect`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L62) | Alternative observation type | Abort, receipt, handoff and completion boundaries | Finite ordered observations; reasons, exceptions and asynchronous cleanup are outside this type. |
| [`uniqueCleanupTargets`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L78) | Alternative helper | No standalone upstream function | Keep first-encounter target order during one transition. |

### Cancellation and teardown

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`State.cancelTask`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L92) | Native purpose, projected | [`cancelTask`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L290) | Collect task and held-stream targets instead of performing async abort calls. |
| [`cancelStream`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L101) | Native purpose, extended observation | [`cancelStream`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L307) | Observe source cancellation then Queue abort; native WorkQueue directly calls `stream.queue.abort`. |
| [`CleanupTarget.effects`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L105) | Alternative helper | No standalone upstream function | Expand temporary targets into ordered host-effect observations. |
| [`State.cancelGroup`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L113) | Native purpose, projected | [`cancelGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L274) | Traverse group membership and descendants to collect cleanup targets. |
| [`State.cleanupTargets`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L129) | Alternative helper | [`cancel`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L261) traversal | Extract the reachable-root teardown inventory; no standalone native function. |
| [`State.clearRecords`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L137) | Alternative teardown | Queue/reader retirement boundary | Erase finite accounting after stop; not a native WorkQueue function. |
| [`State.cancel`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L151) | Native purpose, projected | [`cancel`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L261) | Observe reachable cancellation, stop reading and clear finite records; erase promises and reasons. |

### Integration, removal and dispatch

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`TaskRegistration`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L166) | Alternative transition result | [`addTask`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L386) owner loop | Classify active, registered or rejected membership; no upstream enum. |
| [`IntegratedWork`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L176) | Alternative transition result | [`maybeIntegrateWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L318) | Return released roots plus temporary active/rejected task subsets; no upstream record. |
| [`IntegratedWork.newWork`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L184) | Alternative projection | [`NewWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L41) | Extract the shared roots result from the richer registration transition. |
| [`State.addTask`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L191) | Native purpose, alternative algorithm | [`addTask`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L386) | One owner loop installs memberships and returns registration classification without starting computations. |
| [`State.maybeIntegrateWork`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L224) | Native purpose, alternative algorithm | [`maybeIntegrateWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L318) | Complete group/task/stream integration and return activation/disposal projections. |
| [`State.disposeRejectedTasks`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L244) | Alternative phase | Absent-owner computation cleanup boundary | Observe rejected tasks after scope handoff; no standalone native function. |
| [`State.removeGroup`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L263) | Native purpose, alternative algorithm | [`removeGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L748) | Fuse shrinking subtree removal with last-owner cleanup before unlinking; native baseline does not record these effects. |
| [`State.finishGroupFailure`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L320) | Native operation, alternative removal | [`finishGroupFailure`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L739) | Use fused removal and return the shared `GroupFailureEvent` plus temporary cleanup targets. |
| [`State.startGroup`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L333) | Native operation, alternative removal | [`startGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L466) | Use the same local `errors` scan and immediate removal; return deferred notices alongside inline cleanup targets. |
| [`State.startNewWork`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L357) | Native purpose, alternative algorithm | [`startNewWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L432) | Complete activation after scope integration and rejected-task disposal; reuse cached-failure inspection. |
| [`State.initialize`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L385) | Alternative initialization | [`createWorkQueue`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L211) initialization block | Lower execution work and initialize registration/activation with the alternative transitions. |
| [`State.taskFailure`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L411) | Native purpose, alternative removal | [`taskFailure`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L643) | Retain one triggering cause, close active owners and capture inline cleanup once. |
| [`State.drainReadyGroups`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L438) | Lean control-flow adapter | [`maybeFinishGroup`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L615) + [`startNewWork`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L432) | Share successful zero-pending readiness while threading inline cleanup targets. |
| [`State.taskSuccess`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L480) | Native purpose, alternative algorithm | [`taskSuccess`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L585) | Integrate and hand off produced work before disposal/activation; preserve reference success events. |
| [`State.streamItems`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L535) | Native purpose, alternative algorithm | [`streamItems`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L660) | Preserve per-item integration/activation order and observe item handoff and receipt completion. |
| [`State.handleGraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L592) | Extracted dispatch + effects | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544) switch | Dispatch modified task/item handlers and share the reference stream-finalization cases. |
| [`GraphBatchResult`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L620) | Extracted accumulator + effects | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544) local accumulator | State, ordered workQueueEvents and inline effects; pending notices live in the shared queue rather than a batch-end accumulator. |
| [`GraphBatchResult.handleGraphEvent`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L627) | Alternative accumulator helper | One [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544) iteration | Append handler outputs and effects; realize returned notice enqueue effects before consuming the next FIFO entry. |
| [`State.handleGraphEvents`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L640) | Native purpose, projected | [`handleGraphEvents`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544) | Fold observed FIFO entries, retain undispatched notices and inline cleanup, and terminate only after pending notices are consumed. |

### Factory and response reader

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`State.runNormalized`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L668) | Lean replay adapter | Queue iteration + publisher owner selection | Reuse the reference publisher and omit silent output batches. |
| [`createWorkQueueForSchedule`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L687) | Lean factory adapter | [`createWorkQueue`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L211) | Expose normalized alternative outputs through the same explicit EventSource language. |
| [`createWorkQueueForScheduleConforms`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L714) | Lean correctness proposition | No runtime counterpart | State conformance under the shared reference source premises; witnessed by `createWorkQueueForScheduleConforms_holds`. |
| [`ResponseStreamCursor`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L726) | Alternative optional reader | [`buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44-L89) subsequent-results lifecycle | Queue, shared publisher and explicit once-only finish guard; no native cursor class. |
| [`ResponseStreamCursor.onWorkQueueFinished`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L735) | Native callback purpose, extended cleanup | [`buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44-L89) local `onWorkQueueFinished` | Mark finished and clear finite publisher records; actual callback calls are observed separately. |
| [`ResponseStreamCursor.buildResponse`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L748) | Native purpose, finite adapter | [`IncrementalPublisher.buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44) | Initialize queue and initial envelope; explicit cursor replaces an async result stream. |
| [`ResponseStreamCursor.close`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L763) | Alternative reader operation | `withConcurrentAbruptClose` / `onWorkQueueFinished` | Observe cancellation before once-only response completion; no standalone native `close` method here. |
| [`ResponseStreamCursor.handleBatch`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L776) | Native purpose, guarded adapter | [`_handleBatch`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L124) + finish callback | Guard the reader, map final notices before clearing IDs, and observe completion once. |
| [`ResponseStreamCursor.run`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L801) | Lean replay adapter | Subsequent-results iteration | Replay a supplied finite history and retain ordered effects. |
| [`replayIncrementalResponse`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L813) | Lean replay adapter | [`buildResponse`](https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L44-L89) + subsequent iteration | Observe the same pure completion independently of effect observations. |

### Model comparison

| Lean declaration | Relationship | Upstream counterpart | Projection / difference |
| --- | --- | --- | --- |
| [`State.fromReference`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L830) | Lean comparison projection | No runtime counterpart | Embed live reference accounting, or clear it after termination. |
| [`replayMatchesReference`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L837) | Lean equivalence proposition | No runtime counterpart | State exact finite queue replay equality under the shared source abstraction; witnessed by `replayMatchesReference_holds`. |
| [`createWorkQueueForScheduleMatchesReference`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L850) | Lean equivalence proposition | No runtime counterpart | State equality of observable queue factories under the same source premises. |
| [`responseReplayMatchesReference`](../../GraphQL/IncrementalDelivery/WorkQueueAlternativeImpl.lean#L859) | Lean equivalence proposition | No runtime counterpart | State equality of actual finite response replay, including the finish guard. |

## Reporting contract and spec-facing response mapping

The [execution/spec cross-reference](README.md#spec-origin-execution-definitions) covers
the shared execution algorithms; the [semantics guide](semantics.md) explains the independent
history contract. The following table maps the reporting definitions used by this change
outside the two queue modules. These are relational contracts or shared spec-facing mapping
helpers, not new GraphQL.js caches or ledgers.

| Lean definition | Spec / GraphQL.js relationship |
| --- | --- |
| [`Execution.Work`](../../GraphQL/IncrementalDelivery/Execution.lean#L387) (`declareGroups`) | Ordered fresh declarations correspond to native Work.groups insertion after immediate fields. Contributor references remain on tasks; the annotation adds no structural address edge or work count. |
| [`Work.withoutDeclarations`](../../GraphQL/IncrementalDelivery/Execution.lean#L407) | Structural-address projection ignores declaration annotations; no native runtime counterpart. |
| [`Execution.TaskOutcome`](../../GraphQL/IncrementalDelivery/Execution.lean#L367) / [`deliveryResult`](../../GraphQL/IncrementalDelivery/Execution.lean#L487) | Separate collected diagnostics from the selected rejection at a task boundary. Queue failures model thrown reasons; successful values preserve their diagnostics. |
| [`Execution.WorkQueueEvent`](../../GraphQL/IncrementalDelivery/Execution.lean#L913) | Same seven output variants as native `WorkQueueEvent`. The pinned draft's singular `GROUP_FAILURE.error` is generalized to the count of reported task causes; native `GroupFailureEvent.errors` is plural. |
| [`Execution.initializeIncrementalResponse`](../../GraphQL/IncrementalDelivery/Execution.lean#L1035) | Shared draft initial-envelope mapping; corresponds to the initial part of publisher `buildResponse` plus `_toPendingResults`. |
| [`Execution.ensureID`](../../GraphQL/IncrementalDelivery/Execution.lean#L863) / `getPendingEntry` | Draft ID/pending helpers; native publisher `_ensureId` / `_toPendingResults`. |
| [`Execution.mapWorkEventBatch`](../../GraphQL/IncrementalDelivery/Execution.lean#L926) | Shared draft response mapping, composed after native-style owner normalization. Group-failure counts pass through to completed entries, corresponding to `errors.map(ensureGraphQLError)`. |
| [`WorkQueueSemantics.FailureWitness`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L356) | Lean-only causal cancellation evidence. It retains the uncancelled-task premise; it is not a runtime failure log. |
| [`WorkQueueSemantics.FailureReportingWitness`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L375) | Lean-only reporting availability, including retained rejections that are causally redundant. Native cached computations motivate this distinction; no per-group cache is introduced. |
| [`WorkQueueSemantics.CausalFailuresAvailable`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L394) | Lean-only link requiring the same task occurrence to be available for reporting by its causal cut. Earlier cached availability can support later causal acceptance without duplicating reporting evidence. |
| [`WorkQueueSemantics.NodeFailureCause`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L547) | One supported selected boundary cause, retained for stream failure. |
| [`WorkQueueSemantics.NodeFailureCauses`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L562) | A nonempty distinct supported collection of task causes for group completion. The contract allows supported subsets; native/reference startup collects all cached causes and active-task failure uses one. |
| [`WorkQueueSemantics.EventAllowed`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L586) | Lean-only admission relation: open failed group plus supported reporting counts, or the existing single stream cause. It does not require a runtime graph or ledger. |
| [`WorkQueueSemantics.Explains`](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean#L640) | Lean-only history relation: every causal occurrence is available for reporting at an equal or earlier cut. Reporting evidence cannot authorize extra causal cancellation. |

The plural group report is a documented extension of the pinned draft mapper, not a
literal implementation of its singular-error pseudocode. The independent semantics
contract remains broader than the deterministic reference choice of all cached startup
rejections. Conformance, equivalence, query, and resource witnesses retain ordered
declarations and explicit internal-notice dispatch. Definition-level regressions cover the
reproduced native mismatches; native scheduling and source realizability remain separate
refinement obligations.

[pr]: https://github.com/graphql/graphql-js/pull/4870
[head]: https://github.com/graphql/graphql-js/tree/299a2792ccb325b04cc8a01adc3c9ee162393eea
[wq]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts
[publisher]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts
[computation]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/Computation.ts
[queue]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/Queue.ts
[executor]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalExecutor.ts#L472-L589
[spec]: https://github.com/graphql/graphql-spec/tree/045e19363c2b55f127960bd3b5e8072a15b29aec
[result]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/Computation.ts#L45-L54
[start-group]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L466-L490
[finish-failure]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L739-L746
[push]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L237-L241
[dispatch]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L544-L582
[publish-failure]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/IncrementalPublisher.ts#L208-L216
[fixture]: ../../Tests/GraphQL/IncrementalDelivery/Fixtures/GraphQLJsAlignment.lean
[task-failure]: https://github.com/graphql/graphql-js/blob/299a2792ccb325b04cc8a01adc3c9ee162393eea/src/execution/incremental/WorkQueue.ts#L643-L658
