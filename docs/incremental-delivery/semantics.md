# Incremental-delivery semantics: history-based work accounting

## Contract and scope

A **finite output-history contract** defines the work-queue semantics.
The shared `EventSource` supplies an opaque language of possible histories. A client
observes
one ordered stream; the model need not describe threads, ready queues, graph
mutation, or a scheduler algorithm.

The contract is defined in
[WorkQueueSemantics.lean](../../GraphQL/IncrementalDelivery/WorkQueueSemantics.lean).
It separates execution, mapping, and batching from structural occurrence relations
and direct constraints on output prefixes. No runtime task graph or mutable progress
machine is prescribed.

Reference implementation conformance derives valid initialization from nonempty executed
work. Callers supply executed-work and event-source premises; the
[initialization proof](implementation.md#initialization) discharges notice validity.

This is a proposed completion of the pinned draft's unspecified queue interface,
not a claim that the GraphQL specification already states these invariants.
For the execution/spec cross-reference, see [execution guide](README.md).

The [checked research results](#checked-research-results) establish that failure uniqueness
follows from licensing and event provenance in explained histories. Terminal task
accounting remains necessary for permissive raw work; nonblocking is a separate
implementation property. Local commutation does not justify identifying ordered wire
responses.

## Our problem is not a FIFO queue

The input is finite `Work` whose pure resolver outcomes are already known.
The output is initial defer/stream notices followed by work-event batches.
Different observations may differ in publication order, chosen shared-result owner,
announcement frontier, value coalescing, and batch boundaries.

An implementation may restrict those alternatives. Conformance requires its
observed histories to belong to the contract; it does not require realizing
every contract history. A prefix may stall. A terminal history must account for
work. Neither says a real asynchronous computation eventually finishes.

Important distinctions:

- Work occurrences are not values: two equal list items are distinct occurrences.
- Defer IDs are not tasks: one shared object-result occurrence may have several owners.
- A failed task can affect cancellation before its failure notification is observed.
- A work-event batch and a response-event batch are different aggregation layers.
- Work keys are not wire IDs. Only response mapping allocates the latter.
- A raw queue's triggering group is not necessarily the effective publication owner.
  The contract applies after owner normalization; see the checked
  [shared-owner adapter](implementation.md#shared-publication-owners).

## Reference implementation

The executable GraphQL.js-inspired queue, publisher, smaller host-event contract,
and conformance proof are documented in the
[reference implementation guide](implementation.md).
The output-history contract described here remains independent of that machine.

## Research comparison

The sources below are primary papers or author-hosted publications. The
applicability assessments are our design judgments, not claims made by their authors.

| Approach | What the literature provides | Fit for this model |
| --- | --- | --- |
| I/O automata and trace inclusion | Separates internal executions from external traces; implementation correctness can be stated as inclusion of observable behaviors. | Closest conceptual fit. Specify permitted finite outputs directly; leave an implementation automaton optional. |
| TLA+ hiding and auxiliary variables | Internal variables and auxiliary proof information can explain refinement without becoming externally visible implementation requirements. | Useful guidance for existential occurrence/failure evidence and implementation-refinement proofs. No TLA dependency is needed. |
| Concurrent-object linearizability | Relates histories of invocations/responses to legal sequential object operations while preserving real-time precedence. | Useful for verifying a concrete concurrent queue underneath an implementation, but not the incremental-delivery contract itself. |
| Event structures | Represents occurrence identity, causality, and consistency/conflict independently of one total execution order. | Useful research direction for commuting independent work and minimizing equivalent schedules; more machinery than the current finite observer needs. |
| Interaction Trees / Choice Trees | Mechanized coinductive program models with interaction; Choice Trees adds explicit nondeterministic branching. | Appropriate if effectful resolvers, infinite behaviors, or interpreter refinement enter scope. Unnecessary for the current finite, already-computed outcomes. |

### Trace semantics: the best starting point

Lynch and Tuttle distinguish executions containing states/internal actions from
externally observable behaviors. Their framework permits nondeterministic
specifications and uses behavior inclusion for correctness. Their treatment
also separates fair behaviors from arbitrary finite prefixes; fair behavior
languages need not be prefix-closed.
[An Introduction to Input/Output Automata, Sections 2–3 (1989)](https://groups.csail.mit.edu/tds/papers/Lynch/CWI89.pdf).

We borrow the external-language perspective, not the entire I/O-automaton
framework. In particular, this Lean model does not add input-enabled automata,
fairness classes, or infinite traces. Our `PrefixClosed` condition concerns
finite admitted observations, not a fair-trace language.

### Hidden evidence is not implementation state

Lamport and Merz explain history, prophecy, and stuttering variables as
auxiliary devices for relating specifications without changing their observable
behaviors.
[Auxiliary Variables in TLA+ (2017)](https://arxiv.org/abs/1703.05121).

Our analogy is limited: an existential output-to-occurrence matching explains
an already observed finite history. It is not a prophecy variable selecting a
future, and no theorem from that paper automatically proves our normalization
correct. The reference conformance proof constructs such evidence from executable replay.

### Why not linearizability?

Herlihy and Wing define linearizability using invocation/response histories,
legal sequential behavior, and real-time precedence; FIFO queues are examples.
[Linearizability: A Correctness Condition for Concurrent Objects,
Sections 2–3 (1990)](https://www.cs.columbia.edu/~wing/publications/HerlihyWing90.pdf).

Our visible interface has neither queue-enqueue/dequeue calls nor concurrent
clients issuing those calls. The object we specify is a language of incremental
outputs with dependencies and cancellation. Imposing FIFO semantics would
choose an ordering we deliberately leave open. A concrete implementation could
use a linearizable queue, but would still need a separate proof connecting its
queue operations to our allowed output histories.

### Partial orders and richer branching

Event structures distinguish events from their labels and represent causal and
consistency information; configurations capture compatible causal histories.
[Winskel, Events, Causality and Symmetry](https://www.cl.cam.ac.uk/~gw104/VisionRevised.pdf).
More general models are needed when events have alternative compatible causes;
prime event structures do not directly support that form of disjunctive causality.
[Castellan, Clairambault, and Winskel, FSCD 2017](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.12).

Our owner alternatives and multiple producer occurrences make this a useful
comparison. For now, structural occurrence predicates plus explicit enabling
conditions express these alternatives without importing a general event-structure
algebra. The local independence proofs below identify reorderings that preserve task
accounting, while showing why exact wire observations need not agree.

ITrees model recursive interaction in Coq; CTrees add explicit internal
nondeterministic branching and support bisimulation/refinement reasoning.
[Interaction Trees (POPL 2020)](https://arxiv.org/abs/1906.00046),
[Choice Trees (POPL 2023)](https://arxiv.org/abs/2211.06863).

Those are implemented Coq frameworks, not Lean libraries used here. Adding an
interpreter, coinduction, and branching equivalences would currently formalize
more operational detail than our task requires.

## Admission rules

### 1. Public admission is about histories

`History` contains initial group/stream notices and observed work batches.

- `AdmissiblePrefix work history`: a possibly interrupted finite output history.
- `AdmissibleRun work history`: an accounted-for history ending in queue termination.
- `ValidHistory`: either of those cases.
- `AdmissibleNext work history batch`: the current history is valid and not
  terminal, the batch is nonempty, and appending it gives another valid history.

`AdmissibleNext` does not choose an output or assert availability. Several
different batches may satisfy it. It describes maximal contract possibilities;
an individual conforming source may allow fewer.

A complete event sequence is not chosen by initialization. Output evidence is
existentially quantified for each finite history. If an extension is admitted,
one coherent witness must explain the whole extended history; it is insufficient
to justify each output using mutually incompatible matches.

This is a trace abstraction, not a branching-time equivalence. Explanations for
two prefixes need not be the same hidden witness. Reference-machine conformance
establishes
trace inclusion. A stronger branching-time simulation or refinement of a real host runtime
is not claimed.

### 2. Structural identities replace allocated task IDs

`Occurrence.executionGroup address` identifies an execution-group task occurrence.
`Occurrence.item address index` identifies one stream item. Addresses describe
navigation through `Work`, not response paths or allocated queue keys.

`Address` and `Keys` are transparent abbreviations for `List Nat`, distinguishing
structural routes from delivery-node key lists in signatures, not enforcing new types.
`PublicationMatching` and `FailureCuts` similarly name the two witness types.

The module's banners provide an event-oriented reading order:

- **What work exists?** Structural provenance, owners, and producer dependencies.
- **Which failures justify cancellation?** Hidden failure evidence and its consequences.
- **What has been observed?** Publications, announcements, and open nodes.
- **Which events are permitted?** Readiness and notice rules feeding `EventAllowed`.
- **Admitted histories and batching.** Coherent event sequences and termination.

These are properties of work and its observations, not runtime workers. `EventAllowed`
is the central next-event rule; it constrains an observation without choosing one.
`CanAnnounce` names notice readiness. `DependencySatisfied` deliberately does not say
"succeeded": an absent node or an unannounced, accounted-for node can satisfy a dependency
without a success notification.

Group notice eligibility permits reporting a recorded contributing task failure after
normal producer/dependency release (`HasRecordedFailure`). The notice must be fresh.
Recording a failure does not grant permission to publish data, close successfully, or
satisfy a child's dependency: those operations retain their own premises. Publication
requires a healthy supporter even when a failed co-owner supplies the wire ID.
This is part of the proposed queue contract, not normative draft wording; see
[retained outcomes](implementation.md#retained-outcomes).

`locateWork` follows an address through the original work. Its `WorkLocation`
result contains the subwork, producer, and enclosing defer owners. This is a
static lookup view, not allocated tasks or scheduler state; invalid edges return
`none`. Sequential traversal uses `do` notation. `Located` is lookup equality.
`TaskAt` and `NodeAt` are ordinary predicates over those locations, supplying payloads,
contributing owners, producer occurrences, and dependencies. A node's dependencies are
defer ancestors for a group and enclosing defer owners for a stream; they are never
additional structural producers. There is no compiled `Graph`, `Task` record, task
allocator, or graph mutation. No synthetic stream-end task is necessary.

The structural section also contains the task/node projections and the single
`Reachable` inductive, which requires a successful producer chain. Reachability does
not depend on failures, observations, or the mutual cancellation rules.
`NodeAccounted` reuses `TaskHasOwners`; `DependencySatisfied` tests node absence through
`NodeHasProducer`. Owner selection and announcements still retain full node metadata.

All repeated metadata occurrences are inspected structurally. Raw work may contain
inconsistent descriptors; execution-generated key coherence is a derived invariant, not
a restriction on the raw syntax.

### 3. Successful publication is matched to work

An existential `matching : PublicationMatching` maps unbatched work-event indices to
producing work occurrences. Indices are zero-based, before value grouping or batching;
only value-publication indices are used, not control-event indices.

`CanPublish` requires freshness, no justified cancellation, prior publication
of the producer, and—in a stream—publication of the preceding item.
`OpenOwner` identifies a known contributing descriptor whose notice is still open.
`HealthyOpenOwner` additionally requires that contributor to be healthy.
`PublicationOwner` requires some such healthy supporter, but selects the effective wire
ID from **all** open contributors by longest path, with ties left nondeterministic.
These need not be the same contributor: a failed but still-open co-owner can identify a
different successful shared task supported by another healthy group. This is our
queue-contract interpretation,
not a new execution algorithm or a claim that the draft specifies internal health checks.
Matching freshness still prevents publishing one shared occurrence again under another
owner; `CanPublish` still excludes cancelled work. Correctness and implementation
conformance are proved with this distinction; see
[shared publication owners](implementation.md#shared-publication-owners).

`TaskAccounted` means one occurrence has been published or causally cancelled.
`NodeAccounted` requires this for every task contributing to a node. Neither predicate
means that the node's completion notice has already been emitted.

Announcements and closed keys are projections of outputs, not stored progress
fields. Each `EventAllowed` clause checks an atom against its preceding output
prefix. Carrier publication/closure is visible to notices released by that
same event, without making those notices visible before their own release.

### 4. Failures need a small causal explanation

Failure notification time is not failure occurrence time. Identifying them
would incorrectly prohibit cancellation that precedes notification.

The witness is an ordered finite list of `(cut, occurrence)` pairs.
Cut `i` means after initialization and before output `i`; equal cuts retain
the list's order. Every witness occurrence must:

- be a real failing task in `Work`;
- be reachable through successful producer outcomes;
- have at least one contributing owner announced by its settlement cut;
- occur no later than the end of the observed prefix;
- not already be cancelled by earlier witness settlements.

The previously announced owner need not remain open at settlement: a shared task may
have started through an owner that has since closed, while a latent owner keeps it alive.
The witness records accepted settlement order, not reporting order. Equal cuts preserve
list order. Later cancellation does not remove an accepted failure from `failedBefore`.
This distinction is represented by the licensing predicate, not by adding queue state,
host timestamps, or a second index to each failure. Actual completion events retain their
`Open` requirement and exact error totals through their own output boundary.

Cancellation and node failure are assessed at a reached failure cut using
the failures known through that cut and the value publications in `events.take cut`.
Published producers cannot be retroactively cancelled by a later failure of an
owner. `NodeFailed` and `TaskCancelled` retain a witness to the cut at which the
consequence arose, so appending outputs cannot undo an earlier cancellation.
`FailureWitness` checks a new failure against only earlier cuts. This is a
history relation, not a mutable queue state or a choice of future events.

Uniqueness is derived, not an admission premise: an earlier copy fails every contributing
owner and cancels the unpublished task. `FailureWitness.nodup` and
`failureWitness_iff_nodup_and` prove this when recorded failures have no successful
publication. `Explains.failures_nodup` derives that exclusion from event provenance,
so uniqueness holds for every explained history, without a generated-work premise.

`NodeFailed` and `TaskCancelled` expose cut-indexed observation predicates over a
small mutually inductive kernel in `Causality`. Structural premises are factored into
`TaskHasOwners`, `TaskHasProducer`, `TaskSucceeds`, `NodeHasDependencies`, and
`NodeHasProducer`. These merely project existing task/node descriptors; they do not
introduce additional invariants. The failure and cancellation rules remain mutually
inductive to enforce least causal closure, rather than permit circular explanations.
A producer cancels its unpublished child either by failing or by being cancelled itself;
there is no separate `ProducerUnavailable` judgment in the public model. For node failure,
every producer occurrence with that node key must be unpublished and either failed
or cancelled, and no root occurrence may exist. This preserves the handling of
repeated metadata in raw work. The Lean premise requires every nonfailed producer
to be cancelled; it is equivalent to the disjunction but avoids nesting a recursive
predicate under `Or` with a bound producer.

The least rules cannot manufacture failure by cyclic justification. `failedBefore`
exposes only failures available at a given cut. Error totals use those justified
occurrences, not arbitrary error numbers. Public query-correctness witnesses, finite
progress, auxiliary research results, and reference-queue conformance are checked against
the current contract. This does not establish refinement of the actual GraphQL.js runtime.

The release requirement retains the boundary exposed by two independent defer groups:
announcing only the successful group must not allow the other, never-announced failing
group to cancel silently and terminate with zero reported errors. Such a failure still
has no previously announced owner and cannot enter the failure witness.

A settled shared failure can remain accepted after the owner through which it started
has closed, while another owner is still latent. `Explains.failure_reported` and
`failure_le_total` require an owner still open at settlement; the zero-error correctness
proof instead uses the first accepted failure. A successful owner closure would imply
publication or cancellation of that task, and no earlier failure can explain a failed
closure. `Explains.first_failure_open_owner` and `AdmissibleRun.first_failure_accounting`
prove this argument without adding an admission premise.

This list is proof evidence, not a ready queue, mutable ledger, or implementation
requirement. Successful silent completions are abstracted away: publication
still follows observable producer dependencies, while a failing descendant must
have a successful producer chain. The cut indices are logical output positions,
not host time.

### 5. Completion and aggregation remain separate

`Terminal` accounts for every work occurrence by publication or justified
cancellation. Every structural node is either closed or unannounced and
failed/accounted for. Only then may a run append the termination event.

`ValueGrouping` and `WorkBatching` retain ordered coalescing and arbitrary
nonempty batches. Stream coalescing may regroup group/stream notices within
one batch; occurrence preservation is therefore a permutation result, not
necessarily equality of notice lists.

Response batching belongs to `Execution`, independently of work admission.
Neither admission nor terminal accounting mentions wire-ID allocation,
reconstruction success, response disjointness, or equality to basic execution.

## Verification and limitations

All 12 public query-correctness witnesses are checked against the current contract,
including finite progress (`queryOutcomeExists`). History-prefix preservation,
publication-matching changes, query realization, general mixed-work continuation,
research and specialized proofs, and broader regressions are covered by the passing
build, tests, and lint checks. Public-witness axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`, with no proof holes or added axioms.

Reference-queue conformance and the implementation-to-query bridge are also proved.
Their detailed status is maintained in the
[implementation guide](implementation.md#work-queue-conformance).
The [incremental-delivery proof map](README.md#proof-status-and-verification)
lists the public witnesses. These finite results do not imply host fairness, completion
of every admitted prefix, or refinement of the actual GraphQL.js implementation.

### Independent accounting and actual observations

`EventAllowed.accounting`, `Explains.noticeFacts`, and `Explains.allCompleted` derive
notice freshness, open references, and terminal closure from output admission.
`AdmissiblePrefix.uniqueKeys`, `AdmissibleRun.liveKeys`, and
`keysCompleteExactlyOnce` retain those facts across every permitted grouping.
Causal failure proofs require actual bounded failure evidence; generated-work error
positivity and error conservation rule out silently cancelled successful-looking runs.

`HistoryPrefixes` proves prefix closure, and `SpecificationSource` proves maximal-source
conformance for valid initial notices. `SourceRealization` and `QueryRealization`
connect every admitted history to actual response observations under arbitrary nonempty
response grouping, in both directions. No fixed future schedule is selected.

### Why the general progress proof needs supported notice coverage

A shared deferred publication can silently account for an unannounced co-owner and make
a child stream eligible while another owner remains open. Object events cannot carry
that new notice. Thus full `NoticesCovered` is not preserved after every publication,
even for legitimate work. A regression records this boundary and also proves that the
same fixture has a complete run.

`SupportedNoticesCovered` is a weaker, proof-only construction witness. Groups use
ordinary eligibility; a stream may wait until one defer dependency and its full ancestry
are satisfied. The public contract permits earlier announcement. This witness
chooses a useful family of histories for existence; it does not restrict admission.

The progress proof uses these checked facts:

- `Initialization` and `NoticeFrontiers` provide valid covering initial notices.
- `GroupAccounting` gives a published contributor to every healthy accounted defer
  group; it does not require cancellation of each task to fail all its owners.
- `MixedNoticeMetadata` supplies key roles and producer/ancestor support.
  `MixedNoticeCoverage` transports full dependencies backwards, and
  `MixedNoticeExtension` preserves coverage across non-carrier changes.
- `MixedProgressEvents` applies preservation to actual object publications, justified
  failures, and stream-success completions. Covering group-success and stream-item
  carriers supply the witness directly.
- `FiniteHistories` supplies a maximal finite history preserving that witness.
  `LeastKeyProgress` finds a ready task at a least healthy outstanding owner.
  In a maximal supported history, smaller accounted healthy keys can complete,
  and that least owner must already be announced. Its task could then take another
  permitted step, contradicting maximality.
- `CompletionExistence` finalizes the resulting task-accounted history.
  `MixedExistence.mixed_completeRun_exists` packages the terminal-run construction;
  `QueryOutcomeExistence` derives its metadata from execution and realizes the result.

Shared owners, arbitrary mixed nesting, and all fixed outcomes are allowed.
There is no validation, zero-error, supplied-history, or scheduler premise at query level.
Admission assumes no response-correctness conclusion or supported-coverage premise.

### Checked boundary

The work, mapper, and query regressions cover alternative owner/closure choices,
duplicate rejection, nested cancellation, counted failures, empty streams, shared
producers, and actual mixed defer/stream/defer/stream observations. Whole-project build
and lint pass with the current contract.

These results do **not** establish:

- completion of every admitted prefix or every conforming source;
- eventual resolver completion, host-future termination, or fairness;
- refinement of an actual host/runtime implementation.

Arbitrary notice choices can strand work. Successful silent completions and synthetic
stream-end tasks are abstracted away; no compiler optimization theorem is claimed.

## Checked research results

The following results characterize stronger progress, constraint minimality, failure
evidence, and local independence. They supplement the four `Conforms` premises without
turning response-correctness conclusions into admission assumptions.

### Nonblocking

Two optional public propositions distinguish possible completion from source policy:

- `History.CanFinish history work` means some terminal suffix preserves the history's
  initial notices and all existing work batches.
- `WorkQueue.Nonblocking result` means every admitted history has a finished
  extension in **that same source**. It is not enough that another source could finish.

The proof-only `viableSource` admits precisely prefixes with terminal extensions. It is
prefix closed and nonblocking; a viable initialization makes it conforming.
`nonblocking_viable` proves that any conforming nonblocking source admits only such
histories. Thus this is the largest nonblocking admissible language for fixed notices,
not an executable online policy, a selected future, or a requirement to realize every
allowed trace. `maximal_finished` shows that its unfinished histories cannot be maximal.
These results live in
[WorkQueueSemantics/Nonblocking](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueSemantics/Nonblocking.lean).

The negative result is unconditional for a concrete raw-work fixture: an empty root
stream and an independent one-item successful root stream. Announcing only the empty
stream is legal. Its completion cannot carry notices, and the omitted stream cannot
publish through an unannounced owner. No output matching, failure witness, or grouping
can complete this initialization. Therefore the maximal `specificationSource` can
conform without being nonblocking. The test proves absence of **any** complete run,
not merely rejection of one proposed continuation; see
[Tests/Nonblocking](../../Tests/GraphQL/IncrementalDelivery/Nonblocking.lean).

Neither definition promises that a host takes another step. Existential continuation
does not exclude infinite waiting or uncompleted resolver futures. Fairness and actual
eventual execution still require a host-level model outside these finite histories.

### Supported prefixes have terminal continuations

`mixed_supported_accounted_extension` extends an already explained prefix with
`SupportedNoticesCovered`.
`mixed_supported_continuation` then appends finalization and proves `History.CanFinish`,
preserving the supplied initial notices, events, and batch boundaries. Existing matching
and failure-cut evidence is existential: the theorem preserves observations, not the
identity of an implementation's private explanation.

The premises are the existing generated-work ancestry, key-role, continuity,
stream-owner-order, and path-coherence certificates, plus supported notice coverage at
the supplied prefix. `mixed_completeRun_exists` establishes covering initialization and
invokes this continuation theorem.
See [Correctness/MixedExistence](../../Proofs/GraphQL/IncrementalDelivery/Correctness/MixedExistence.lean).

Supported coverage is a sufficient construction property, not a necessary characterization
of viable prefixes. In particular, this theorem does not require every permitted stream
notice to appear as soon as it becomes eligible through silent co-owner accounting.
The regression starts after a shared-owner object publication with delayed child notices,
retains its supplied batches, and admits it in a conforming nonblocking viable source;
see [Tests/SupportedContinuation](../../Tests/GraphQL/IncrementalDelivery/SupportedContinuation.lean).

This provides a benchmark for a practical policy: do not strand notice carriers, retain
supported coverage, and allow the required continuation steps. Merely checking supported
coverage does not make an arbitrary restrictive source nonblocking; that source must
also admit the continuation. No concrete host scheduling policy is implemented here.

### Redundancy and necessary constraints

[WorkQueueSemantics/Minimality](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueSemantics/Minimality.lean)
proves two precise redundancy results:

| Clause | Checked result | Boundary |
| --- | --- | --- |
| Explicit failure-occurrence `Nodup` | `FailureWitness.nodup` and `failureWitness_iff_nodup_and` derive uniqueness when failures are unpublished; `Explains.failures_nodup` supplies it for explained histories. | Event provenance excludes successful publications of failing tasks; an earlier duplicate cancels the unpublished task. |
| Terminal task accounting | `terminal_iff_nodes` derives it from terminal node accounting in an explained history. | Requires every task to have an owner; raw ownerless tasks invalidate the implication. |

Only terminal task accounting is retained as a public clause. A concrete explained
ownerless-work history closes its only stream node while leaving an unpublished successful
task, proving that boundary is real. Failure uniqueness is available as a theorem whenever
a proof needs it; witness construction and extension need no separate uniqueness premise.

Further [minimality regressions](../../Tests/GraphQL/IncrementalDelivery/Minimality.lean)
isolate requirements rather than silently strengthening admission:

- Removing publication freshness permits repeating the same shared task through another
  valid owner while its other publication conditions still hold.
- Removing previous-item publication makes the second stream item ready before the first.
- Treating a recorded failure as sufficient, without any announcement requirement, permits
  causal cancellation of never-announced work without an output reporting its failure.
  The prior-announcement requirement excludes this case, as the checked regression shows.
- Failure and open-owner evidence alone allow an incorrect claimed error count;
  `NodeErrors` excludes reporting zero for a two-error contribution.

This is not an exhaustive independence audit of every clause. Removing `Nodup` evidence
does not eliminate the ordered failure cuts themselves. An equivalent purely output-based
causal account remains an open problem; no elimination of that witness is claimed.

### Local commutation does not imply equal wire histories

[WorkQueueSemantics/Independence](../../Proofs/GraphQL/IncrementalDelivery/WorkQueueSemantics/Independence.lean)
proves two conservative local diamonds:

- `Explains.objects_commute`: two distinct successful object tasks that are both ready
  and have permitted selected owners at the same prefix can publish in either order.
  Both extensions are explained and account for exactly the same task occurrences.
  The owners may coincide; new matching indices track the exchanged publications.
- `Explains.group_closures_commute`: two already enabled healthy group closures with
  different keys and no new notices can occur in either order. Completed-key membership
  agrees. Neither step introduces failures or announces nodes; other nodes may become
  eligible after the closures.

These theorems preserve the earlier prefix. They do not commute dependent producers,
successive items of one stream, failure release, or notice-bearing carriers. Nor do they
establish equivalence of all future histories under arbitrary batching.

The [independence regressions](../../Tests/GraphQL/IncrementalDelivery/Independence.lean)
exercise shared-owner object tasks and both closure orders. They also run the actual
response helpers: reversing two legal initial notices changes the ID of the same later
patch from `"0"` to `"1"`. Even without new notices, exchanging group closures reverses
the completion-entry order inside a coalesced response. Any future partial-order reduction
must therefore specify its observational quotient explicitly; exact wire equality is
too strong.

The build, tests, and lint checks pass. The principal research theorems use only Lean's
standard axioms
(`propext`, `Classical.choice`, and `Quot.sound` as needed), with no proof holes or added
axioms.

## Remaining research frontiers

- **Implementation progress:** establish a practical online notice policy and show that
  its own admitted language is nonblocking. Resolver termination and fairness require
  separate host-level assumptions; finite possible continuations do not supply them.
- **Further minimality:** audit the remaining clauses with explicit removal
  counterexamples or equivalence proofs. No redundancy among the four top-level source
  invariants has been established.
- **Failure abstraction:** determine whether an output-only causal relation can replace
  any ordered failure-cut evidence while preserving delayed failure notification.
- **Observational equivalence:** define which ID renamings, entry reorderings, and batch
  changes are acceptable before generalizing local commutation to trace reduction.
- **Implementation refinement:** connect an actual host/runtime implementation to the
  proved reference machine, and establish optional nonblocking for its source policy.
  Reference-machine conformance is proved; see the
  [proof structure](implementation.md#proof-structure).
