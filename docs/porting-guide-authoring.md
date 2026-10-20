# Writing porting guides for formal models

A porting guide explains how to turn an executable formal model into a practical
implementation without accidentally changing its contract. It is neither a line-by-line
translation manual nor a catalogue of available data structures.

After reading it, an implementer should know what behavior to preserve, what machinery to
replace or omit, which optimizations are justified, and what still needs native evidence.
These guidelines focus on Lean models, but the distinctions apply to other formal models.

## Establish the contract before discussing implementation

Identify the specification, public model, algorithm being ported, and target implementation
boundary. Distinguish normative requirements from modeling choices and design references.
A reference runtime can explain an algorithm without becoming an additional specification.

State the comparison target explicitly. Depending on the port, it may require equal values,
counted errors, ordered publications, permitted histories, ownership transitions, or final
responses. Internal record equality, resolver-call order, wire chunk boundaries, timing, and
allocation counts are separate claims; do not silently include or exclude them.

Describe the input domain and assumptions: validation, finite work, generated identities,
source eligibility, uniqueness, acyclicity, and any scheduling restrictions. Separate
assumptions supplied by a host from invariants established by the algorithm. Do not turn
desired cleanup, successful merging, or response equivalence into an input assumption.

Explain each deliberate difference and the comparison it permits. For example, an eager
executor and an executor that cancels unfinished siblings may produce different error
counts. That requires an explicit execution-policy relationship; it does not excuse unequal
errors when both queues receive the same fixed work and inputs.

## Describe what to port

Port semantic decisions and the dependencies between them, not the incidental shape of
the Lean program.

| Model content | Porting guidance |
| --- | --- |
| Eligibility, failure, publication, and termination rules | Preserve the conditions and their observable consequences. |
| Ordered ownership, ancestry, and release relationships | Preserve identity, multiplicity, and relevant iteration order. |
| Registration, handoff, cancellation, and retirement | Preserve ownership boundaries and the points at which effects occur. |
| Explicit algorithmic optimizations | Describe the changed work performed and the invariants that justify it. |
| Response mapping and ID allocation | Preserve the required identity lifecycle and externally visible results. |

For each important transition, explain its purpose, inputs, affected state, output, and
ordering constraints. Use a compact symbol-to-operation table where names alone are not
enough. Map important helpers as well as top-level entry points, without cataloguing every
lemma or private function.

Explain a novel optimization as a change in algorithmic work. Good examples include:

- Classify newly registered tasks in one owner traversal and return only active/rejected
  subsets, rather than reconstructing those classifications later.
- Capture last-owner cleanup during failed-subtree removal, before unlinking held resources,
  rather than traversing the subtree again.
- Build an index only for the ancestry used by the current plan, instead of duplicating an
  entire request-wide catalogue.
- Split state into projections with different readers and lifetimes, or drop data after its
  last necessary observation.

Explain why each projection, duplicated subset, or discarded field is needed. A cache or
extra indirection should have an identified reader, maintenance rule, and measurable
purpose. A smaller runtime state must still represent all information needed by future work.

## Describe what not to port literally

Classify definitions by purpose, not merely by directory. Proof modules can contain useful
executable optimized algorithms as well as ghost state. Identify the optimized algorithm and
its connection to public behavior; do not copy the surrounding proof instrumentation.

Common things to replace or omit include:

- **Proof fuel and totalization.** Use a terminating native traversal where its invariant
  applies. State the valid-input assumption and the policy for malformed raw inputs; do not
  reproduce repeated collection-length calculations just to imitate proof fuel.
- **Ghost evidence.** Snapshots, historical matchings, resource ledgers, and an older state
  used for simulation are proof instruments unless a runtime consumer independently needs
  them. Their existence in a proof is not an allocation requirement.
- **Pure precomputed work.** A model may store complete finite outcomes to separate execution
  from observation order. Native lazy computations and iterators can replace that storage
  when they preserve the required work, identities, outcomes, and ownership relationships.
- **Persistent copies.** Immutable state updates do not require cloning the whole native
  queue. Conversely, mutation must preserve aliases and observations that the model keeps
  independent.
- **Literal list representations.** A list can describe ordering, identity lookup, a frontier,
  or an ownership relation. Those roles need different concrete representations.
- **Formal unbounded arithmetic.** Natural-number identities and counters do not establish
  machine-integer safety, floating-point precision, or serialization correctness.

Avoid introducing generic collection libraries into the formal model just to make lists
look efficient. Ordinary maps, sets, arrays, and arenas normally belong in representation
guidance. Model the explicit algorithmic change when it affects what is stored, traversed,
updated, or observed.

## Audit representations and scans

For each significant collection or scan, document:

- Its contents and semantic role: lookup, ordering, membership, multiplicity, or traversal.
- The identity used for lookup, and whether uniqueness is established or only assumed.
- Which order is observable, including the order of entries appended during traversal.
- Which transitions insert, update, invalidate, unlink, and reclaim entries.
- Whether work is global, scoped to newly exposed work, or restricted to an affected subset.
- What determines its size and lifetime, including late callbacks and outstanding effects.

A proposed index needs more than a key name. If records can repeat, explain whether lookup
returns the first match, all matches, or a unique representative. Show how the index stays
consistent through every relevant mutation. Preserve duplicate handling and ordered
iteration where the abstract algorithm depends on them.

Keep identity roles separate: object references, structural addresses, response paths,
planner ordinals, and wire IDs are not interchangeable. Explain when a structural identity
can be represented by a stable pointer or integer handle. Include allocation, uniqueness,
reuse, and lifetime rules; generation tags may be needed when callbacks outlive records.
Type aliases alone do not enforce separation between identity domains.

Audit scaling in the right dimensions. Query-shaped owner lists and ancestry may be small
in practice, but stream-item counts can be much larger. Do not justify a permanent item
ledger by saying that the query has few nodes. Separate query size, active work, buffered
items, and total work observed over the request.

Write cost claims narrowly. Expected hash lookup is not a worst-case bound; a proved visit
count is not a native timing bound; an item-capacity threshold is not a request-wide byte
bound. State the counted operation, size parameter, assumptions, and evidence.

## Explain lifecycle and asynchronous boundaries

For asynchronous or resource-owning ports, document who owns each resource before and after
registration, handoff, normal completion, rejection, cancellation, and cleanup settlement.
Distinguish requesting cleanup, invoking a completion hook, and reaching quiescence.

Identify the operations whose order matters. Examples include installing all ownership
before activation, capturing held resources before unlinking, and recording pending cleanup
before invoking a completion hook. A list of abstract effects may describe inline
observations, not commands that can safely be delayed until the handler returns.

Explain the following separately when they apply:

- Source backpressure and credit release.
- Callback enqueue eligibility and eligibility when the callback is actually consumed.
- Execution batching, publication grouping, response mapping, and wire buffering.
- Per-receipt acknowledgement and per-resource cleanup deduplication.
- Queue stop, semantic termination, reader closure, and asynchronous settlement.

State the scope of every once-only rule. An acknowledgement may belong to each receipt,
while cancellation deduplication belongs to a task/source identity within one dispatch.
Those scopes must not be conflated.

Cover partial consumption, late results, reentrancy, exceptions, and unaccepted work.
Filtering a stale callback out of the semantic history does not erase its native
acknowledgement or resource obligations. A finite non-reentrant proof does not settle
exceptional or asynchronous behavior absent from its model.

## Explain how to build and validate the port

Recommend a sequence that isolates semantic mistakes from performance changes:

1. **Read the actual definitions and theorem statements.** Record the current contract,
   assumptions, observation boundary, and relevant proof roots. An old passing build or a
   theorem name is not evidence for a subsequently changed contract.
2. **Map identities and transitions.** Choose native records and operations, identifying
   the logical state they represent. Keep a simple independent comparison path available.
3. **Port the core algorithm.** Preserve ordering and lifecycle boundaries before adding
   representation-specific optimizations.
4. **Optimize in separate slices.** For each change, state what work or storage it removes,
   the representation relation, and the invariant that must survive each transition.
5. **Compare related executions.** Exercise the actual implementation path, not only an
   independently legal synthetic trace. Relate queue, response, callback, and ownership
   observations to the same run.
6. **Measure concrete costs.** Benchmark representative and adversarial workloads; record
   input shape, concurrency, buffer policy, environment, and the metric being compared.

A projection or simulation can reuse existing proofs: establish initialization, show how
each new transition corresponds to the older model, and transfer the required observations.
The old state may exist only as ghost evidence. A local helper equivalence does not by
itself establish the complete recursive executor or asynchronous runtime refinement.

Recommend targeted regressions alongside differential testing and fuzzing. Include shared
ownership, failed-but-live owners, cached failures, rejected unstarted work, successful
transfer, partial batches, late callbacks, preserved prior errors, and boundary-empty work
where relevant. Preserve small counterexamples and reproducible replay commands. Mutation
sentinels help check that the harness detects the invariant violation it claims to test.

Tests establish evidence for exercised cases, not universal equivalence. Performance tests,
semantic tests, resource tests, and proof checks answer different questions.

## State proof coverage without overstating it

For every important optimization or safety claim, provide the definition, theorem or test
that supports it, its assumptions, and the remaining native obligation. Use these distinctions:

- **Representation guidance:** an implementation direction whose correspondence still needs
  to be established.
- **Proved model result:** a theorem about the stated formal definitions and input domain.
- **Conditional reduction:** a checked implication requiring witnesses or invariants that
  the actual implementation must still construct.
- **Regression evidence:** checked concrete examples, counterexamples, replays, or fuzz runs.
- **Native refinement:** a relationship established for the actual implementation and the
  same observed execution, within its stated scope.

Do not call a port verified merely because its abstract algorithm has a conformance proof.
In particular, a resource-safety theorem assuming complete acquisition evidence does not
prove that the runtime records every acquisition or registers every outstanding effect.
Existence of one completing schedule does not prove fairness or progress for every source.

Whenever public definitions or contracts change, revisit the coverage claims. Existing proof
files and historical axiom audits do not verify newly added obligations. Mark pending
migration explicitly until the relevant checks pass against the current definitions.

## Organize the resulting porting guide

Use the smallest structure that answers the implementation questions. A typical guide has:

1. **Scope and comparison target:** sources, preserved observations, assumptions, and deliberate
   differences.
2. **Model to native mapping:** important definitions, operations, and ownership locations.
3. **Representations and scaling:** identities, order, indexable scans, update rules, and lifetimes.
4. **Algorithm and lifecycle:** critical transitions, handoff, cancellation, buffering, and closure.
5. **Optimization guidance:** the work saved, required invariant, evidence, and native boundary.
6. **Validation and limits:** executable checks, adversarial cases, measurements, and open obligations.

Keep qualifications next to the claims they limit. Link to theorem maps and central build
instructions rather than duplicating them extensively. Give port-specific replay commands
and explain what they check. Use small comparison tables for repeated mappings and short
ordered descriptions where effect sequence matters.

Keep the guide a snapshot of the current design, not a development log. Use stable symbols
and paths for repositories whose history may be squashed; do not rely on private commit
hashes as durable correspondence. Pin a normative specification or upstream version when
its exact revision defines the target. Keep implementation-specific mappings in the porting
guide so that the formal model remains understandable on its own.

Before delivery, ask whether an implementer could preserve the contract, avoid copying ghost
machinery, justify each optimization, and identify the remaining proof and runtime work
without guessing. If not, add the missing decision or evidence, not more translation detail.
