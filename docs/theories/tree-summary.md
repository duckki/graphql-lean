# Condition-Tree Summaries

`GraphQL.Theories.TreeSummary` provides one bottom-up analysis algebra and two traversal
backends with different precision and cost.

| Backend | Recursion domain | Condition treatment | Cost and precision |
| --- | --- | --- | --- |
| `TreeSummary.Syntactic` | `ConditionTree.Tree` | Evaluates node-local materializable type-condition products and factors Boolean alternatives by variable, then recurses into selected condition-tree subtrees | Faster, sound, but may lose correlations and global response-name grouping |
| `TreeSummary.ExactCases` | `ExactCases.CaseCursor` or `ExactCases.CaseForest` | Uses the cursor for variable-independent analysis and the batched forest for supplied variables | More expensive; globally groups each completed boundary and supports least-bound proofs |

An individual analysis supplies the same `Algebra` for either backend. The caller chooses
the traversal strategy.

## Shared algebra

An `Algebra` supplies one synthesized `Summary` type and four operations:

- `empty` summarizes no contribution;
- `field group child` handles one collected response-name group after its child summary;
- `combine left right` composes contributions that may occur together;
- `join left right` bounds alternatives.

`CollectedFieldGroup` records its inherited Boolean context, cumulative condition, and
one nonempty typed `ConditionTree.FieldGroup`. Its `fields` projection retains typed fields,
while `selections` reconstructs their directive-free GraphQL syntax. The response name
and field syntax therefore cannot disagree, and no inline-fragment case remains for an
analysis to reject. For a valid operation, field-merging validation also ensures that
occurrences applicable to the same runtime object have one selected field name and an
equivalent argument set. `representativeField` exposes the first occurrence for
analyses to inspect that shared identity and arguments once; the complete occurrence
list remains necessary to merge every child selection set. The estimators are total,
but their correctness contracts intentionally make no claim for invalid operations.
`toExecutableGroup` is the canonical conversion used by adequacy theorems that compare
a collected static group with runtime field collection.
`mergedSelectionSet` follows GraphQL `CollectSubfields`. Schema and condition context
flow down, while algebra summaries flow up.

`Algebra.Lawful` supplies the proof-facing order, commutative-monoid laws for `combine`,
its monotonicity, and upper-bound laws for `join`. It does not change the executable
algebra.

The proof-only `Algebra.Relation` in `Proofs.GraphQL.Theories.TreeSummary.Algebra`
packages constructor-local obligations between two algebras. Generic proof theorems lift
those obligations through list folds, exact-case recursion, lazy Boolean decisions, and
decision collapse. It is not part of the public definition surface.

The shared definitions and structural measures live in `TreeSummary.Core`, while
`GraphQL.Theories.TreeSummary` is the public aggregator. The annotated executor lives in
`GraphQL.Theories.AnnotatedExecution`; the abstract and concrete response folds and the
shared `SoundnessCore` live in `TreeSummary.Soundness`. Each traversal
backend extends that contract with its own field transfer and owns its condition
processing.

## Abstract-interpretation perspective

TreeSummary uses an abstract-interpretation-style organization:

- `OutcomeSet` is the predicate-valued collecting domain for feasible exact cases;
- `OutcomeSemantics` supplies concrete empty, simultaneous-composition, and field
  transfers;
- `Algebra` supplies the corresponding executable abstract transfers;
- `approximates` relates modeled outcomes to abstract summaries;
- `BestBound` states soundness and leastness relative to an analysis-defined order;
- `BestTransferLaws` requires every local abstract transfer to preserve best bounds.

Execution soundness and structural optimality remain separate claims. The former relates
an analysis directly to GraphQL execution; the latter says an ExactCases evaluator is the
best approximation of its relational outcome model. The interface does not require a
Galois connection.

## Variable-aware known-false pruning

The supplied-variable entry points of both backends extract through the request-aware
condition-tree path after applying operation defaults. Only known-inactive `@include`
and `@skip` selections are removed. Known-active, missing, and unavailable conditions
remain explicit, and every recursively summarized field selection set repeats the same
boundary-local pruning.

The ExactCases cursor contributes no pruning values, even after a speculative case
choice is recorded. The batched forest carries the coerced request values directly. A
lazy cursor split therefore cannot prune later syntax as if its choice had been supplied
by the request. Syntactic likewise carries its request pruning values through recursive
child extractions.

There are two different correctness questions:

1. Fixed-request soundness asks whether execution for this request is approximated by the
   pruned summary. The generic framework proves this directly from extraction coverage
   and each analysis's existing soundness obligations. It needs no new idempotence or
   absorption law: a removed subtree is proved inactive in that concrete request.
2. Result preservation asks whether the pruned summary equals the old
   variable-independent summary for every generic `Algebra`. That is intentionally not
   claimed. Such an equality can fail without stronger laws governing inactive
   alternatives, for example idempotent/least-upper-bound `join` behavior. IBM cost's
   componentwise `max` and zero empty summary satisfy the intended inactive-alternative
   behavior, but the core algebra contract remains more general.

The canonical unknown-variable entry points keep variable-independent extraction. This
makes the optimization explicit and prevents silently strengthening the contract of all
tree-summary algebras.

## Fast syntactic backend

`TreeSummary.Syntactic` traverses the extracted `ConditionTree.Tree` directly. It resolves
the immediate outgoing conditions of each node before recursively applying the same
procedure to selected branch bodies.

At one node:

1. current-node fields are collected by response name and summarized bottom-up;
2. each outgoing type branch is summarized once with the cumulative possible-type set
   already stored on its body; those sets partition the node scope into nonempty regions
   whose members select the same applicable branch summaries, and the distinct products
   are joined;
3. immediate Boolean branches are grouped by variable; same-value branches are
   combined, the false and true alternatives are joined, and independent variable
   results are combined;
4. the current-node fields, type-case family, and Boolean-case family are combined.

`TypeBranchSummary` pairs each feasible immediate type branch with its stored possible
types and its one widened summary. The type-case evaluator constructs only materializable
symbolic regions and evaluates one representative per region, omitting inactive
products. It does not compare analysis summaries: distinct activation products remain
distinct even if an algebra maps them to equal values, so no decidable equality or join
idempotence is required. `BooleanBranchSummary` pairs a literal with its widened summary;
`BooleanAlternatives` accumulates the simultaneous contributions for the false and true
values of one variable.

Type and Boolean branches are independent sibling families, so the traversal does not
form their Cartesian product at one node. Selected child trees inherit the accumulated
possible-type scope and Boolean environment. Known Boolean values prune falsified
branches; unknown immediate variables are represented by one local `join`, without
materializing assignments or a global decision tree.

The entry points are:

- `Syntactic.summarizeConditionTree`;
- `Syntactic.summarizeSelectionSet`;
- `Syntactic.summarizeOperation`;
- `Syntactic.summarizeOperationWithVariables`.

This backend intentionally does not compose every simultaneously active condition-tree
subtree before calling `field`. Consequently, fields with one response name can remain
in several local groups even though execution collects them together. Its direct soundness
contract exposes those groups together to the proof obligation, preserving soundness
without claiming exact-backend precision.

The backend synthesizes each immediate branch once under a widened context. Type cases
reuse those summaries in sparse products selected by symbolic runtime-type regions; Boolean
cases collect same-variable alternatives directly into a compact `combine`/`join`
circuit. This avoids assignment enumeration and repeated recursive branch analysis, at
the accepted cost of less precision than re-analyzing a branch under every refined case.
Its motivation, algebraic laws, and direct soundness proof are described in
[`tree-summary-factorization.md`](tree-summary-factorization.md).

## Exact-case backend

`TreeSummary.ExactCases` has one analysis surface backed by two independently verified
evaluators.

`summarizeOperation` uses an incremental branch-local `CaseCursor`. The cursor retains
the activated named fields and a preorder list of pending condition-tree branches.
Activated fields are stored as reversed chunks, so selecting a deeply nested branch does
not repeatedly copy the accumulated prefix; source order is materialized only when a
completed case is grouped.

An unresolved truth value becomes an `Internal.BooleanDecision.split` only when the
cursor reaches its literal. Decisions from sibling and child summaries are combined
pointwise in one canonical variable order, so repeated uses stay correlated. Disjoint
type alternatives use `BooleanDecision.join`, which keeps unrelated variables in
separate alternatives instead of forming a Cartesian product. `joinCases` and the final
bottom-up compaction evaluate a join eagerly only when both operands are leaves; this is
the same scheduled algebra operation and requires no extra algebra law.

`summarizeOperationWithVariables` uses the batched `CaseForest` compatibility-region
scheduler. At
each selection-set boundary it resolves the whole active frontier for every feasible
type region, resolves Boolean branches directly from the closed request environment,
records those assignments in inherited conditions, globally collects completed fields
by response name, and immediately folds the region summaries in their specified order.
It constructs no Boolean decision tree, performs no Boolean splitting, and retains no
persistent cursor. Missing, null, and non-Boolean directive inputs are determined as
false.

The entry points are:

- `ExactCases.summarizeOperation`;
- `ExactCases.summarizeOperationWithVariables`.

Condition-tree and selection-set functions are algorithm-specific helpers under
`CaseCursor` and `CaseForest`, not generic entry points. The variable-independent
operation summary begins with every Boolean unresolved. The variable-aware operation
summary applies operation defaults and passes the resulting request values to the
batched evaluator.

The model intentionally does not assert that the cursor and forest evaluators return
equal algebra terms. Their alternative schedules can associate `join` differently, and
`Algebra` does not require associativity, commutativity, idempotence, or distributivity.
Instead, each operation entry point is proved sound and optimal against its own
independent outcome relation.

## Soundness boundaries

`ConcreteAlgebra` folds a completed `AnnotatedResponse`. Each backend has a local
soundness contract relating its concrete and abstract transfer steps.
`foldChildSummaryForValue` replays only response shape: null and scalar values have no
child fields, an object contributes one child summary, and a list combines its element
shapes. The framework defines no numeric response-size or cost multiplicity; individual
analyses own those measures and prove the bridge they require.

The exact-case backend has generic execution soundness. The framework handles runtime
conditions, global response-name grouping, nested selections, null bubbling, lists, and
forgetting supplied Boolean values. Its public statements live under `ExactCases`:

- `AnalysisSound`;
- `AnalysisWithVariablesSound`.

These are per-operation contracts; their witnesses are `ExactCases.analysisSound` and
`ExactCases.analysisWithVariablesSound`.
Forgetting concrete operation-variable values is proved by evaluating one path of the
lazy Boolean decision tree and placing that path below its collapsed join. It uses
`Algebra.Lawful` together with the ExactCases-specific
`ExactCases.JoinFactoringLaws` needed by factored type alternatives.
`ExactCases.Soundness` is the narrower shared contract containing the core and field
obligations. `ExactCases.SoundnessWithFactoring` extends it with
`JoinFactoringLaws`; cursor execution theorems, including selection-set outcome
coverage, require the extended contract. The variable-aware batched operation theorem
uses `Soundness` directly.

The ExactCases backend also supports variable-indexed algebras without forgetting the
coerced request variables. `AnalysisWithVariablesSound` targets
`summarizeOperationWithVariables`; its witness is
`ExactCases.analysisWithVariablesSound`. The proof module retains the fuel-parameterized
`operationWithVariablesSoundWithFuel` theorem used by concrete analysis proofs, but its
statement is not part of the public definition module.
Because coercion gives a closed request environment, this entry point uses the batched
compatibility-region evaluator. It constructs no Boolean split or decision tree.
Missing, null, and non-Boolean values select false.

The Syntactic backend has the same public variable-indexed surface:
`AnalysisWithVariablesSound`, witnessed by
`Syntactic.analysisWithVariablesSound`. Its proof module retains
`operationWithVariablesSoundWithFuel` for concrete analysis proofs. Known values are
threaded through nested field summaries, not merely the root condition family.

`ExactCases.Soundness` is indexed by the coerced variable environment used by both
resolver-call annotations and its abstract algebra. This lets argument-sensitive
analyses state the local field law directly. The variable-indexed theorem needs no
monotonicity proof; a family of soundness witnesses supplies one record for each
request environment.

The syntactic backend instead uses `Syntactic.Soundness`. Its `field_sound` obligation
receives all local syntactic groups that represent one executed response field, together
with their recursively summarized children. An analysis proves that one concrete field
step is approximated by this local abstract result. The framework handles the condition
cases, coverage, recursion, and regrouping argument.

`Syntactic.analysisSound` is the direct witness for the public per-operation syntactic
statement. The proof module retains
`operationSoundWithFuel` for concrete analysis proofs. These theorems do not compare
against the exact estimate, require no operation-specific dominance premise, and use
only `Algebra.Lawful`.

`executeQueryAnnotated_equal` separately proves that erasing field annotations gives
exactly `Execution.executeQuery`. The additional resolver-call metadata is constructed
by the small `resolvedFieldProvenance` helper and is an explicit trusted modeling
boundary; the erasure theorem does not specify that metadata independently.

## Optional optimality

Optimality is available only for `ExactCases` and is separate from ordinary execution
soundness. `ExactCases.OutcomeSemantics` describes concrete simultaneous composition and
the possible concrete result of one collected field group. The cursor evaluator has an
independent mutually inductive `CaseCursor` outcome relation: a derivation chooses one
branch-local type region and follows one total Boolean assignment shared across sibling
groups and recursive children. The batched evaluator has a separate mutually inductive
`CaseForest` relation that chooses the frontier regions and resolves
Boolean branches from the closed environment.

The proof modules establish that each independent relation characterizes its executable
evaluator exactly. Only after those characterizations do they use private
predicate-valued algebras to transport local best-bound obligations to the analysis
algebra. No cross-mode summary-equivalence lemma is assumed or proved.

An analysis that opts in provides `ExactCases.BestTransferLaws`: localized best-bound
obligations for `empty`, `combine`, `field`, and `join`. This package is part of the
public optimality contract. The proof-only algebra relation transports those obligations
through the shared cursor traversal.

The generic `BestBound` and `OutcomeSet` definitions live under
`TreeSummary.Optimality` in the exact-case optimality module. A `BestBound` says that
the computed estimate:

- bounds every recursively feasible concrete outcome;
- is below every other bound of those outcomes;
- has at least one feasible outcome.

The first item is structural-case soundness. The last item is needed for simultaneous
composition to preserve least bounds.

`BestBound` accepts the summary comparison relation directly. `BestTransferLaws` is
indexed by that same relation and supplies the modeled-to-abstract `approximates`
relation. Execution coverage indexes it by the order already carried by soundness, so
the coverage theorem cannot silently compare two different abstract orders.

Optimality is an opt-in layer: import
`GraphQL.Theories.TreeSummary.ExactCasesOptimality` for its public contracts and
`Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality` for their witnesses.
The per-operation contracts are `ExactCases.AnalysisOptimal` and
`ExactCases.AnalysisWithVariablesOptimal`, witnessed by `ExactCases.analysisOptimal`
and `ExactCases.analysisWithVariablesOptimal`.

`ExactCases.summarizeOperation_best` and
`ExactCases.summarizeOperationWithVariables_best` are the corresponding generic
least-bound theorems. Their `BestBound.sound` projections provide structural soundness;
the execution-soundness theorems above connect each entry point to GraphQL execution.

Thus the framework does not claim that every analysis algebra is intrinsically
precise. It says that, once its four local transfer steps are best, exact-case traversal
does not introduce additional over-approximation: its result is the least bound of all
and only the recursively feasible cases represented by the traversal.

Five adequacy theorems make the shared cursor outcome model independently inspectable:

- `SelectionSetExecutionCovered` says every common abstract bound of the cursor outcomes
  also bounds every execution at the same complete request context;
- `SelectionSetBooleanSplitExact` shows that resolving one unknown Boolean gives the
  exhaustive union of its false and true cofactors;
- `SelectionSetResolvedAssignmentsExact` extends this to every Boolean variable in an
  extracted hierarchy without changing the request-pruning policy;
- `SelectionSetOutcomesInhabited` shows that enumeration cannot get stuck when each
  analysis-defined field transfer has an outcome;
- `SelectionSetRuntimeGroupsExact` specializes outcomes to field-group observation and
  relates every complete-request case to runtime `collectFields` in both directions.

- GraphQL execution is the external behavioral specification. `AnalysisSound` relates
  the implementation directly to it, while `SelectionSetExecutionCovered` shows that
  upper bounds of the relational outcome semantics are also sound for execution.
- `OutcomeSemantics` is the relational feasible-case specification. `AnalysisOptimal`
  proves that the implementation computes its least abstract bound. It deliberately
  describes the precision target of the static analysis rather than promising that
  every member is an independently realizable resolver execution.

Additional adequacy theorems make the second specification inspectable instead of
treating it as an opaque definition:

- `SelectionSetBooleanSplitExact` proves that resolving one unknown Boolean partitions
  the current outcome set into its false and true cofactors.
- `SelectionSetResolvedAssignmentsExact` lifts that result to all Boolean variables in
  the extracted selection hierarchy while preserving the extraction-pruning policy.
- `SelectionSetOutcomesInhabited` proves that case enumeration cannot get stuck when
  every analysis-defined field transfer admits an outcome.
- `SelectionSetRuntimeGroupsExact` specializes the relational outcome semantics to
  collected-field-group observation at a complete request context through
  `OutcomeSemantics.boundaryFieldGroups`. For every runtime object type in the root
  scope it produces a modeled case related by `CollectedGroupsMatchRuntimeGroups` to
  runtime `collectFields`; conversely, every modeled group case has a runtime object-type
  representative with the same response-name keys and flattened executable fields.

Together, Boolean exactness, inhabitance, runtime-group exactness, and execution
coverage explain the intended tightness boundary. Remaining over-approximation may
come from analysis-defined local field outcomes or from combining several runtime
objects in one response, but not from missing Boolean assignments, infeasible root type
regions, or the incremental case scheduler itself.

`SelectionSetExecutionCovered` requires a well-formed schema, a runtime object type,
selection validity, and field-merging validity. It uses an upper-closure statement
because one execution can combine several modeled cases, for example when a list
contains objects of different runtime types; it need not be represented by one outcome
member. The theorem does not claim that every modeled outcome is realizable by some
resolver. Structural optimality itself remains separate from executable GraphQL
semantics.

There is intentionally no general syntactic optimality statement: losing correlations
and splitting response-name groups can make its result strictly less precise.

## MaxResponseSize

`MaxResponseSize` uses one shared `Nat` algebra:

- each response name contributes `1 + listMultiplier * childSummary`;
- simultaneous contributions use addition;
- alternatives use `Nat.max`.

Each backend exposes an unknown-variable estimate and a supplied-variable refinement:

- `MaxResponseSize.Syntactic.estimateOperation`;
- `MaxResponseSize.Syntactic.estimateOperationWithVariables`;
- `MaxResponseSize.ExactCases.estimateOperation`;
- `MaxResponseSize.ExactCases.estimateOperationWithVariables`.

The exact-case response-size statements are
`MaxResponseSize.ExactCases.AnalysisSound` and
`AnalysisWithVariablesSound`. Their witnesses are
`MaxResponseSize.ExactCases.analysisSound` and
`analysisWithVariablesSound`. The fast Syntactic namespace exposes the same public
statement/witness pairs. Explicit-fuel contracts and their witnesses remain proof-local
implementation lemmas.

`MaxResponseSize.ExactCases.outcomeSemantics` collects every multiplicity admitted by the
uniform list-size model. The public `AnalysisOptimal` and
`AnalysisWithVariablesOptimal` propositions say that the corresponding estimate is the
least bound of those outcomes. Their witnesses are `analysisOptimal` and
`analysisWithVariablesOptimal`. The private proof packages show that zero, addition,
the affine field rule, and `Nat.max` satisfy the framework's localized least-bound
obligations. The proof is algebraically valid for every `Nat`; interpreting the
multiplicity model as realizable list cardinalities assumes a positive list-size bound.

## StaticCost example

`GraphQL.Theories.TreeSummary.StaticCost` is a static query-cost analysis
following the IBM GraphQL Cost Directives specification. Because `GraphQL.Schema`
does not represent custom directives, `StaticCost.CostModel` provides the
already-validated `@cost` weights, `@listSize` metadata, and a finite fallback for
otherwise-unbounded lists as a separate analysis input.

The result keeps signed IBM type cost and nonnegative field cost as separate
components. The field rule pays resolver-call cost once; estimated cardinality
multiplies returned type cost and both child components. It supports assumed sizes,
direct `Int` slicing arguments, schema and operation defaults, and direct
`sizedFields` transfer. Signed argument and input-field weights are clamped at the
complete field-call boundary; signed type weights remain visible to concrete response
costs.

The summary is a function from inherited resolved direct-child sizes to a nonnegative
static `Bound`; that
context is what lets a bottom-up fold apply a parent field's list size to its named
child list. Both `StaticCost.ExactCases` and `StaticCost.Syntactic` expose
`estimateOperationWithVariables`, which schema-coerces resolver arguments and prunes
Boolean directive branches fixed by the coerced request variables. There is no
variable-free StaticCost estimator: arbitrary later slicing integers and recursive input
values have no finite `Nat` upper bound.

The syntactic estimator always uses its fast factored traversal. Its soundness witness
assumes nonnegative schema type costs because duplicating signed return-type
contributions across factored field transfers is not sound in general. ExactCases has
no such restriction.

`actualCost` folds the annotated response, using its concrete resolver-call
definitions and completed values. The public
`StaticCost.ExactCases.AnalysisWithVariablesSound` and
`StaticCost.Syntactic.AnalysisWithVariablesSound` propositions
quantify over all resolver environments, root values, and variable-condition
assignments and bound both actual cost components whenever the annotated response
respects the model's list-size estimates, assuming a well-formed schema and valid
operation. The Syntactic statement additionally assumes nonnegative type costs; the
ExactCases statement supports signed type weights without that premise. Erasing the
annotations produces the corresponding `Execution.executeQuery` response. The concrete
algebra has no join or condition operation.

`StaticCost.ExactCases.outcomeSemantics` uses the modeled local field-cost transfer as its
outcome semantics. The public `AnalysisWithVariablesOptimal` proposition says that
the synthesized summary is the pointwise least bound of those outcomes; its witness is
`StaticCost.ExactCases.analysisWithVariablesOptimal`. Its private transfer-law proof
treats type cost and field cost independently, so a componentwise maximum need not be
realized by one case.

See [Static Cost Analysis](static-cost.md) for the model and cost rule.

## Module map

- `GraphQL/Theories/TreeSummary.lean`: public framework aggregator.
- `GraphQL/Theories/TreeSummary/Core.lean`: shared algebra, collected groups,
  possible-type-region partitions and their exactness contract, and structural
  termination measures.
- `GraphQL/Theories/TreeSummary/Syntactic.lean`: fast structural traversal.
- `GraphQL/Theories/TreeSummary/ExactCases.lean`: ExactCases cursor, case forest,
  measures, operation entry points, laws, and soundness
  contracts; Boolean-decision construction is qualified under `ExactCases.Internal`.
- `GraphQL/Theories/AnnotatedExecution.lean`: annotated response syntax and execution,
  with an erasure statement connecting it to ordinary execution.
- `GraphQL/Theories/TreeSummary/Soundness.lean`: abstract child-shape and concrete
  response folds, `ConcreteAlgebra`, and the soundness core shared by both backends.
- `GraphQL/Theories/TreeSummary/ExactCasesOptimality.lean`: independent cursor and
  case-forest outcome semantics plus public least-bound contracts.
- `GraphQL/Theories/TreeSummary/StaticCost.lean`: external cost/list-size model and IBM
  static/query-response cost analyses.
- `GraphQL/Theories/TreeSummary/MaxResponseSize.lean`: both response-size entry points.
- `GraphQL/Theories/SelectionConditions.lean`: the shared Boolean/type condition algebra
  and tree-free conditioned-field extraction.
- `GraphQL/Theories/ConditionTree.lean`: canonical tree construction plus the opt-in
  variable-aware known-false pruning and extraction entry points.
- `Proofs/GraphQL/Theories/ConditionTree/KnownFalsePruning.lean`: fixed-request extraction and
  runtime-group preservation witnesses.
- `Proofs/GraphQL/Theories/TreeSummary/PossibleTypeRegions.lean`: exactness of the
  possible-type-region partition shared by both traversal backends.
- `Proofs/GraphQL/Theories/TreeSummary/ExecutionValidity.lean`: recursive field-merging
  and argument-validity facts shared by both execution-soundness proofs.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCases/`: cursor and case-forest runtime-case
  interpreters, runtime alignment, variable refinement, execution soundness, and the
  case-forest optimality characterization.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCasesOptimality.lean`: proof aggregator for
  ExactCases relational outcome semantics, cursor characterization, and recursive
  exact-case best-bound induction.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCasesOptimality/OutcomeCharacterization.lean`:
  executable-cursor characterization and condition-tree best-bound induction.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCasesOptimality/BestBounds.lean`:
  selection-set and operation best bounds, execution coverage, and the public
  optimality witnesses.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCasesOptimality/OutcomeAdequacy.lean`:
  Boolean-case exactness, outcome inhabitance, and runtime-field-group adequacy.
- `Proofs/GraphQL/Theories/TreeSummary/Algebra.lean`: reusable lawful-algebra lemmas.
- `Proofs/GraphQL/Theories/ConditionTree/Invariants.lean`: feasibility and uniqueness
  facts for extracted conditions.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/RuntimePath.lean`: proof-only runtime
  paths and visited-path invariants.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/RuntimeGroups.lean`: runtime-group
  representation and coverage facts.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/Factorization.lean`: factorized-case
  upper-bound facts.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/Coverage.lean`: proof aggregator for
  concrete field coverage, runtime-selected summaries, and factorized-case coverage;
  the proofs are split across its `Coverage/` submodules.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/Soundness.lean`: soundness lifting
  and direct syntactic execution soundness.
- `Proofs/GraphQL/Theories/TreeSummary/AnnotationErasure.lean`: annotation erasure and proof
  facade.
- `Proofs/GraphQL/Theories/TreeSummary/StaticCost.lean`: local cost-algebra
  soundness, optimality, and analysis witnesses.
- `Proofs/GraphQL/Theories/TreeSummary/MaxResponseSize.lean`: response-size
  soundness, optimality, and analysis witnesses.
