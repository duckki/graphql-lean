# Condition-Tree Summaries

`GraphQL.Theories.TreeSummary` provides one bottom-up analysis algebra and two traversal
backends with different precision and cost.

| Backend | Recursion domain | Condition treatment | Cost and precision |
| --- | --- | --- | --- |
| `TreeSummary.Syntactic` | `ConditionTree.Tree` | Evaluates node-local materializable type-condition products and factors Boolean alternatives by variable, then recurses into selected condition-tree subtrees | Faster, sound, but may lose correlations and global response-name grouping |
| `TreeSummary.ExactCases` | `ExactCases.CaseForest` | Keeps one correlated Boolean context for the whole selection hierarchy, then recurses over feasible type-region compositions of simultaneously active condition-tree subtrees | More expensive; supports structural least-bound proofs |

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
analysis to reject.
`mergedSelectionSet` follows GraphQL `CollectSubfields`. Schema and condition context
flow down, while algebra summaries flow up.

`Algebra.Lawful` supplies the proof-facing order, commutative-monoid laws for `combine`,
its monotonicity, and upper-bound laws for `join`. It does not change the executable
algebra.

`Algebra.Relation` packages constructor-local obligations between two algebras. Generic
theorems lift those obligations through list folds, exact-case recursion, lazy Boolean
decision composition, and decision collapse. A client proves the four local constructor
cases once rather than repeating a backend traversal proof.

The shared definitions and structural measures live in `TreeSummary.Core`, while
`GraphQL.Theories.TreeSummary` is the public aggregator. The annotated executor lives in
`GraphQL.Theories.AnnotatedExecution`; the abstract and concrete response folds and the
shared `CompatibilityCore` live in `TreeSummary.ResponseFold`. Each traversal
backend extends that contract with its own field transfer and owns its condition
processing.

## Variable-aware known-false pruning

The supplied-variable entry points of both backends extract through the request-aware
condition-tree path after applying operation defaults. Only known-inactive `@include`
and `@skip` selections are removed. Known-active, missing, and unavailable conditions
remain explicit, and every recursively summarized field selection set repeats the same
boundary-local pruning.

ExactCases keeps the request values used for pruning separate from the evolving values
used by its lazy Boolean decisions. A speculative assignment chosen while enumerating an
unknown-variable case therefore cannot prune later syntax as if it had been known in the
request. Syntactic carries the fixed summary environment through its recursive child
extractions.

There are two different correctness questions:

1. Fixed-request soundness asks whether execution for this request is related to the
   pruned summary. The generic framework proves this directly from extraction coverage
   and each analysis's existing compatibility obligations. It needs no new idempotence or
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
in several local groups even though execution collects them together. Its direct compatibility
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

`TreeSummary.ExactCases` uses `ExactCases.CaseForest`. Its `activeTrees` are condition-tree
subtrees simultaneously active in one partially resolved runtime case.

Every entry point uses the same compact Boolean context. A `BooleanEnvironment` records
each support variable as `missing`, `known`, or `unresolved`. The traversal collects the
recursive support once and streams missing-versus-present completion directly, without
materializing an exponential list of environments. `BooleanEnvironment.Completion` is
the proof-facing relation that characterizes those streamed choices.

The environment also carries immutable `fixedVariableValues`. Supplied-variable resolved
entry points initialize them from coerced request values; `assign` changes only the
case-evaluation values. This separates request knowledge from speculative case choices.

An unresolved truth value becomes a `BooleanDecision.split` only when the current
exact-case frontier first needs it. Decisions from sibling and child summaries are
combined pointwise in one canonical variable order, so repeated uses stay correlated
instead of forming false Cartesian products. `BooleanDecision.collapse` joins the
remaining alternatives after traversal. The context, including every completed
missing-versus-present choice, is inherited unchanged by sibling trees and nested field
selection sets.

Within one resolved path, each frontier enumerates only its unique nonempty
possible-type regions. Known and missing Boolean branches are filtered deterministically;
an unresolved value is split at that frontier by the lazy form. Selected branch bodies
are inserted into a case forest, and recursion continues until no condition
remains unresolved. Only then are fields from all active trees at that selection-set
boundary globally collected by response name and passed to the algebra.

The entry points are:

- `ExactCases.summarizeConditionTree`;
- `ExactCases.summarizeSelectionSet`;
- `ExactCases.summarizeOperation`;
- `ExactCases.summarizeOperationWithVariables`.

The condition-tree and selection-set functions take an explicit `BooleanEnvironment`.
The ordinary operation entry point supplies an empty environment, meaning every support
variable is initially unknown; the variable-aware operation entry point constructs a
total environment after applying operation defaults.

## Soundness boundaries

`ConcreteAlgebra` folds a completed `AnnotatedResponse`. Each backend has a local
compatibility contract relating its concrete and abstract transfer steps.
`foldChildSummaryForValue` replays only response shape: null and scalar values have no
child fields, an object contributes one child summary, and a list combines its element
shapes. The framework defines no numeric response-size or cost multiplicity; individual
analyses own those measures and prove the bridge they require.

The exact-case backend has generic execution soundness. The framework handles runtime
conditions, global response-name grouping, nested selections, null bubbling, lists, and
forgetting supplied Boolean values. Its public statements live under `ExactCases`:

- `OperationSoundWithFuel`;
- `OperationSound`;
- `AnalysisSound`.

Their witnesses are `ExactCases.operationSoundWithFuel`,
`ExactCases.operationSound`, and `ExactCases.analysisSound`. Forgetting concrete
operation-variable values is proved by evaluating one path of the lazy Boolean decision
tree and placing that path below its collapsed join. It therefore uses only
`Algebra.Lawful`.

The ExactCases backend also supports variable-indexed algebras without forgetting the
coerced request variables. `OperationWithVariablesSoundWithFuel`,
`OperationWithVariablesSound`, and `AnalysisWithVariablesSound` target
`summarizeOperationWithVariables`; their witnesses are
`ExactCases.operationWithVariablesSoundWithFuel`,
`ExactCases.operationWithVariablesSound`, and
`ExactCases.analysisWithVariablesSound`.
Because coercion fixes every relevant Boolean as known or missing, this entry point
calls `CaseForest.summarize` directly instead of scanning completion states or constructing
and collapsing a `BooleanDecision`.

Summarizing an operation through the explicit-context selection-set entry point has
matching contracts for fixed and variable-indexed algebras: `OperationContextSound` and
`OperationContextWithVariablesSound`, witnessed by
`ExactCases.operationContextSound` and
`ExactCases.operationContextWithVariablesSound`. Both contracts require the supplied
context to carry the coerced request values and to resolve the operation's Boolean
support. `BooleanEnvironment.ofCompleteValues` constructs that canonical total context;
`BooleanEnvironment.ofCompleteValues_resolvedFor` proves its resolution property.

The Syntactic backend has the same variable-indexed surface:
`OperationWithVariablesSoundWithFuel`, `OperationWithVariablesSound`, and
`AnalysisWithVariablesSound`, witnessed by
`Syntactic.operationWithVariablesSoundWithFuel`,
`Syntactic.operationWithVariablesSound`, and
`Syntactic.analysisWithVariablesSound`. Known values are threaded through nested field
summaries, not merely the root condition family.

`ExactCases.Compatible` is indexed by the coerced variable environment used by both
resolver-call annotations and its abstract algebra. This lets argument-sensitive
analyses state the local field law directly. The variable-indexed theorem needs no
monotonicity proof; a family of compatible records supplies one record for each request
environment.

The syntactic backend instead uses `Syntactic.Compatible`. Its `field_related` obligation
receives all local syntactic groups that represent one executed response field, together
with their recursively summarized children. An analysis proves that one concrete field
step is related to this local abstract result. The framework handles the condition cases,
coverage, recursion, and regrouping argument.

`Syntactic.operationSoundWithFuel`, `Syntactic.operationSound`, and
`Syntactic.analysisSound` are direct witnesses for the corresponding public syntactic
statements. They do not compare against the exact estimate, require no operation-specific
dominance premise, and use only `Algebra.Lawful`.

`executeQueryAnnotated_equal` separately proves that erasing field annotations gives
exactly `Execution.executeQuery`. The additional resolver-call metadata is constructed
by the small `resolvedFieldProvenance` helper and is an explicit trusted modeling
boundary; the erasure theorem does not specify that metadata independently.

## Optional optimality

Optimality is available only for `ExactCases` and is independent of ordinary
soundness. `ExactCases.CaseSemantics` describes concrete simultaneous composition and
the possible concrete result of one collected field group. A separate finite enumerator
first fixes the Boolean environment. Independent inductive relations then define the
recursively feasible tree cases by choosing exact type regions, child output types, and
field outcomes. Feasibility is therefore not defined by running the analyzer with a
special algebra.

At operation scope, Boolean completion is deliberately separate from tree semantics.
`BooleanEnvironment.Completion` relates the initial context to one globally consistent
completed context, while `operationContextOutcomes` says that the root selection set has
an outcome under one such context and one total truth assignment. The operation
statement therefore adds no second recursive summary semantics.

The proof module defines a proof-only collecting algebra whose joins are set union.
`conditionTreeContextOutcomes_iff_collecting` proves that this fold retains exactly the
inductively derivable lazy-context cases; the selection-set and operation results are
direct specializations. An analysis that opts in provides
`ExactCases.BestTransferLaws`: localized best-bound obligations for `empty`, `combine`,
`field`, and `join`.

The generic `BestBound` and `OutcomeSet` definitions live under
`TreeSummary.Optimality` in the exact-case optimality module. A `BestBound` says that
the computed estimate:

- bounds every recursively feasible concrete outcome;
- is below every other bound of those outcomes;
- has at least one feasible outcome.

The first item is structural-case soundness. The last item is needed for simultaneous
composition to preserve least bounds.

`BestBound` accepts the summary comparison relation directly. Public analysis
statements therefore describe only the attainable outcomes, their relation to an
estimate, and leastness; they do not expose a transfer-law proof package.
`BestTransferLaws` remains the framework's proof method for deriving those statements
from localized obligations.

Optimality is an opt-in layer: import
`GraphQL.Theories.TreeSummary.ExactCasesOptimality` for its public contracts and
`Proofs.GraphQL.Theories.TreeSummary.ExactCasesOptimality` for their witnesses.

`ExactCases.summarizeOperation_best` proves the central recursive theorem. An operation
derivation includes every nested choice made in child selection sets, rather than
describing only one isolated condition tree. Boolean choices are fixed once at the
selection-hierarchy entry and inherited by all children; each recursive condition tree
still chooses its local runtime-type cases and field outcomes.

Thus the framework does not claim that every analysis algebra is intrinsically
precise. It says that, once its four local transfer steps are best, exact-case traversal
does not introduce additional over-approximation: its result is the least bound of all
and only the recursively feasible cases represented by the traversal.

This recursive optimality layer is deliberately separate from executable GraphQL
semantics. In particular, completeness—realizing every structural case through
`executeQueryAnnotated`—depends on resolver behavior and is not part of the generic
optimality statement.

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
`MaxResponseSize.ExactCases.SoundWithFuel` and `MaxResponseSize.ExactCases.Sound`. Their
witnesses are `MaxResponseSize.ExactCases.soundWithFuel` and
`MaxResponseSize.ExactCases.sound`. The variable-aware statements are
`SoundWithVariablesWithFuel` and `SoundWithVariables`, with correspondingly named
lowercase witnesses.

The fast response-size statements are `MaxResponseSize.Syntactic.SoundWithFuel` and
`MaxResponseSize.Syntactic.Sound`. Their direct witnesses are
`MaxResponseSize.Syntactic.soundWithFuel` and `MaxResponseSize.Syntactic.sound`; the
Syntactic namespace also supplies the same variable-aware statement/witness pair.

`MaxResponseSize.ExactCases.caseSemantics` collects every multiplicity admitted by the
uniform list-size model. The public `SummaryOptimal` and
`SummaryOptimalWithVariables` propositions say that the corresponding estimate is the
least bound of those outcomes. Their witnesses are `summaryOptimal` and
`summaryOptimalWithVariables`. The private proof packages show that zero, addition, the
affine field rule, and `Nat.max` satisfy the framework's localized least-bound
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
`StaticCost.ExactCases.SoundWithVariables` and
`StaticCost.Syntactic.SoundWithVariables` propositions
quantify over all resolver environments, root values, and variable-condition
assignments and bound both actual cost components whenever the annotated response
respects the model's list-size estimates, assuming a well-formed schema and valid
operation. The Syntactic statement additionally assumes nonnegative type costs; the
ExactCases statement supports signed type weights without that premise. Erasing the
annotations produces the corresponding `Execution.executeQuery` response. The concrete
algebra has no join or condition operation.

`StaticCost.ExactCases.caseSemantics` uses the modeled local field-cost transfer as its
collecting semantics. The public `SummaryOptimalWithVariables` proposition says that
the synthesized summary is the pointwise least bound of those outcomes; its witness is
`StaticCost.ExactCases.summaryOptimalWithVariables`. Its private transfer-law proof
treats type cost and field cost independently, so a componentwise maximum need not be
realized by one case.

See [Static Cost Analysis](static-cost.md) for the model and cost rule.

## Module map

- `GraphQL/Theories/TreeSummary.lean`: public framework aggregator.
- `GraphQL/Theories/TreeSummary/Core.lean`: shared algebra, collected groups, and
  structural termination measures.
- `GraphQL/Theories/TreeSummary/Syntactic.lean`: fast structural traversal.
- `GraphQL/Theories/TreeSummary/ExactCases.lean`: feasible type regions,
  `ExactCases.CaseForest`, exact-case traversal, and its soundness contract.
- `GraphQL/Theories/AnnotatedExecution.lean`: annotated response syntax and execution,
  with an erasure statement connecting it to ordinary execution.
- `GraphQL/Theories/TreeSummary/ResponseFold.lean`: abstract and concrete
  algebras, response folding, and the compatibility core shared by both backends.
- `GraphQL/Theories/TreeSummary/ExactCasesOptimality.lean`: independent structural-case
  semantics and localized best-transfer contract.
- `GraphQL/Theories/TreeSummary/StaticCost.lean`: external cost/list-size model and IBM
  static/query-response cost analyses.
- `GraphQL/Theories/TreeSummary/MaxResponseSize.lean`: both response-size entry points.
- `GraphQL/Theories/SelectionConditions.lean`: the shared Boolean/type condition algebra
  and tree-free conditioned-field extraction.
- `GraphQL/Theories/ConditionTree.lean`: canonical tree construction plus the opt-in
  variable-aware known-false pruning and extraction entry points.
- `Proofs/GraphQL/Theories/ConditionTree/KnownFalsePruning.lean`: fixed-request extraction and
  runtime-group preservation witnesses.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCases/`: exact regions, the proof-only
  deterministic runtime-case interpreter, runtime alignment, variable refinement, and
  execution soundness.
- `Proofs/GraphQL/Theories/TreeSummary/ExactCasesOptimality.lean`: collecting
  characterization and recursive exact-case best-bound induction.
- `Proofs/GraphQL/Theories/TreeSummary/Algebra.lean`: reusable lawful-algebra lemmas.
- `Proofs/GraphQL/Theories/ConditionTree/Invariants.lean`: feasibility and uniqueness
  witnesses for extracted condition groups.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/RuntimePath.lean`: proof-only runtime
  paths and visited-path invariants.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/RuntimeGroups.lean`: runtime-group
  representation and coverage facts.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/Factorization.lean`: factorized-case
  upper-bound facts.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/Coverage.lean`: proof aggregator for
  concrete field coverage, runtime-selected summaries, and factorized-case coverage;
  the proofs are split across its `Coverage/` submodules.
- `Proofs/GraphQL/Theories/TreeSummary/Syntactic/Soundness.lean`: compatibility lifting
  and direct syntactic execution soundness.
- `Proofs/GraphQL/Theories/TreeSummary/AnnotationErasure.lean`: annotation erasure and proof
  facade.
- `Proofs/GraphQL/Theories/TreeSummary/StaticCost.lean`: local cost-algebra
  compatibility, optimality, and soundness witnesses.
- `Proofs/GraphQL/Theories/TreeSummary/MaxResponseSize.lean`: response-size
  compatibility, optimality, and soundness witnesses.
