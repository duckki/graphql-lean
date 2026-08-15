# Static Cost Analysis

`GraphQL.Theories.TreeSummary.StaticCost` implements Static Query Analysis and
Query Response Analysis for the
[IBM GraphQL Cost Directives specification](https://ibm.github.io/graphql-specs/cost-spec.html)
over this project's fragment-free query syntax. Custom schema directives remain outside
`GraphQL.Schema`; their already-validated meaning is supplied separately. Mutation,
subscription, custom executable directives, enforcement thresholds, and decimal cost
weights are outside the scoped analysis.

## Conformance profile

Within that scope, the reference `ExactCases` backend implements the IBM rules directly:

- object, scalar, and enum type weights contribute to type cost, while abstract output
  types use the maximum weight of their possible concrete object types;
- field cost is the field weight plus its supplied argument and recursive input-field
  costs, with only the complete field-call cost clamped at zero;
- omitted weights use IBM's scalar/enum zero and composite one defaults;
- multiple slicing arguments use their maximum, schema argument defaults are honored,
  slicing values take precedence over `assumedSize`, and `sizedFields` transfers the
  selected size to named direct-child lists;
- response-name collection charges one field call for one executed resolver, while
  aliases and repeated parent values contribute independently;
- static results are related to query-response results by the public upper-bound
  theorem, subject to the selected list sizes actually bounding the response.

This is a semantic specialization, not a complete implementation of the IBM SDL and
introspection extensions. In addition to the syntax exclusions above, weights are
integral rather than serialized decimal `Float` values or formulas, directive metadata
is supplied already validated, and `CostModel.defaultListSize` replaces IBM's otherwise
unbounded result for an unsized list. `requireOneSlicingArgument` remains validation
metadata because IBM permits, but does not require, rejecting a request that violates
it. For nested list wrappers, the soundness precondition conservatively requires the
selected size to bound the total non-null cost-bearing values; the IBM directive does
not provide independent bounds for nested list dimensions.

The response fold uses the maximum possible object weight for an abstract declared
return type. This is IBM's conservative Query Response Analysis mode for responses whose
concrete object type is not otherwise available. `AnnotatedResponse` retains a runtime
type for execution matching, but the StaticCost proof deliberately does not require that
extra provenance to calculate a sound response upper bound.

## External model

`StaticCost.CostModel` supplies the metadata normally extracted from schema `@cost`
and `@listSize` directives:

- `cost` maps a `CostCoordinate` to an optional signed integral weight;
- `listSize` maps a `FieldCoordinate` to optional `ListSize` metadata;
- `defaultListSize` supplies a finite bound when IBM's model would otherwise regard a
  list as unbounded.

Cost coordinates cover type definitions, field definitions, argument definitions, and
input-field definitions. The model is expected to come from an IBM-valid directive
schema: object, scalar, and enum definitions may supply type weights; concrete fields,
arguments, and input fields may supply their corresponding weights; interface and union
type costs are derived from their possible object types.

`ListSize` stores direct argument and field names after parsing its SDL strings:

```lean
{
  assumedSize := some 10
  slicingArguments := ["first"]
  sizedFields := ["edges"]
  requireOneSlicingArgument := true
}
```

IBM directive validation is not repeated by the cost fold. In particular,
`requireOneSlicingArgument` remains validation metadata. The total estimator takes the
maximum of all supplied `Int` slicing arguments, then tries `assumedSize`, and finally
uses `defaultListSize`. Schema argument defaults, operation variable defaults, and
supplied variable values participate in slicing. An undefined variable denotes an
omitted argument and therefore does not suppress a schema argument default; explicit
`null` remains present and does suppress that default. Negative integral sizes are
clamped to zero.

## Costs

IBM reports type cost and field cost separately. The analysis therefore returns:

```lean
structure Cost where
  typeCost : Int
  fieldCost : Nat
```

The specification represents `@cost` weights as decimal strings. This formalization
uses signed `Int` metadata. Type weights remain signed in concrete response costs;
negative argument and input-field adjustments remain signed until every complete
field-call cost is clamped into `Nat`.

Static query analysis separately synthesizes a nonnegative `Bound`. A resolver may
return null or error, contributing no returned type, so zero is always an alternative
to a negative returned-type contribution. Negative type weights are nevertheless not
clamped individually: they offset positive child type costs before that alternative is
taken.

For a field whose estimated response cardinality is `n`, the static rule is:

```text
typeCost  = max(0, n * (return-type cost + child typeCost))
fieldCost = field-call cost + n * child fieldCost
```

The field-call cost is the field-definition weight plus the costs of effective
arguments, clamped at zero. Effective arguments include supplied values and schema
argument defaults activated by omission or an undefined variable. A field returning an
object, interface, or union defaults to field cost 1; a field returning a scalar or enum
defaults to 0. An explicit field weight overrides that default.

Object type values default to type cost 1 and scalar or enum values default to 0. An
explicit type weight overrides that default. Interface and union returns use the maximum
weight of their possible concrete object types, as required by IBM's static analysis.
That maximum is signed: exclusively negative possible-object weights remain negative.
Null contributes no type instance, but its enclosing response field is still analyzed
and pays the field-call cost.

Input-object values recursively add input-field costs. Signed argument and input-field
weights allow a cheaper option to reduce its containing field-call cost, but the
complete field-call cost cannot be negative. An argument or input-field weight is paid
once; a list value may add nested input-field costs from its elements, but it does not
multiply the containing coordinate's own weight.

At the field-definition boundary, StaticCost applies the same schema-directed
`coerceArgumentValues` map that execution passes to resolvers. Request variables are
substituted, omitted or undefined values activate argument and nested input-field
defaults, and explicit `null` remains present and suppresses those defaults. Weighted
arguments and list sizing then fold the resulting finite values structurally, including
through lists and recursive input-object types. Supplied scalar values are still assumed
already coerced and type-conformant, as in the execution model.

For example, IBM's `users(max: 5) { age }` example assigns `age` field weight 2. Static
analysis reports `fieldCost = 1 + 5 * 2 = 11`; if execution returns three users, query
response analysis reports `fieldCost = 1 + 3 * 2 = 7`. With default object type weights,
the corresponding type costs are 6 and 4: one `Query` plus five or three `User` values.

## List sizes and the tree summary

For a list field, the cardinality bound is selected in this order:

1. a direct `sizedFields` value inherited from its parent field;
2. the maximum supplied or defaulted `Int` slicing argument;
3. `assumedSize`;
4. `CostModel.defaultListSize`.

When an annotation names `sizedFields`, its slicing or assumed size is transferred to
those child fields and does not size the annotated field itself, even if that field also
returns a list.

The final case is a formalization boundary. IBM treats a list without finite size
information as unbounded; a `Nat`-valued analysis needs a finite externally justified
bound. Soundness therefore requires the executed response to respect whichever bound
the model selects.

The algebra's synthesized `Summary` is a function from resolved direct-child sizing
metadata to nonnegative `Bound`. This context lets the bottom-up fold transfer a parent field's
`sizedFields` cardinality to the named child list. Simultaneous condition-tree
contributions add, while alternative branches take componentwise maxima. The exact-case
backend fixes every unresolved Boolean variable once for the whole selection hierarchy,
prunes `@skip` and `@include` branches under each resulting environment, and joins those
environments and the possible runtime object types.

Both backends expose a variable-aware estimator:

- `StaticCost.ExactCases.estimateOperationWithVariables`;
- `StaticCost.Syntactic.estimateOperationWithVariables`.

`estimateOperationWithVariables` applies supplied values plus operation defaults for
argument, input, list-size, and Boolean-condition costs. Passing an explicit empty
supplied-variable map still materializes operation defaults. A Boolean condition with
no supplied value or default remains unknown and is maximized across its feasible
branches.

The syntactic backend always runs its own factored traversal; it never silently selects
ExactCases. Duplicating a negative return-type contribution is not order-preserving, so
its execution-soundness statement assumes that all schema type costs are nonnegative.
This restriction does not apply to ExactCases. It also does not reject negative
argument or input-field weights, whose complete field-call cost is clamped at zero.

The regression test demonstrates why the premise is necessary. Give `Query` weight
zero, `Book` weight `-7`, and `String` weight `5`, then select two independently
conditional pieces of the same response field: `book { title }` and
`book { author { name } }`. When both conditions hold, execution collects `book` once
and its merged type cost is `max(0, -7 + 5 + 6) = 4`. Syntactic factors the pieces and
gets `max(0, -7 + 5) + max(0, -7 + 6) = 0`. Thus the signed type component can be an
underestimate even though the same factoring is conservative for nonnegative type
costs. This is a limitation of the StaticCost algebra under syntactic field factoring,
not a general unsoundness of the Syntactic tree-summary framework.

There is intentionally no variable-free StaticCost estimator or soundness statement.
A finite `Nat` cannot bound every later assignment: a variable may supply an arbitrarily
large slicing integer or recursively nested input value. Supporting that mode would
require an abstract variable environment with explicit bounds, an unbounded cost value,
or a precondition restricting concrete assignments.

The ExactCases backend globally composes feasible condition cases before grouping
response names. Syntactic is faster and may be less precise because response-name pieces
from separate syntax nodes remain separate contributions. Both variable-aware backend
forms carry the execution-soundness witnesses described below.

## Soundness

`actualCost` performs IBM Query Response Analysis over an `AnnotatedResponse`. Each
response field records the concrete resolver call `(parentType, fieldName, arguments)`
that produced its value. Field and argument costs are paid once per resolver call;
completed values determine the concrete type counts and child field multiplicities.

The public `ExactCases.SoundWithVariables` proposition bounds that concrete result
componentwise for all signed IBM weights. Its statement is:

```lean
schemaWellFormed schema
→ operationDefinitionValid schema operation
→ ∀ ObjectRef resolvers variableValues source,
    ResponseWithinEstimatedSizes schema model
        (executeQueryAnnotated schema resolvers variableValues operation source)
    → actualCost schema model
        (executeQueryAnnotated schema resolvers variableValues operation source)
      ≤ ExactCases.estimateOperationWithVariables
          schema model variableValues operation
```

Here `≤` means both actual type cost and actual field cost are at most their static
estimates. `executeQueryAnnotated_equal` separately proves that erasing annotations is
exactly `Execution.executeQuery`, so the theorem covers every resolver environment,
root source, and variable assignment for a well-formed schema and valid operation.
`ExactCases.SoundWithVariablesWithFuel` gives the corresponding explicit-fuel statement;
the Syntactic backend exposes the same pair of statements and witnesses in its namespace,
with the additional `TypeCostsNonnegative schema model` premise required by its factored
field proof.

Syntactic soundness relies on a field-merge invariant: argument-equivalent syntactic
field pieces resolve to the same canonical argument set for the supplied variables.
Consequently they produce identical slicing sizes and recursive input-value costs.
This justifies distributing the one concrete resolver field over the separately
summarized syntactic pieces without changing its argument-sensitive semantics.

`ResponseWithinEstimatedSizes` is the concrete admissibility hypothesis. At every
observed list field, the analysis-specific multiplicity of non-null cost-bearing values
must be no larger than the selected `sizedFields`, slicing-argument, `assumedSize`, or
fallback bound, recursively through the response. This is necessary: six returned
cost-bearing values cannot be bounded by a static estimate that assumes five.

The concrete algebra observes only annotated field values. It defines empty,
simultaneous combination, and field folding; it has no join and cannot observe
conditions. Componentwise maximum exists only in the abstract static analysis.

## Exact-case optimality

`ExactCases.SummaryOptimalWithVariables` states that the synthesized summary function
is the pointwise least bound of every recursively feasible modeled outcome after
applying supplied variable values and operation defaults. The statement mentions only
the pointwise `SummaryBound`, the independent structural-case semantics, and the
computed summary.
Its theorem witness is `ExactCases.summaryOptimalWithVariables`; the localized
best-transfer laws used by that proof remain private to the proof module.

This is structural optimality for the analysis's modeled field outcomes, not a claim
that arbitrary resolver behavior realizes every cost or that the final root-cost
projection is execution-optimal. Execution soundness remains the separate result above.

The regression suite in
[`Tests/GraphQL/Theories/TreeSummary/StaticCost.lean`](../../Tests/GraphQL/Theories/TreeSummary/StaticCost.lean)
includes IBM's published static and query-response examples, assumed and
argument-derived list sizes, schema and operation defaults, nested weighted-input
defaults, undefined-versus-null input behavior, direct `sizedFields` transfer, signed
input costs, collected-field deduplication, and execution-derived actual costs.
