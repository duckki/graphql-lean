# Query Inclusion

`GraphQL.QueryInclusion.includes` is a syntactic relation over selected response paths.
Under every complete Boolean assignment, each path selected by the right operation must
also be selected by the left. Path steps record the concrete parent object, response
name, field identity, argument syntax, and output type. The executable checker is
`GraphQL.QueryInclusion.includesBool`.

`GraphQL.QueryInclusionSemantics.includes` separately compares every pair of error-free
annotated executions, preserving response fields and resolver-call provenance. The
`IncludesSyntacticToSemantic` and `IncludesSemanticToSyntactic` statements connect the
two relations.

## Correctness Domain

The Boolean checker is total on permissive raw syntax. Its syntactic soundness requires:

1. `SchemaWellFormedness.schemaWellFormed schema`;
2. `Validation.operationDefinitionValid schema left`;
3. `Validation.operationDefinitionValid schema right`.

`includesBool_sound` proves acceptance implies syntactic `includes`, and
`includesBool_complete` proves the converse under the same three premises. Thus a
rejected result is conclusive for valid operations under a well-formed schema. The
checker itself does not run validation.

The syntactic relation compares field collection without executing resolvers. Its
Boolean assignments cover the condition variables used by both operations. It also
requires shared variable definitions to have structurally equal types and syntactically
equivalent defaults; definition order and one-sided definitions remain unrestricted.

For valid operations under a well-formed schema, syntactic inclusion implies semantic
inclusion. The reverse bridge requires both
`operationCoercibleInPossibleTypes` and
`operationCompositeFieldTypesInhabited` for each operation. Concrete argument defaults supply
coercible arguments, and output inhabitance supplies error-free response values.
Together they construct an error-free execution witness for each selected path.
The semantic relation alone can be vacuous when such executions are unavailable.
`operationBoolTypeConditionFeasible` is not required by this bridge.

The shared-definition check deliberately avoids omitted/default-aware condition analysis.
When a shared value is omitted, equivalent defaults give both operations the same value;
equal declared types ensure that a common supplied probe is accepted at both variable
boundaries. One-sided defaults may materialize independently. A production caller should
separately coerce the same request variables for both operations and fall back when
either operation produces a request or execution error.
The check projects each definition list to names declared by the other operation, then
compares those projections syntactically up to reordering. This formulation relies on the
operation-validity premises that reject duplicate variable names; behavior on invalid
duplicate-name lists is outside the checker theorem domain.

The semantic-to-syntactic proof constructs a supplied variable environment for
each `BoolCase` complete on the comparison condition variables. Both operations'
field arguments coerce in that environment.
That environment must agree with the case on those condition variables; unrelated
entries in the case do not constrain argument values. It does not claim that arbitrary
runtime variable values succeed. The shared
`GraphQL.Theories.ExecutionReadiness.operationArgumentsCoercible` predicate performs the
recursive, operation-local check: it checks enabled fields under the supplied
Boolean values and every possible composite child runtime type.

Output inhabitance does not imply argument coercibility. For example, the current
schema rules accept:

```graphql
interface I { f(a: Int! = 1): String }
type Query implements I { f(a: Int!): String }
```

Both `{ ... on I { left: f } }` and `{ ... on I { right: f } }` validate against
`I.f`, whose default permits omitting `a`. Execution uses `Query.f`, which has no
default, so every execution has a coercion error. Their composite-output
inhabitance obligations hold, semantic inclusion is vacuous, and syntactic
inclusion fails because their response names differ.
`Tests.GraphQL.Theories.QueryInclusionSemantics.ArgumentCoercibility` proves this
counterexample over all resolvers, variable values, and source values.

`operationCoercibleInPossibleTypes` checks that omitted non-null field arguments
have defaults in each concrete implementation on enabled paths. Both readiness
predicates quantify over variable environments, preserving correlated conditions
through field boundaries. Inline fragments retain the current concrete runtime
type. Validation already checks supplied arguments at the declared location; the static predicate does not repeat those
checks. It rejects this example and replaces the explicit coercibility premise
for both operations. The stronger `NormalForm.operationFieldsValidInPossibleTypes`
is defined in `GraphQL/Theories/NormalForm.lean` for normalization validity.

The proof
`QueryInclusionSemantics.exists_coercibleValues_for_comparisonCase`
constructs a common environment for the union of the operations' variable
definitions. Matching names have the same type by shared-definition compatibility;
names declared by only one operation remain supported. Every declared variable
receives a non-null typed value, so operation defaults do not change the supplied
environment. Each Boolean case overrides only comparison-condition variables,
including conditions used by just one operation. Unrelated entries in the case
are ignored. This proves argument coercibility without output-inhabitance or
Boolean/type-condition feasibility assumptions; output inhabitance is used later
when constructing complete error-free responses.

The semantic relation restricts both executions to zero errors, preventing resolver
failures and null bubbling from erasing otherwise required response structure. It
also covers variable environments where a directive condition does not resolve to a
Boolean; field collection treats that condition as false.
`operationCompositeFieldTypesInhabited`
requires a possible runtime object only for a selected non-list `T!` return whose
named type `T` is composite. If `T` has no possible objects, nullable `T` can complete
as `null`, and any list wrapping `T` can complete as `[]`, including `[T!]!`. The
semantic bridge uses those values as error-free witnesses; a selected non-list `T!`
with no possible object has none. Syntactic checker completeness has no inhabitance
premise because it compares selected paths without constructing execution witnesses.

## Response-Local Search

At each response scope, the checker analyzes every right-hand response name independently.
Its type regions come from the conditions that can contribute that response name on either
side, and it splits only the Boolean variables used by those guarded fields. Variables
below a composite field are delayed until the recursive child scope. For every local
type/Boolean region, active fields are merged before child selections are checked. The two
conditional source shapes need not match.

The checker does not construct condition trees. It consumes the flat conditioned-field
stream from `GraphQL.SelectionConditions`, groups that stream in one pass by response
name, and retains each cumulative condition. Resolver lookup remains sensitive to the
concrete parent type, which preserves covariant return types and field-call provenance.

Before starting a recursive child search, the checker accepts a conservative directional
syntax witness. For the child’s possible runtime types, it first flattens directive-free
inline fragments whose type condition admits every type in that list, on either side. A
typed fragment is never flattened when the possible-types list is empty. Every
remaining right selection must have an exact left match for response name, field name,
arguments, directives, and inline-fragment type. The exact syntax matcher checks child
selections recursively. Extra left selections are allowed. If this boundary-only
witness fails and matched fields contain either bare/fragment packaging differences
or differing directive-free fragment wrappers with corresponding fields, a recursive
witness retries inside matched fields and fragments. It unions possible
return types across concrete parent definitions, then narrows them under matched
fragment conditions. Both witnesses retain the response-depth guard and have
soundness proofs; the complete response-local search remains the fallback.

Scalar response groups also have a symbolic condition shortcut. Cumulative
`@include`/`@skip` conditions are conjunctions of Boolean literals; the checker subtracts
the union of matching left clauses from each right clause and accepts when no assignment
remains. This recognizes complementary coverage such as `$x` together with `!$x` without
enumerating unrelated variables. Because selection conditions are flattened before this
check, a broader left type condition can directly cover a narrower right type region even
when their inline-fragment syntax differs.

The local composite shortcut handles one field occurrence on each side of a runtime-type
slice when the left guard covers the right, resolver calls agree, and the child selections
pass the verified syntactic-inclusion witness. Merged groups continue to the symbolic
witness or complete response-local search.

Guarded composite groups have a recursive symbolic witness as well. When every occurrence
uses the same resolver call and the left occurrence conditions cover every right condition,
the checker carries each occurrence's cumulative Boolean condition into its child boundary.
`SelectionConditions.ofTypeRegionUnder` performs this seeded extraction. Child response names
then split only the variables they actually read, avoiding the product of independent guards
that happen to share a parent response name. A child condition that contradicts its carried
parent condition is discarded during extraction. The witness is tried only for groups with a
Boolean condition; if resolver-call equality, condition coverage, or the seeded child check
fails, the complete assignment-enumerating search remains the fallback.

## Proof Structure

`includesBoolReference` is retained only as a simple reference checker; the public
checker does not fall back to it. Under schema well-formedness and operation validity,
`includesBool_complete_of_reference` proves that the guarded field-group search covers
every reference-checker case.

`GraphQL.QueryInclusion.includesBool_sound` and
`GraphQL.QueryInclusion.includesBool_complete` are exported by
`Proofs.GraphQL.Theories.QueryInclusion`. The two bridge theorems are exported by
`Proofs.GraphQL.Theories.QueryInclusionSemantics`.

## Benchmark

The native benchmark includes explicit positive and negative pairs, a reflexive shortcut
case, a deep missing-field case, symbolic Boolean-clause coverage, a guarded-parent
case with fourteen independent child guards, and nested transparent-fragment cases
for bare/wrapped and differently wrapped fields:

```sh
lake exe query-inclusion-bench
```

It is a development benchmark rather than a stable performance suite; broader adversarial
and production-language profiling can be added later.
