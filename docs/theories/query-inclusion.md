# Query Inclusion

`GraphQL.QueryInclusion.includesBool` decides the project’s recursive,
resolver-provenance-preserving query-inclusion relation. Inclusion is directional:
every response field selected by the right operation must also be present in the left
response whenever that right field is selected, with composite values compared
recursively.

## Correctness Domain

The executable Boolean function is total on the project’s permissive raw schema and
operation syntax. A production caller should establish these checks before treating its
result as a semantic decision:

1. `SchemaWellFormedness.schemaWellFormed schema`;
2. `Validation.operationDefinitionValid schema left`;
3. `Validation.operationDefinitionValid schema right`;
4. `comparisonBranchesArgumentCoercible schema left right`;
5. `operationCompositeFieldTypesInhabited schema left`; and
6. `operationCompositeFieldTypesInhabited schema right`.

The first three premises suffice for soundness: `includesBool_sound` proves that
acceptance implies `includes`. All six premises give the completeness direction through
`includesBool_complete`, so the Boolean function decides the relation on that checked
domain. `includesBool` does not run validation, probe-readiness, or inhabitance checks
internally; a production API should perform them before calling the checker or bundle
them in a checked wrapper.

The `includes` relation has additional deliberate fine print:

- variable-definition order and definitions occurring on only one side are unrestricted;
  definitions sharing a name must have structurally equal declared types and
  syntactically equivalent defaults, which `includesBool` checks before selection
  analysis;
- every variable environment is constrained, including environments whose Boolean
  condition variables do not all resolve: an unresolvable `@skip`/`@include` condition
  behaves like `false` during field collection, so those executions are ordinary
  error-free executions;
- only pairs of annotated executions with zero execution errors contribute response-shape
  obligations.

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

`comparisonBranchesArgumentCoercible` is the corresponding completeness-only witness.
For each finite Boolean assignment, it requires an extension with values for any
remaining variables under which both operations' field arguments coerce successfully.
The complete Boolean assignment is the prefix of that environment, so operation defaults
and extension values cannot override the branch being checked. It does not claim that
arbitrary runtime variable values succeed. The shared
`GraphQL.Theories.ExecutionReadiness.operationArgumentsCoercible` predicate performs the
recursive, operation-local check; it conservatively checks every syntactic field and each
possible composite child runtime type, including fields disabled by the particular
Boolean assignment.

The zero-error restriction prevents resolver failures and null bubbling from erasing
otherwise required response structure. Composite-return inhabitance is needed only for
completeness: it supplies error-free witness executions and rules out vacuous semantic
inclusion when a selected composite return has no possible runtime types.

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
syntax witness: every right selection must have an exact left match for response name,
field name, arguments, directives, and inline-fragment type, with child selections checked
recursively. Extra left selections are allowed. This bypasses type-region and Boolean
splitting for syntactically included child scopes; a response-depth guard preserves the
reference checker’s explicit fuel semantics.

Scalar response groups also have a symbolic condition shortcut. Cumulative
`@include`/`@skip` conditions are conjunctions of Boolean literals; the checker subtracts
the union of matching left clauses from each right clause and accepts when no assignment
remains. This recognizes complementary coverage such as `$x` together with `!$x` without
enumerating unrelated variables. Because selection conditions are flattened before this
check, a broader left type condition can directly cover a narrower right type region even
when their inline-fragment syntax differs.

The same local proof follows a one-to-one composite field when its child selection has the
verified syntactic-inclusion witness. Composite field merging and other ambiguous cases
continue through the complete response-local search.

## Proof Structure

`includesBoolReference` is retained only as a simple reference checker; the public
checker does not fall back to it. Under schema well-formedness, operation validity, and
composite-return inhabitance, `includesBool_complete_of_reference` proves that the guarded
field-group search covers every reference-checker case.

`GraphQL.QueryInclusion.includesBool_sound` and
`GraphQL.QueryInclusion.includesBool_complete` are exported by the proof root
`Proofs.GraphQL.Theories.QueryInclusion`.

## Benchmark

The native benchmark includes explicit positive and negative pairs, a reflexive shortcut
case, a deep missing-field case, and symbolic Boolean-clause coverage:

```sh
lake exe query-inclusion-bench
```

It is a development benchmark rather than a stable performance suite; broader adversarial
and production-language profiling can be added later.
