# Execution-readiness checking

`GraphQL.checkExecutionError schema operation` is an executable static checker in
`GraphQL/Theories/ExecutionReadiness.lean`. Use it after schema and operation
validation. It checks concrete field argument defaults and composite output
inhabitance, suppressing counts under infeasible Boolean and type conditions.

## Argument defaults

For each concrete field definition, the checker asks whether every **omitted
non-null argument** has a default. It does not repeat `Validation.argumentsValid`,
variable-use validation, or input-value validation.

For a validated operation, omission of a non-null argument already implies a
default at the declared field location. An object implementing an interface may
omit that default:

```graphql
interface I { f(a: Int! = 1): String }
type Query implements I { f(a: Int!): String }
```

Selecting `... on I { f }` therefore passes operation validation but fails
argument coercion at `Query.f`. The checker detects this missing concrete default.
It need not check the interface default again. Explicitly supplied arguments and
nullable arguments need no default for this check. Defaults need not have equal
values; schema validation checks their types.

`operationCoercibleInPossibleTypes` expresses the additional static condition.
Both it and `operationCompositeFieldTypesInhabited` quantify over variable
environments. Within each environment, they inspect only enabled selections,
retaining the same environment through parent and child fields. Inline fragments
test the current concrete object type instead of expanding to other implementations.
The proof `ExecutionReadiness.operationArgumentsCoercible_of_defaults` combines
it with schema validity, operation validity, and fully supplied non-null typed
variable values to establish argument coercibility. Both the comparison-branch
and complete-normal-form Boolean witnesses use this weaker condition.

The stronger `NormalForm.operationFieldsValidInPossibleTypes` belongs to
`GraphQL/Theories/NormalForm.lean` and supports normalization validity. For example,
`$a: Int` is valid at `I.f(a: $a)` because `I.f` supplies a default, but the same
variable use is invalid at `Query.f(a: $a)` without that default. Supplying a
non-null value still makes it coerce. Thus execution witnesses
need less than preservation of validation when grounding abstract field scopes.

## Result and counting rules

The result is `GraphQL.ExecutionReadiness.Result`:

| Member | Meaning |
| --- | --- |
| `argumentDefaultErrors : Nat` | Feasible concrete field occurrences with an omitted non-null argument lacking a default. |
| `uninhabitedOutputErrors : Nat` | Feasible composite fields with a non-list non-null output and no possible object type. |
| `errorCount : Nat` | Sum of the two counts. |
| `isSuccess : Bool` | Whether both counts are zero. |

Each source field occurrence is checked once per visited concrete object scope.
Distinct implementations and sibling occurrences contribute separately, even if
execution would merge those siblings by response name. Multiple missing defaults
on one field contribute one argument-default error. Nested failures are counted
on the failing descendants, without duplicate counts on their ancestors. The two
categories accumulate independently.

Selecting an uninhabited `Empty!` output contributes one output-inhabitance error;
`Empty`, `[Empty!]`, and `[Empty!]!` do not.

## Feasibility

The traversal maintains a concrete runtime object type and a conjunction of
signed Boolean variables. An inline fragment must admit that runtime type.
`@include(if: false)`, `@skip(if: true)`, and contradictory requirements on the
same variable prune the entire governed subtree before counting.

Boolean constraints persist across parent-field boundaries. Thus a child requiring
`x = false` beneath a parent requiring `x = true` contributes no errors. Each
sibling starts with the inherited constraints; siblings do not constrain each
other. When entering a composite field's children, the checker traverses each
possible output object type while retaining the Boolean constraints.

Variable defaults do not fix Boolean conditions: supplied values can override
them. Nullable and list parents do not suppress feasible descendants, because
those descendants can execute when the parent returns a non-null object or a
nonempty list.

## Scope

The checker has no supplied values or resolvers. Counts describe errors when the
corresponding field is reached, not response error counts or a claim that every
execution reaches the field. Arbitrary runtime variable values or resolver results
can cause other errors even when both counts are zero. Invalid schemas and
operations are outside its contract.

## Semantic soundness and necessity

`GraphQL.ExecutionReadinessSound schema operation` states that a well-formed schema
and valid operation satisfying `operationCompositeFieldTypesInhabited` and
`operationCoercibleInPossibleTypes` admit an execution with zero counted errors.
The statement existentially quantifies over the resolver-reference type, resolvers,
supplied variable values, and root reference. It executes `Execution.executeQuery`
with an object of the operation's root type, using the standard schema-aware fuel
bound, and requires the resulting response's `errors` count to be zero.

`GraphQL.executionReadiness_sound`, in
`Proofs/GraphQL/Theories/ExecutionReadiness/SemanticSoundness.lean`, proves this
statement independently of the static checker. It constructs non-null supplied
variable values, derives argument coercibility from concrete defaults, and uses
`QueryInclusion.supportedResolvers` with `PUnit` object references. The existing
error-free annotated execution theorem supplies the standard fuel bound; annotation
erasure gives the ordinary `executeQuery` response. This guarantees one successful
configuration; arbitrary variable assignments or resolver results may still fail.

Two additional propositions state that neither readiness premise can be dropped
from the general existence guarantee:

- `ExecutionReadinessNeedsInhabitedOutputs` asks for a well-formed schema and valid
  operation satisfying `operationCoercibleInPossibleTypes` but failing
  `operationCompositeFieldTypesInhabited`, for which every execution configuration
  has a nonzero error count. An unconditionally selected singular non-null field
  returning an interface with no possible object type supplies the counterexample.
  `GraphQL.executionReadiness_needsInhabitedOutputs` proves this statement.
- `ExecutionReadinessNeedsCoercibleArguments` asks for the symmetric counterexample:
  inhabited composite outputs, a failure of `operationCoercibleInPossibleTypes`,
  and a nonzero error count for every execution configuration. The omitted required
  argument whose interface default is absent from the concrete implementation,
  shown above, supplies the counterexample when selected unconditionally.
  `GraphQL.executionReadiness_needsCoercibleArguments` proves this statement.

Both necessity witnesses are in
`Proofs/GraphQL/Theories/ExecutionReadiness/Necessity.lean`. Each proves schema
well-formedness, operation validity, the retained readiness predicate, failure of
the omitted predicate, and exactly one counted error for every resolver-reference
type, resolver environment, supplied-variable environment, and root reference.
They express necessity for a guarantee covering all valid operations, not a converse for
each individual operation: variable assignments, inapplicable fragments, null
parents, and empty lists can prevent a failing field from being executed.

## Checker correctness

The checker-correctness section of `GraphQL/Theories/ExecutionReadiness.lean`
states `CheckExecutionErrorSound` and `CheckExecutionErrorComplete`.
`GraphQL.checkExecutionError_sound` and `GraphQL.checkExecutionError_complete`, in
`Proofs/GraphQL/Theories/ExecutionReadiness/Checker.lean`, prove those statements.
Together, `checkExecutionError_errorCount_eq_zero_iff` establishes:

```lean
(checkExecutionError schema operation).errorCount = 0
  ↔ operationCompositeFieldTypesInhabited schema operation
    ∧ operationCoercibleInPossibleTypes schema operation
```

`checkExecutionError_isSuccess_sound` and `checkExecutionError_isSuccess_complete`
supply both directions using `.isSuccess = true`. No schema or operation validity
premises are needed for this equivalence with the two readiness predicates.
Interpreting those predicates as execution guarantees still relies on validation
and the other execution assumptions described above.

The soundness proof follows the traversal in a fixed environment satisfying the accumulated
Boolean condition. Pruned branches cannot execute in that environment. Zero summed
counts imply zero local and child counts, which establish both recursive predicates.
The Boolean default-presence and output-inhabitance helpers are also proved
equivalent to their local predicates.

Completeness constructs a satisfying Boolean environment for every retained
condition, using its literals directly. The readiness predicates then imply that
each checked local obligation holds. Their recursive obligations establish zero
child counts in every possible output scope. This proof requires no enumeration
of Boolean assignments and makes no change to the executable checker.

## Rust port

The implementation uses structural recursion, schema lookups, list folds, and
sorted lists of signed Boolean variables. It enumerates possible object types;
it does not enumerate Boolean assignments or run coercion. The result is a pair
of counters with addition. The tests in
`Tests/GraphQL/Theories/ExecutionReadiness.lean` give concrete examples and expected
counts for a Rust port.

## Proposed schema constraints

The proposed-schema section of `GraphQL/Theories/ExecutionReadiness.lean` describes
two optional strengthenings of schema validation. They supplement the modeled
September 2025 `schemaWellFormed` predicate.

`schemaInterfaceArgumentDefaultsPreserved` requires object and interface
implementations to preserve the presence of defaults on inherited field arguments.
It follows option 3 discussed in
[graphql-spec issue #1121](https://github.com/graphql/graphql-spec/issues/1121):
an implementation must supply a default whenever the interface does, but the
default values may differ. This rule includes nullable arguments, although the
execution-readiness obstruction concerns omitted non-null arguments. Existing
schema validation still checks input types and default-value validity.
`ExecutionReadiness.operationCoercibleInPossibleTypes_of_schema` proves that under
schema and operation validity, this constraint implies
`operationCoercibleInPossibleTypes` for every operation. The proof transfers
interface defaults to the concrete runtime field, using explicit ancestor
declarations to cover transitive interface inheritance. Additional implementation
arguments already satisfy the existing rule forbidding required extra arguments.

`schemaCompositeFieldTypesInhabited` checks every declared object and interface
field. A singular non-null composite output must have a possible runtime object
type. Uninhabited interfaces can still be declared and used as `Empty`, `[Empty]`,
`[Empty!]`, `[Empty]!`, or `[Empty!]!`; `Empty!` is rejected. Nullable outputs can
complete as null, and list outputs can be empty even when their elements are
non-null. Scalar and enum outputs are unaffected.
`ExecutionReadiness.operationCompositeFieldTypesInhabited_of_schema` proves that
this constraint implies `operationCompositeFieldTypesInhabited` for every
operation, independently of which fields an operation selects. This implication
does not require schema or operation validity; implicit `__typename` is a scalar
leaf, and every declared composite field is covered directly by the constraint.

`SchemaExecutionSound schema` states the resulting guarantee: for a well-formed
schema satisfying both constraints, every valid operation has some resolver
environment, supplied-variable environment, and root object for which
`Execution.executeQuery` returns zero counted errors using its standard fuel
bound. No separate operation-readiness premises appear in this statement. The
witnesses may depend on the operation; arbitrary resolver results and variable
values can still fail. `GraphQL.schemaExecution_sound` proves this statement by
deriving both operation-readiness predicates and applying
`GraphQL.executionReadiness_sound`. The schema implication proofs and final witness
are in `Proofs/GraphQL/Theories/ExecutionReadiness/SchemaConstraints.lean`.
`Tests/GraphQL/Theories/ExecutionReadiness/SchemaConstraints.lean` checks default
presence, nullable arguments, output wrappers, and inhabited composite outputs,
and audits the three public witnesses' axiom dependencies.
