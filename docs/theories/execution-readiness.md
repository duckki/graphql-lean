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
