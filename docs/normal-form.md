# Normal Forms

This document describes the project-specific normal forms and their public
correctness propositions. Normal forms are not GraphQL specification features;
they are proof and algorithm artifacts used to relate different operation
representations to the same resolver-parametric execution semantics.

The public definitions live in `GraphQL/Theories/NormalForm.lean`. Proof witnesses live
under `Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/` and
`Proofs/GraphQL/Theories/NormalForm/CompleteNormalization/`.

The public soundness and uniqueness propositions and their checked proof witnesses use
coerced resolver arguments.

## The Two Normal Forms

### Ground-Type Normal Form

`NormalForm.normalizeOperation` is the directive-free normalizer. It rewrites an
operation selection set by:

1. merging fields with the same response name into one field head whose child
   selection set contains the merged subselections from the source group, and
2. grounding abstract return types by replacing their child selections with one
   inline fragment per possible concrete object type.

The resulting shape is described by `operationNormal`: selection layers are
grounded to object type conditions where needed and are non-redundant by
response name and inline-fragment type condition.

### Complete Normal Form

`NormalForm.completeNormalizeOperation` is the directive-aware normalizer for
the modeled `@skip` and `@include` directives. It computes the Boolean variables
mentioned by those directives, enumerates complete BoolCases once at the
operation root, and wraps each nonempty branch in unconditional inline fragments
carrying that BoolCase's directive tests.

Inside a selected BoolCase branch, fields are normalized with the same
ground-type machinery. Nested field child normalization receives the selected
BoolCase as context; it does not introduce another directive-only DNF at every
composite field.

The resulting shape is described by `completeNormalOperation`: the operation is
a complete Boolean DNF at the root, and every branch body is directive-free
ground-type normal form.

## Proved Properties

Each normalizer has four public property families: normality, semantics preservation,
validity preservation, and uniqueness up to reordering.

### Normality

Normality says the output has the intended syntactic shape.

- `NormalForm.normalizeOperationNormal` is witnessed by
  `GraphQL.NormalForm.GroundTypeNormalization.normalizeOperation_normal` in
  `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
  It assumes only `SchemaWellFormedness.schemaWellFormed schema`.
- `NormalForm.completeNormalizeOperationNormal` is witnessed by
  `GraphQL.NormalForm.CompleteNormalization.completeNormalizeOperation_normal`
  in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization`.
  It assumes schema well-formedness and operation validity, because the complete
  normal shape depends on the operation's modeled directive variables and
  validated root shape.

### Semantics Preservation

Semantics preservation says the original and normalized operations execute to
the same response for every resolver environment, explicit fuel value, source value,
and variable assignment in the theorem's stated runtime domain.

- `NormalForm.groundTypeNormalFormSemanticsPreservation` is witnessed by
  `GraphQL.NormalForm.GroundTypeNormalization.groundTypeNormalFormSemanticsPreservation`
  in `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
  It assumes schema well-formedness, operation validity, and
  `operationDirectiveFree operation`.
- `NormalForm.completeNormalizationSemanticsPreserved` is witnessed by
  `GraphQL.NormalForm.CompleteNormalization.completeNormalizationSemanticsPreserved`
  in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization`.
  It assumes schema well-formedness, operation validity, and
  `operationBoolVarsComplete operation variableValues`, so every modeled
  directive variable used by the operation has a Boolean runtime value.

Both statements compare `Execution.executeQueryWithFuel` at the same explicit
fuel. This avoids making a false syntax-size preservation claim: normalization
can change the operation size, so comparing default operation-derived fuel
bounds would not be stable.

### Validity Preservation

Validity preservation says the normalized output is also accepted by
`Validation.operationDefinitionValid`. These theorems intentionally need extra
assumptions that are not GraphQL validation rules.

- `NormalForm.normalizeOperationValid` is witnessed by
  `GraphQL.NormalForm.GroundTypeNormalization.normalizeOperation_valid` in
  `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
  In addition to schema well-formedness, operation validity, and
  directive-freeness, it assumes `operationFieldsValidInPossibleTypes` and
  `operationTypeConditionFeasible`.
- `NormalForm.completeNormalizeOperationValid` is witnessed by
  `GraphQL.NormalForm.CompleteNormalization.completeNormalizeOperation_valid`
  in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization`.
  In addition to schema well-formedness and operation validity, it assumes
  `operationFieldsValidInPossibleTypes` and
  `operationBoolTypeConditionFeasible`.

The extra assumptions are important because they expose a real gap between
GraphQL operation validity and runtime semantics.

Spec 5.8.4 requires every declared variable to remain syntactically used. The
ground feasibility assumption requires every selected field's complete
type-condition stack to be feasible in each concrete scope introduced by
grounding. Every nonempty composite child must also have at least one possible
concrete type. Consequently ground normalization preserves every variable use;
`normalizeOperation_operationVariablesUsed` derives the normalized operation's
all-variables-used property from input validity.

For complete normalization, `operationBoolTypeConditionFeasible` additionally
requires every selection to survive in at least one Boolean case compatible
with its ancestors. It also requires every admitted case for a nonempty child
selection set to retain a child. Thus every original variable use is preserved
in at least one normalized branch: Boolean directive variables occur in the
generated case wrappers, while other variables remain in a surviving branch.
`completeNormalizeOperation_operationVariablesUsed` therefore derives the
normalized all-variables-used property from input validity and feasibility.

First, GraphQL operation validity rejects syntactically empty selection sets,
but a syntactically nonempty selection set can be semantically empty for a
particular scope. For example, all child selections of a composite field may be
under infeasible type-condition stacks.

The validation rule for inline-fragment applicability is local to the current
parent scope, so the following operation can be valid even though no runtime
value of `f` can satisfy the full `A`, `I`, and `B` stack:

```graphql
interface I {
  id: ID
}

type A implements I {
  id: ID
}

type B implements I {
  id: ID
  data: String
}

type Query {
  f: A
}
```

```graphql
{
  f {
    ... on I {
      ... on B {
        data
      }
    }
  }
}
```

`A` overlaps `I` because `A` implements `I`, and `I` overlaps `B` because `B`
implements `I`, but the intersection of `A` and `B` is empty. Execution never
reaches `data` for any runtime object returned by `f`, but normalization may
drop the infeasible scopes and therefore expose an empty composite child
selection set. `operationTypeConditionFeasible` rules this out for ground
normalization by requiring every field stack to be feasible. The mode-free
`operationBoolTypeConditionFeasible` strengthens that condition for complete
normalization: all selection paths have feasible type conditions, every
selection has a compatible Boolean case, and every case admitted by a surviving
composite selection retains at least one child.

Second, a field selected under an interface type condition is validated against
the interface field definition. Ground normalization makes concrete
implementation object scopes explicit. A field selection that is valid under the
interface may become invalid under one of those implementation object types, for
example when the implementation field requires arguments that the interface field
did not require or default. Normalization can therefore change the field definition
used for argument coercion and the semantic argument map passed to the resolver. The
`operationFieldsValidInPossibleTypes` assumption records the operation-specific
compatibility needed for every concrete branch introduced by normalization.

For example:

```graphql
interface I {
  value(x: Int! = 7): String
}

type T implements I {
  value(x: Int!): String
}

type Query {
  i: I
}
```

```graphql
{
  i {
    value
  }
}
```

The operation is valid when checked under `I.value`, because `x` has a default
there. If `i` resolves to a `T`, execution coerces arguments for `T.value`,
where `x` is non-null and has no default, so the modeled resolver argument map
omits `x`. The validity assumption rules out exposing that changed resolver input.
This is the same shape as GraphQL spec issue
[#1121: ProvidedRequiredArgumentsRule fails to evaluate all potential runtime
types](https://github.com/graphql/graphql-spec/issues/1121). That issue lists
several possible spec fixes, including changing required-argument validation to
inspect possible runtime types. `operationFieldsValidInPossibleTypes` is the
operation-local theorem assumption corresponding to that style of fix.

These assumptions are deliberately outside `GraphQL.Validation`: they are not spec
validation requirements. They are theorem-specific preconditions for asking a stronger
question, namely whether a normalized operation is itself a valid GraphQL operation.

### Uniqueness Up To Reordering

Uniqueness says valid normal operations with the same resolver-parametric semantics
have the same structure modulo order, with corresponding field arguments compared
after the schema and operation variables coerce them to the lists seen by resolvers.
The raw selection-only `*EqualUpToReordering` relations are proof-layer helpers in
`GroundTypeNormalization/Uniqueness/SyntaxDiff.lean`. Public resolver-boundary
relations use the `*EqualUpToReorderingWithCoercion` suffix.

Every operation-level soundness and uniqueness statement assumes the binary
relation
`variableDefinitionsEquivalent left.variableDefinitions right.variableDefinitions`.
It compares the lists positionally, requiring equal names and equivalent defaults;
it intentionally does not compare variable types.

- `NormalForm.normalOperationsEqualUpToReorderingSemanticallyEquivalent` is witnessed
  by `normal_operations_equalUpToReordering_semanticallyEquivalent` in
  `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
  It lifts selection-set reordering soundness to operation execution.
- `NormalForm.normalizeOperationsEqualUpToReorderingSemanticallyEquivalent` is
  witnessed by `normalizeOperations_equalUpToReordering_semanticallyEquivalent` in
  `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
  It lifts normalized-operation reordering equality back to source-operation semantics.
- `NormalForm.normalOperationsSemanticallyEquivalentEqualUpToReordering` is witnessed
  by `normal_operations_semanticallyEquivalent_equalUpToReordering` in
  `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
  It concludes `operationsEqualUpToReorderingWithCoercion`, comparing
  directive-free ground-normal siblings up to reordering for every supplied variable
  environment.
- `NormalForm.normalizeOperationUniqueUpToReordering` is witnessed by
  `GraphQL.NormalForm.GroundTypeNormalization.normalizeOperation_uniqueUpToReordering`
  in `Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization`.
- `NormalForm.completeNormalOperationsSemanticallyEquivalentEqualUpToReordering` is
  witnessed by `complete_normal_operations_semanticallyEquivalent_equalUpToReordering`
  in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization`.
  It concludes `completeNormalOperationsEqualUpToReorderingWithCoercion` and
  additionally ignores complete Boolean branch order and minterm stem order;
  field arguments are compared in environments satisfying each paired minterm.
  Boolean-support equivalence is derived from validity, complete normality, and
  unrestricted execution equivalence.
- `NormalForm.completeNormalizeOperationsEqualUpToReorderingSemanticallyEquivalent`
  is witnessed by
  `completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent` in
  `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization`.
  Its semantic conclusion is restricted to complete Boolean environments, with
  source Boolean-support equivalence stated explicitly because normalized equality
  only compares normalized support. It also requires position-wise
  variable-definition equivalence, since public execution applies
  operation-specific defaults.
- `NormalForm.completeNormalizeOperationUniqueUpToReordering` is witnessed by
  `GraphQL.NormalForm.CompleteNormalization.completeNormalizeOperation_uniqueUpToReordering`
  in `Proofs.GraphQL.Theories.NormalForm.CompleteNormalization`.
  It uses the same possible-type and Boolean/type-condition feasibility assumptions as
  complete-normalization validity, and compares operations with equivalent Boolean
  variable support.

The ground and complete proofs are summarized in
`docs/normal-form-uniqueness.md`.

## Proof Shape

The ground-type proof follows the same broad strategy as GraphCoQL's normal-form
argument: prove selection-set preservation first, then lift it to operations.
The key field case relates execution's collected response-name group to the
normalizer's syntactic response-name group, uses field-merge validation to show
the representative field resolves the same field with the same arguments, and
then applies the recursive preservation theorem to the merged child selection
set.

The complete-normalization proof adds a Boolean layer. It proves that the
runtime directive assignment selects the same BoolCase branch that static
filtering chose, then reuses the ground-type preservation theorem on that
directive-free branch. Its validity proof uses filtered branch invariants rather
than requiring the Boolean-filtered intermediate syntax to be fully valid as raw
GraphQL.
