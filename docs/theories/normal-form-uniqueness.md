# Normal Form Uniqueness

Complete normalization is the main normal-form construction of this development. It
turns an operation with Boolean `@skip` and `@include` conditions into exhaustive
Boolean branches, ground-types every surviving branch, and removes the remaining
semantic ambiguity from the syntax except for ordering that execution does not
observe.

The target uniqueness theorem says that this syntax is canonical for the modeled
resolver-parametric execution semantics. Ground-type normalization provides the
directive-free stepping stone. Its construction follows the normal-form work in
GraphCoQL; this development extends the setting with resolver-parametric execution,
variables, non-null completion, and counted execution errors, then uses the ground
result to state uniqueness of complete normalization.

The presentation starts with ground-type normalization because it exposes the core
canonicity argument without Boolean branch machinery. Complete normalization then
lifts that result to the repository's main theorem.

## 1. What The Result Says

Let:

- `N` be `normalizeOperation` or `completeNormalizeOperation`;
- `left ~= right` mean resolver-parametric semantic equivalence of full GraphQL
  responses, with object fields compared modulo response-field order; and
- `left =c right` mean structural correspondence up to sibling and complete Boolean
  branch reordering, with field arguments compared by `Argument.argumentsEquivalent`
  after coercion at the resolver boundary.

Subject to the validity and feasibility assumptions in the public statements, the
result is schematically:

```text
N(left) =c N(right)  ->  left ~= right
left ~= right       ->  N(left) =c N(right)
```

The two directions have distinct roles:

```text
semantic completeness / uniqueness:
  left ~= right -> N(left) =c N(right)

reordering soundness:
  N(left) =c N(right) -> left ~= right
```

The public API states them separately because their smallest assumption sets differ.
In particular, complete-normalization soundness for source operations is restricted
to variable environments containing complete Boolean assignments. This is exactly
the domain on which complete normalization preserves source-operation execution.

For operations that are already complete-normal, equality up to reordering implies
unrestricted semantic equivalence when
`variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions`
holds. That extra condition is necessary because public execution applies
operation-specific defaults, while the operation equality relation does not compare
variable definitions.

The equality relation is indexed by the schema and current parent type. For
every supplied variable environment, it applies each operation's variable defaults,
looks up the shared field definition, and requires the resulting coerced argument
lists to be argument-equivalent. Complete-normal Boolean branches make the comparison
only in environments satisfying the paired minterms. Consequently, an omitted
argument and an explicit value equal to its schema default can have the same
uniqueness result.

### Normalization As A Decision Procedure

The canonicity theorem reduces semantic equivalence, which quantifies over all
resolver environments, source values, variable values, and fuel values, to a
structural comparison:

```text
1. normalize left
2. normalize right
3. compare the results up to the permitted reorderings and argument coercion
```

Both normalizers are total deterministic Lean functions. The remaining equality
relations are currently specified as propositions. An executable decision procedure
would additionally need a finite characterization of
`operationsEqualUpToReorderingWithCoercion` and
`completeNormalOperationsEqualUpToReorderingWithCoercion`, or a symbolic coercion
pass that produces comparable canonical syntax.

The checked theorem supplies semantic completeness and soundness for such a future
procedure on operations whose variable names and defaults are position-wise
equivalent. The remaining computational work is to characterize the equality
relation finitely and prove the checker correct.

### Normalization As A Proof Principle

Normalization is useful independently of deciding equivalence. It lets later proofs
replace an arbitrary valid operation by semantically equivalent syntax with stronger
structural invariants.

The main reusable theorem families are:

- semantic preservation:
  `groundTypeNormalFormSemanticsPreservation` and
  `completeNormalizationSemanticsPreserved`;
- normal-form production:
  `normalizeOperation_normal` and `completeNormalizeOperation_normal`;
- validity preservation:
  `normalizeOperation_valid` and `completeNormalizeOperation_valid`;
- reordering soundness:
  `normalizeOperations_equalUpToReordering_semanticallyEquivalent` and
  `completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent`;
- semantic uniqueness:
  `normalizeOperation_uniqueUpToReordering` and
  `completeNormalizeOperation_uniqueUpToReordering`.

A common transformation proof can therefore be reduced to normal syntax:

```text
left ~= N(left) =c N(right) ~= right
```

For example, a transformation can be shown semantics-preserving by proving that its
output and input normalize to equal forms up to reordering. Conversely, unequal
normal forms under this relation provide the premise for disproving
semantic equivalence by contraposition of uniqueness.

## 2. Public Statements

The public proposition definitions live in `GraphQL/Theories/NormalForm.lean`. Their theorem
witnesses live in the corresponding uniqueness proof modules.

All operation-level statements below assume
`variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions`.
This position-wise relation requires equal variable names and equivalent defaults,
with matching presence or absence. It intentionally ignores variable types because
the execution model assumes supplied values are already coerced and type-conformant.

### Ground-Type Normalization

Ground equality ignores sibling-selection order and compares resolver-visible argument
maps after coercion. It is restricted to directive-free operations because complete
normalization is responsible for Boolean directive structure. This is the first
normalization layer, not the final result: its already-normal uniqueness theorem is
reused to compare the ground bodies of complete Boolean branches.

Already-normal reordering soundness is:

```lean
def normalOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationNormal schema left
  -> operationNormal schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationsEqualUpToReorderingWithCoercion schema left right
  -> operationsSemanticallyEquivalent schema left right
```

Ground-normalization soundness is:

```lean
def normalizeOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationsEqualUpToReorderingWithCoercion schema
      (normalizeOperation schema left)
      (normalizeOperation schema right)
  -> operationsSemanticallyEquivalent schema left right
```

Already-normal uniqueness is:

```lean
def normalOperationsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationNormal schema left
  -> operationNormal schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationsSemanticallyEquivalent schema left right
  -> operationsEqualUpToReorderingWithCoercion schema left right
```

Ground-normalization uniqueness is:

```lean
def normalizeOperationUniqueUpToReordering
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationFieldsValidInPossibleTypes schema left
  -> operationFieldsValidInPossibleTypes schema right
  -> operationTypeConditionFeasible schema left
  -> operationTypeConditionFeasible schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationsSemanticallyEquivalent schema left right
  -> operationsEqualUpToReorderingWithCoercion schema
      (normalizeOperation schema left) (normalizeOperation schema right)
```

The corresponding theorem witnesses are
`GroundTypeNormalization.normal_operations_equalUpToReordering_semanticallyEquivalent`,
`GroundTypeNormalization.normalizeOperations_equalUpToReordering_semanticallyEquivalent`,
`GroundTypeNormalization.normal_operations_semanticallyEquivalent_equalUpToReordering`,
and `GroundTypeNormalization.normalizeOperation_uniqueUpToReordering`.
The stricter ground type-condition feasibility assumptions ensure all source
field uses survive normalization, so the normalized operations'
all-variables-used facts are derived rather than assumed.

### Complete Normalization

Complete normalization builds on the ground result by making Boolean directive cases
explicit. Complete normal-form equality additionally ignores root branch order and
the order used to encode each complete Boolean minterm's directive stem.
It does not carry a separate Boolean-support conjunct: ground selection equality
preserves directive variables, while equivalent complete minterms determine the same
support. The proof theorem
`operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReorderingWithCoercion`
recovers that fact from the structural relation.

For operations that are already complete-normal, reordering soundness is
unrestricted under their binary variable-definition equivalence:

```lean
def completeNormalOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> completeNormalOperation schema left
  -> completeNormalOperation schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema left right
  -> operationsSemanticallyEquivalent schema left right
```

The theorem witness is
`CompleteNormalization.complete_normal_operations_equalUpToReordering_semanticallyEquivalent`.

Source-level soundness uses equivalence restricted to complete Boolean variable
environments:

```lean
def operationsSemanticallyEquivalentForCompleteBoolVars
    (schema : Schema) (variables : List BoolVar)
    (left right : Operation) : Prop :=
  ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
    variableValues fuel (source : Execution.ResolverValue ObjectRef),
    boolVarsComplete variables variableValues ->
      Execution.Response.semanticEquivalent
        (Execution.executeQueryWithFuel schema resolvers variableValues left
          fuel source)
        (Execution.executeQueryWithFuel schema resolvers variableValues right
          fuel source)

def completeNormalizeOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationBoolVarsEquivalent left right
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema
      (completeNormalizeOperation schema left)
      (completeNormalizeOperation schema right)
  -> operationsSemanticallyEquivalentForCompleteBoolVars
      schema (operationBoolVars left) left right
```

Its witness is
`CompleteNormalization.completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent`.
`operationBoolVarsEquivalent` transfers completeness of a runtime environment from
the left operation's Boolean support to the right operation's support.

The already-normal uniqueness direction is:

```lean
def completeNormalOperationsSemanticallyEquivalentEqualUpToReordering
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> completeNormalOperation schema left
  -> completeNormalOperation schema right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationsSemanticallyEquivalent schema left right
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema left right
```

For valid operations that are already complete-normal, unrestricted semantic
equivalence determines Boolean support. If a variable occurred on only one side, a
runtime environment can leave that variable non-Boolean while assigning the other
side's support. The first operation then collects no complete branch, while the
other still has a nonempty executable branch. The proof theorem
`operationBoolVarsEquivalent_of_completeNormal_semantics` supplies the derived
support equivalence used by the uniqueness witness.

The normalization uniqueness theorem, and the main result of this document, is:

```lean
def completeNormalizeOperationUniqueUpToReordering
    (schema : Schema) (left right : Operation) : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema left
  -> Validation.operationDefinitionValid schema right
  -> operationFieldsValidInPossibleTypes schema left
  -> operationFieldsValidInPossibleTypes schema right
  -> operationBoolTypeConditionFeasible schema left
  -> operationBoolTypeConditionFeasible schema right
  -> operationBoolVarsEquivalent left right
  -> variableDefinitionsSyntacticallyEquivalent left.variableDefinitions right.variableDefinitions
  -> operationsSemanticallyEquivalent schema left right
  -> completeNormalOperationsEqualUpToReorderingWithCoercion schema
      (completeNormalizeOperation schema left)
      (completeNormalizeOperation schema right)
```

Its witness is
`CompleteNormalization.completeNormalizeOperation_uniqueUpToReordering`.
The possible-type and Boolean/type-condition feasibility assumptions ensure complete
normalization preserves validity and does not create semantically empty branches.
The stricter, mode-free feasibility predicate ensures every Boolean condition
and type-condition path is feasible, so all source field and variable uses
survive in at least one complete branch. The normalized operations'
all-variables-used facts are therefore derived from input validity rather than
assumed.
Unlike the already-normal result, this source-level theorem retains explicit Boolean
support equivalence: semantically redundant directive variables can disappear only
after normalization unless a separate minimization pass is added.

## 3. Proof Development

### Ground-Type Stepping Stone

The ground result extends the ground-typed normal-form construction from GraphCoQL to
this project's execution model. Its selection-set conclusion retains the schema,
parent type, and effective variable environments so it can compare resolver-visible
arguments:

```text
SelectionSetEqualUpToReorderingWithCoercion
  schema leftVariableValues rightVariableValues parentType left right
```

The proof establishes uniqueness by contraposition through a
`NormalSelectionSetDiff`. Its argument-difference case ignores raw
differences such as omission versus an equal schema default because those differences
are not observable. The response-path and resolver separation layers handle response
names, field names, and child-selection differences.

The current separation infrastructure is organized around these theorem surfaces:

- `normalSelectionSetDiff_of_not_equal` constructs the resolver-visible difference
  witness;
- `selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_coercion_diff`
  proves that a valid-normal witness separates response data;
- `FocusedOperationBridge.lean` lifts selection-set separation to operations; and
- `NormalizeBridge.lean` applies already-normal uniqueness to normalization output.

### Complete-Normalization Strategy

The complete proof splits on `operationBoolVars left`.

When Boolean support is empty, complete normality reduces to directive-free ground
normality, and the ground operation theorem applies directly.

With nonempty Boolean support, every complete-normal operation contains one root
branch for each complete Boolean case. The proof establishes:

> Every branch on one side has exactly one branch on the other side with an
> extensionally equivalent Boolean case, and their ground-normal bodies are equal up
> to reordering.

The proof proceeds in five layers:

1. Equivalent complete cases agree under the same bindings; nonequivalent cases
   disagree on at least one variable/value pair.
2. A matching binding makes every directive in one stem pass, while a mismatching
   binding makes the stem collect no fields.
3. Validity descends through the anonymous inline-fragment stem, yielding a valid,
   nonempty, directive-free ground-normal body.
4. The selected binding isolates one branch body. Variable independence transfers
   operation equivalence to semantic equivalence of the selected ground bodies.
5. Ground uniqueness equates matching bodies after coercion in the environment fixed
   by the paired Boolean cases. Bidirectional functional matching over noduplicated
   branch lists yields the branch permutation.

An absent matching branch would compare a valid nonempty ground body with the empty
selection set. Ground uniqueness would relate them after coercion, contradicting
nonemptiness. The complete theorem therefore reuses ground uniqueness as its semantic
discriminator instead of constructing a second complete-level separator.

The complete proof files follow these layers:

- `BoolCases.lean`: Boolean case agreement and disagreement;
- `RestrictedSemantics.lean`: proof-only complete-environment equivalence;
- `StemExecution.lean`: matching and nonmatching stem execution;
- `VariableIndependence.lean`: directive-free execution independence from the
  variable map;
- `GroundBridge.lean`: access to ground uniqueness;
- `CaseBodies.lean`: branch readiness, matching, and body equality;
- `OperationBridge.lean`: branch pairing and already-normal uniqueness;
- `ReorderingSoundness.lean`: the reverse semantic direction; and
- `NormalizeBridge.lean`: normalization-level corollaries.

## 4. Semantic Canonicity

The theorem is best described as **semantic canonicity modulo reordering and
coercion**. A normal
form is a **complete invariant** when two inputs have the same invariant exactly when
they belong to the same semantic equivalence class. Here the invariant is normal
structure modulo sibling order and resolver-visible argument coercion.

The result is stronger than semantics preservation alone. Preservation says
normalization does not change an operation's meaning. Uniqueness says the resulting
structure captures all distinctions in that meaning after quotienting argument syntax
that produces the same resolver input.

In term-rewriting terminology, a terminating and confluent rewrite system presenting
an equational theory is canonical or convergent. This development represents the
rewriting strategy indirectly as total Lean functions. Evaluating
`normalizeOperation` and `completeNormalizeOperation` reduces Lean lambda terms using
Lean's definitional computation rules.

The project does not define a separate GraphQL one-step reduction relation, so the
result is not a confluence theorem over arbitrary GraphQL reduction paths. It is
intended as a canonicity theorem for the output of a deterministic functional
normalizer. Equality up to reordering and coercion remains unoriented; a verified
symbolic comparator or canonical representative for the statement-level coercion
relation would make the associated semantic decision method directly executable. Such
a representative would remain separate from spec execution, which does not
canonicalize resolver inputs.

The distinction from ordinary lambda-calculus normalization is semantic. Beta/eta
conversion generates lambda-calculus equality, whereas GraphQL execution semantics is
defined independently. The uniqueness proof shows that execution equivalence is
reified by the syntax produced through Lean computation.

## 5. Verification Status

The public normal-form definitions, equality propositions, binary
variable-definition relation, and proof witnesses compile together. The commands below
are the focused and full verification suite.

Run:

```sh
lake env lean Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/Uniqueness.lean
lake env lean Tests/GraphQL/Theories/NormalForm/GroundTypeNormalization.lean
lake env lean Proofs/GraphQL/Theories/NormalForm/CompleteNormalization/Uniqueness.lean
lake env lean Tests/GraphQL/Theories/NormalForm/CompleteNormalization.lean
lake build
lake lint
```
