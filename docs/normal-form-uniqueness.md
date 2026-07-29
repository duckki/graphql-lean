# Normal Form Uniqueness

Complete normalization is the main normal-form result of this development. It
turns an operation with Boolean `@skip` and `@include` conditions into exhaustive
Boolean branches, ground-types every surviving branch, and removes the remaining
semantic ambiguity from the syntax except for ordering that execution does not
observe.

The uniqueness theorem says that this syntax is canonical for the modeled
resolver-parametric execution semantics. Ground-type normalization provides the
directive-free stepping stone. Its construction follows the normal-form work in
GraphCoQL; this development extends the setting with resolver-parametric execution,
variables, non-null completion, and counted execution errors, then uses the ground
result to prove uniqueness of complete normalization.

The presentation starts with ground-type normalization because it exposes the core
canonicity argument without Boolean branch machinery. Complete normalization then
lifts that result to the repository's main theorem.

## 1. What The Result Says

Let:

- `N` be `normalizeOperation` or `completeNormalizeOperation`;
- `left ~= right` mean resolver-parametric semantic equivalence of full GraphQL
  responses, with object fields compared modulo response-field order; and
- `left =r right` mean the corresponding syntactic equality up to sibling,
  argument, and complete-Boolean-branch reordering.

Subject to the validity and feasibility assumptions in the public statements, the
result is schematically:

```text
left ~= right  <->  N(left) =r N(right)
```

The two directions have distinct roles:

```text
semantic completeness / uniqueness:
  left ~= right -> N(left) =r N(right)

syntactic soundness:
  N(left) =r N(right) -> left ~= right
```

The public API states them separately because their smallest assumption sets differ.
In particular, complete-normalization soundness for source operations is restricted
to variable environments containing complete Boolean assignments. This is exactly
the domain on which complete normalization preserves source-operation execution.

For operations that are already complete-normal, equality up to reordering implies
unrestricted semantic equivalence when the operations have identical variable
definitions. That extra condition is necessary because public execution applies
operation-specific defaults, while the syntactic reordering relation does not
compare variable definitions.

### Normalization As A Decision Procedure

The canonicity theorem reduces semantic equivalence, which quantifies over all
resolver environments, source values, variable values, and fuel values, to a finite
syntactic comparison:

```text
1. normalize left
2. normalize right
3. compare the results up to the permitted reorderings
```

Both normalizers are total deterministic Lean functions. The remaining equality
relations are currently specified as propositions. A verified executable comparator
for `operationsEqualUpToReordering` and
`completeNormalOperationsEqualUpToReordering`, or an additional sorting pass that
produces structurally equal canonical syntax, will turn normalization plus equality
up to reordering into a deterministic decision procedure for the corresponding
semantic equivalence.

Thus the current theorem supplies the semantic completeness and soundness of that
future procedure for operations with the same variable definitions. The remaining
work is computational rather than semantic: decide the finite syntactic relation
and prove the checker correct.

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
- syntactic soundness:
  `normalizeOperations_equalUpToReordering_semanticallyEquivalent` and
  `completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent`;
- semantic uniqueness:
  `normalizeOperation_uniqueUpToReordering` and
  `completeNormalizeOperation_uniqueUpToReordering`.

A common transformation proof can therefore be reduced to normal syntax:

```text
left ~= N(left) =r N(right) ~= right
```

For example, a transformation can be shown semantics-preserving by proving that its
output and input normalize to equal forms up to reordering. Conversely, unequal
normal forms provide the syntactic premise for disproving semantic equivalence by
contraposition of uniqueness.

## 2. Public Statements

The public proposition definitions live in `GraphQL/Theories/NormalForm.lean`. Their theorem
witnesses live in the corresponding uniqueness proof modules.

### Ground-Type Normalization

Ground equality ignores sibling-selection and argument ordering. It is restricted to
directive-free operations because complete normalization is responsible for Boolean
directive structure. This is the first normalization layer, not the final result: its
already-normal uniqueness theorem is reused to compare the ground bodies of complete
Boolean branches.

Already-normal reordering soundness is:

```lean
def normalOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation) : Prop :=
  operationDirectiveFree left
  -> operationDirectiveFree right
  -> operationNormal schema left
  -> operationNormal schema right
  -> operationsEqualUpToReordering left right
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
  -> operationsEqualUpToReordering
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
  -> operationsSemanticallyEquivalent schema left right
  -> operationsEqualUpToReordering left right
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
  -> operationsSemanticallyEquivalent schema left right
  -> operationsEqualUpToReordering
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
`operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering`
recovers that fact from the structural relation.

For operations that are already complete-normal, reordering soundness is
unrestricted once their variable definitions are identical:

```lean
def completeNormalOperationsEqualUpToReorderingSemanticallyEquivalent
    (schema : Schema) (left right : Operation) : Prop :=
  completeNormalOperation schema left
  -> completeNormalOperation schema right
  -> left.variableDefinitions = right.variableDefinitions
  -> completeNormalOperationsEqualUpToReordering left right
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
  -> left.variableDefinitions = right.variableDefinitions
  -> operationBoolVarsEquivalent left right
  -> completeNormalOperationsEqualUpToReordering
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
  -> operationsSemanticallyEquivalent schema left right
  -> completeNormalOperationsEqualUpToReordering left right
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
  -> operationsSemanticallyEquivalent schema left right
  -> completeNormalOperationsEqualUpToReordering
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

The ground result extends the ground-typed normal-form construction from GraphCoQL
to this project's execution model. Its difficult selection-set implication is:

```text
selectionSetsDataEquivalent schema parentType left right
  -> SelectionSetEqualUpToReordering left right
```

The proof establishes its contrapositive through two explicit witness layers:

```text
not SelectionSetEqualUpToReordering left right
  -> NormalSelectionSetDiff schema parentType left right
  -> exists responsePath,
       NormalSelectionSetDiffObservableTrace
         schema parentType left right responsePath
  -> not selectionSetsDataEquivalent schema parentType left right
```

`NormalSelectionSetDiff` identifies a structural difference in normal syntax.
`NormalSelectionSetDiffObservableTrace` fixes one concrete response path on which
that difference can be observed. The separator then constructs resolver and source
witnesses that expose the difference in execution data. Fixing one path avoids a
stronger and unnecessary global alignment invariant over unrelated response names.

The final lift is organized around these theorem surfaces:

- `normalSelectionSetDiff_of_not_equalUpToReordering` constructs the syntax witness;
- `normalSelectionSetDiffObservableTrace_of_valid_normal_diff` chooses an observable
  trace;
- `FocusedValidSeparation.lean` proves that the trace separates response data;
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
5. Ground uniqueness equates matching bodies. Bidirectional functional matching over
   noduplicated branch lists yields the branch permutation.

An absent matching branch would compare a valid nonempty ground body with the empty
selection set. Ground uniqueness would make them syntactically equal, contradicting
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

The theorem is best described as **semantic canonicity modulo reordering**. A normal
form is a **complete invariant** when two inputs have the same invariant exactly when
they belong to the same semantic equivalence class. Here the invariant is normal
syntax modulo the ordering that GraphQL execution does not observe.

This is stronger than semantics preservation alone. Preservation says normalization
does not change an operation's meaning. Uniqueness says the resulting syntax captures
all distinctions in that meaning: semantically equivalent operations cannot retain a
normal-form difference.

In term-rewriting terminology, a terminating and confluent rewrite system presenting
an equational theory is canonical or convergent. This development represents the
rewriting strategy indirectly as total Lean functions. Evaluating
`normalizeOperation` and `completeNormalizeOperation` reduces Lean lambda terms using
Lean's definitional computation rules.

The project does not define a separate GraphQL one-step reduction relation, so the
result is not a confluence theorem over arbitrary GraphQL reduction paths. It is a
canonicity theorem for the output of a deterministic functional normalizer. Equality
up to reordering remains unoriented; a verified comparator or sorting phase will make
the associated semantic decision method directly executable.

The distinction from ordinary lambda-calculus normalization is semantic. Beta/eta
conversion generates lambda-calculus equality, whereas GraphQL execution semantics is
defined independently. The uniqueness theorem proves that execution equivalence is
reified by the syntax produced through Lean computation.

## 5. Verification Status

The already-normal theorems and normalization corollaries compile without proof
holes. Axiom audits for their public theorem witnesses report only `propext`,
`Classical.choice`, and `Quot.sound`; they do not report `sorryAx`.

Run:

```sh
lake env lean Proofs/GraphQL/Theories/NormalForm/GroundTypeNormalization/Uniqueness.lean
lake env lean Tests/GraphQL/Theories/NormalForm/GroundTypeNormalization.lean
lake env lean Proofs/GraphQL/Theories/NormalForm/CompleteNormalization/Uniqueness.lean
lake env lean Tests/GraphQL/Theories/NormalForm/CompleteNormalization.lean
lake build
lake lint
```
