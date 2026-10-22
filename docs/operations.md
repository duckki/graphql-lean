# Operations And Validation

[`GraphQL.Operation`](../GraphQL/Operation.lean) defines core executable syntax.
[`GraphQL.Validation`](../GraphQL/Validation.lean) states its validity predicates.
Named-fragment syntax and validation live in
[`GraphQL.NamedFragment`](../GraphQL/NamedFragment/).
See [schemas](schema.md) for type-system validity, [execution](execution.md) for
runtime semantics, and the [conformance summary](spec-conformance.md) for scope.

## Representation

`Operation` represents one query operation with an optional name, variable
definitions, and a selection set. A field selection stores its response name,
schema field name, arguments, directives, and children. Aliases are represented
by the response name rather than a separate syntax node. Inline fragments carry
an optional type condition and their own directives and children.

Core selections are named-fragment-free. The separate named-fragment layer adds
fragment definitions and spreads, with translation to core syntax after inlining.
Both layers represent the modeled `@skip` and `@include` directives.

Raw operations remain permissive. Validation is a proposition about syntax and
schema lookups, not a restriction embedded in constructors or a parser for source
text. Runtime input preparation is a separate execution concern.

## Operation validity

`Validation.operationDefinitionValid` combines the query kind, a composite root,
variable-definition validity, a nonempty root selection set, recursive selection
validity, field-merge compatibility, and the all-variables-used check.
`SchemaWellFormedness.schemaWellFormed` is a separate assumption; in particular,
it requires the query root to be an object.

Recursive validation checks field lookup, argument and directive validity,
variable/input-type compatibility, leaf/composite subselection shape, and fragment
applicability. Variable compatibility includes the nullable-variable exception
for a non-null default. Root and composite selection sets must be nonempty.
The modeled value checks are not a full input-coercion implementation.

## Field merging

Field-merge validation follows the declared type contexts in spec 5.3.2.
`FieldMerge.collectSubfields` collects each field's children under that field's
unwrapped return type before combining them. `FieldMerge.sameResponseShape` checks
recursive response shapes even across mutually exclusive object branches;
field names, arguments, and recursive mergeability additionally apply when the
parent types are equal or either parent is abstract.

`FieldMerge.sameTypeShape` is the type-reference helper for wrapper and leaf-type
checks. It requires matching list/non-null wrappers and equal scalar or enum
types; composite named types may differ. It is not the spec's field-level
`SameResponseShape`, which also compares child selections recursively, and it is
not a schema implementation requirement.

`Proofs.GraphQL.Validation.FieldMerge` proves the field-level merge properties;
`Proofs.GraphQL.Validation.TypeShape` supplies the type-reference shape facts.
Their regression modules are `Tests.GraphQL.Validation.FieldMerge` and
`Tests.GraphQL.Validation.TypeShape`.

## Named fragments

`NamedFragment.Validation.operationDefinitionValid` adds unique fragment names,
acyclic fragment dependencies, used-fragment checks, and validity of fragment
definitions and referenced selections. Its field-merge checker visits fragment
spreads while retaining each field's declared type context.

The all-variables-used check follows fragment spreads transitively and does not
count uses in unreferenced fragments.
`Tests.GraphQL.NamedFragment.Validation.FieldMerge` covers the fragment-aware
merge rules. The direct execution and inlining bridge are described in
[execution](execution.md#named-fragment-execution).

## Transformation assumptions

Operation validation does not guarantee validity after a query transformation.
Normalization uses separate premises such as
`NormalForm.operationFieldsValidInPossibleTypes`,
`NormalForm.operationFieldsSameOutputShape`, and type-condition feasibility. These are not
additional GraphQL validation rules. See
[normal-form validity preservation](theories/normal-form.md#validity-preservation)
for their meanings and counterexamples, and
[execution readiness](theories/execution-readiness.md) for the weaker conditions
used to establish runtime argument coercibility and composite-output inhabitance.
