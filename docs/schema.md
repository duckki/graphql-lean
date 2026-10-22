# Schemas And Well-Formedness

[`GraphQL.Schema`](../GraphQL/Schema.lean) defines raw type-system syntax and
lookup helpers. [`GraphQL.SchemaWellFormedness`](../GraphQL/SchemaWellFormedness.lean)
states the schema validity assumptions used by proofs. The target is the
[GraphQL September 2025 Edition](https://spec.graphql.org/September2025/).
See [operations](operations.md) for executable syntax and validation,
[execution](execution.md) for runtime behavior, and the
[conformance summary](spec-conformance.md) for coverage and exclusions.

## Representation

`Schema` stores the query root name and user-defined types. `Schema.allTypes`
adds the built-in scalars for lookup. `TypeDefinition` distinguishes scalars,
objects, interfaces, unions, enums, and input objects; `TypeRef` represents named,
list, and non-null references.

Object and interface definitions carry field definitions and lists of declared
interfaces. Field definitions carry output types and argument definitions. Input
value definitions carry input types and optional constant defaults.

Raw syntax remains permissive. Invalid references, duplicate declarations,
self-implementation, and cycles are representable. Lookup and finite reachability
helpers do not require a well-formedness proof.

## Well-formedness

`SchemaWellFormedness.schemaWellFormed` combines name uniqueness, a query object
root, per-type well-formedness, input-object cycle checks, possible-object lookup
invariants, and compatible field definitions on possible runtime objects.
`WellFormedSchema` bundles a schema with this proof; it does not change the raw
representation or executable lookup functions.

Per-type predicates keep field and argument validity separate from type
membership and inheritance. For example, `fieldDefinitionWellFormed` checks the
output type and argument definitions, while `fieldDefinitionImplements` checks
return covariance and compatibility with an inherited field's arguments.

## Interface implementation

`possibleObjectFieldDefinitionsImplement` requires fields declared on a parent
type to have compatible definitions on every possible object type. Return types
are related by `Schema.outputTypeSubtype`, following the spec's
[interface implementation rules](https://spec.graphql.org/September2025/#sec-Objects).
An object field returning `String!` can implement an interface field returning
`String`; strengthening is also permitted recursively within lists.

`interfacesIncludeInherited` expresses `IsValidImplementation` step 1: every
declared interface's own interfaces must also appear in the implementing type's
declaration list. Both objects and interfaces satisfy this closure condition.
Interfaces must additionally exclude their own name from their implementation
list. Together, these rules exclude every nonempty inheritance cycle.

Runtime reachability remains separate from declaration validity. Its Boolean and
propositional helpers follow transitive inheritance even on cyclic or dangling
raw schemas; they do not silently complete an implementation list for validation.

Schema covariance is distinct from operation
[field-merge compatibility](operations.md#field-merging). Schema well-formedness
alone does not ensure that grounding abstract returns preserves operation
validity. The additional normalization premises are documented in
[normal forms](theories/normal-form.md#validity-preservation).

## Input-object cycles

`inputObjectCircularReferencesValid` combines two checks. Singular non-null input
fields must not form an unbroken cycle; nullable and list fields break that chain.
Separately, `inputDefaultExpansionAcyclic` rejects cycles reached by following
defaults for absent input-object fields. These checks do not prohibit finite
recursive supplied values through nullable or list fields. Runtime default
materialization is described in [execution](execution.md#inputs-and-defaults).

## Proofs and regressions

- `Proofs.GraphQL.SchemaWellFormedness.FieldLookup` derives field lookup and output
  type facts from well-formedness.
- `Proofs.GraphQL.SchemaWellFormedness.PossibleTypes` supplies possible-object and
  covariance bridges used by execution and transformation proofs.
- `Proofs.GraphQL.SchemaWellFormedness.InterfaceInheritance` proves finite raw
  reachability correspondence, explicit ancestor membership, and cycle exclusion.
  `interfaceTypeWellFormed_noInheritanceCycle` requires an initial declared edge
  before a return path, since raw reachability itself is reflexive.
- `Tests.GraphQL.SchemaWellFormedness.InterfaceValidation` covers valid
  inheritance, missing ancestors, self-implementation, cycles, and invalid targets.
  `Tests.GraphQL.SchemaWellFormedness.InterfaceInheritance` separately checks
  permissive raw reachability.
- `Tests.GraphQL.SchemaWellFormedness.OutputCovariance` covers scalar and list
  strengthening, invalid weakening, and list-shape mismatch.
