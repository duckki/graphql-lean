# Porting query inclusion to Rust

This guide targets a native Rust implementation of
`GraphQL.QueryInclusion.includesBoolReference`. Read the
[query-inclusion contract](query-inclusion.md) first; use the
[execution guide](../execution.md) for field-collection background and the
[development guide](../development.md) for Lean build commands.

## Scope and comparison target

The executable source of truth is
[`GraphQL/Theories/QueryInclusion.lean`](../../GraphQL/Theories/QueryInclusion.lean)
and its dependencies. The required comparison is the final Boolean:

```text
rust_includes(schema, left, right)
  = includesBoolReference schema left right
```

State the native input domain explicitly. A useful first port accepts the modeled AST
directly, preserves the reference checker's bounded behavior, and compares small finite
inputs, including permissive regression fixtures. A production wrapper may admit only
validated inputs. Keep that wrapper separate from the checker being compared, and do
not interpret a validation failure, unsupported input, or resource limit as `false`.

The mathematical contract is `QueryInclusion.includes`: shared variable definitions
must be compatible, and every path selected by `right` must be selected by `left` under
every complete comparison assignment. Extra left paths are allowed. A path carries
concrete parent objects, response names, field names, argument syntax, and output types;
plain field-name containment is insufficient.

`IncludesBoolReferenceSound` and `IncludesBoolReferenceComplete` state the two checker
correctness directions under exactly these premises:

- `SchemaWellFormedness.schemaWellFormed schema`;
- `Validation.operationDefinitionValid schema left`;
- `Validation.operationDefinitionValid schema right`.

The checker does not establish these premises. A host validator must establish the
modeled requirements before relying on those correctness statements. Do not add a
separate assumption that field groups merge successfully to conceal a porting error.

The underlying GraphQL model targets the
[September 2025 specification](https://spec.graphql.org/September2025/).
Query inclusion itself is a project-specific relation, not a GraphQL specification
algorithm. GraphQL.js is not an oracle for this Boolean. This port does not implement
query execution, response inclusion, cache reuse, named fragments, or incremental
delivery. The optimized `includesBool` from the larger project is not present here;
the target in this branch is explicitly `includesBoolReference`.

## Executable dependency map

Port the public checker's executable dependency closure, rather than the entire executor.

| Source and symbols | Native responsibility |
| --- | --- |
| [QueryInclusion](../../GraphQL/Theories/QueryInclusion.lean): `includesBoolReference`, shared-definition compatibility | Check the root/definition guard, then require every assignment case to pass. |
| Same module: `selectionBooleanVariables`, `selectionSetBooleanVariables`, `comparisonConditionVariables`, `booleanVariableAssignments` | Find directive variables through nested selections, deduplicate their union, enumerate all Boolean assignments. |
| Same module: `selectionSetIncludesBoolWithFuel`, `selectionSetIncludesAtRuntimeBoolWithFuel` | Check every possible runtime type and recurse through composite field outputs. |
| Same module: `executableGroupsIncludeBool`, `executableGroupIncludedBool`, `executableFieldsMergedSelectionSet` | Match each right response-name group, compare its head's resolver-call identity, and merge all group members' children. |
| [Execution](../../GraphQL/Execution.lean): `collectFields`, `collectSelection`, `addExecutableGroup`, `mergeExecutableGroups` | Apply directives and runtime fragment filters; preserve ordered groups and their field sequences. |
| Same module: `lookupVariableValue?`, `inputValueBoolean?`, `selectionDirectivesAllowBool`, `doesFragmentTypeApplyBool` | Resolve modeled Boolean conditions and concrete runtime-type membership. |
| [Schema](../../GraphQL/Schema.lean): `lookupType`, `lookupField`, `getPossibleTypes`, interface-implementation Boolean helpers, `TypeRef.namedType`, `TypeRef.isCompositeBool` | Supply schema lookups, possible objects, transitive interface applicability, and output classification. |
| [Operation](../../GraphQL/Operation.lean): `VariableDefinition.equivalent`, `Argument.argumentsEquivalent`, their Boolean wrappers, selection sizes | Preserve syntactic comparisons, shared definitions, and the initial recursion bound. Input-value canonicalization comes from `Schema.lean`. |

`ResponsePath` supplies the specification, not a runtime path-enumeration algorithm.
The `decide` wrappers above perform real comparisons; replace them with native Boolean
comparisons with the same meaning. The surrounding `Decidable` instances and proof
terms do not require a native runtime representation.

## Preserve the algorithm's decisions

1. Compare roots and shared variable definitions. This syntax has only query operations,
   but keep the root guard in the comparison path. For definitions, project each side to
   names declared on the other side, then compare both projections without regard to
   declaration order. Shared names require equal raw `TypeRef` syntax and equivalent
   defaults. An absent default differs from an explicit `null` default. One-sided
   definitions are unrestricted by this compatibility check.
2. Collect variables used directly as the condition of modeled `@skip` and `@include`
   directives, including uses below fields and fragments. Deduplicate the union of both
   operations' supports. Argument-variable occurrences do not add Boolean cases.
   Enumerate every assignment, including the single empty assignment when support is
   empty. Do not replace enumeration with operation defaults or a sampled assignment.
3. For each assignment, check every object in `schema.getPossibleTypes parentType`.
   Field collection uses that runtime object's type and a unit reference; no resolver
   call is needed. A typed inline fragment filters by runtime-object membership in the
   condition's possible types. Collection keeps its execution `parentType` when entering
   a fragment; the fragment condition does not replace that lookup scope.
4. For each right group, find a left group with the same **response name**. Both groups
   must have a head. Compare head field names and syntactic argument equivalence, then
   look up the right head's field definition under the current `parentType`. A missing
   group, empty group, identity mismatch, or lookup miss fails that group check.
5. A non-composite output needs no child comparison. For a composite output, concatenate
   the child selection sets of **every** field in each matched group, preserving their
   sequence. Check all possible child objects using the same Boolean assignment and
   recurse with each child object's name as the next parent scope. Do not choose one
   representative object or restart child conditions with independent truth values.
6. Start selection-comparison fuel at `right.size + 1`. At positive fuel, a composite
   child descent uses one less unit. Inline-fragment collection is structural and does
   not consume this fuel. At zero fuel, a runtime case accepts precisely when its
   collected right groups are empty; zero fuel is not an unconditional failure.

The universal checks use ordinary empty-list truth: checking no right groups or no
possible runtime types succeeds. An uninhabited composite output can therefore make
child comparison vacuous, while the parent field's response name and resolver-call
identity must still match. Do not require a leaf descendant before recognizing a
selected parent field.

Directive interpretation also matters on permissive inputs. `@skip` rejects exactly
when its condition resolves to `some true`; `@include` accepts exactly then. An
unresolvable condition keeps a skipped selection and drops an included selection.
All directives on a selection must allow it. Enumerated comparison variables are
explicit Booleans, so operation defaults are not materialized during this checker.
Arguments remain syntax: a variable reference is compared by its name, not by evaluating
it under the current assignment or coercing it through the execution machinery.

## Native representations, identity, and lifetime

Use immutable schema/operation data for one comparison, with borrowed selections or
stable arena handles where convenient. These handles identify syntax nodes, not GraphQL
object references or response paths. A merged child context represents an ordered
sequence of selections and needs its own identity if memoized. No wire IDs, callbacks,
resolver ownership, cancellation protocol, or asynchronous cleanup is involved here.

| Collection | Meaning and representation guidance |
| --- | --- |
| Schema types and field lists | Name lookup returns the first match. Built-in scalar definitions precede explicit schema types in `allTypes`. Build immutable indexes once per schema snapshot, preserving first-match behavior or using uniqueness established by validation. |
| Possible-type lists | Objects yield their own name, unions their member sequence, interfaces the matching objects in schema order. Cache by type name within the same immutable schema. Preserve membership and the reference list for initial comparison. |
| Shared variable definitions | A pair of name indexes can find the intersection on validated, unique-name lists. Compare only that intersection, with the model's type/default equivalence. Raw duplicate lists need the original bidirectional existence checks. |
| Condition variables and assignments | Preserve the complete support set. A lazy depth-first Boolean generator can reuse one assignment buffer rather than allocate all cases. Each nested check must see the same bindings until that case completes. |
| Collected groups | Keep an ordered vector of groups plus a response-name-to-slot index. Append every field to that slot's ordered vector; its first field remains the head. Drop case-local groups after their recursive checks finish. |
| Argument lists and input objects | Arguments compare as unordered sets of name/value pairs; input objects canonicalize by field name recursively. Input lists remain ordered. Valid-input maps can replace unique-name lists; a raw port must preserve duplicate behavior instead of silently overwriting entries. |

Group key order is useful for matching collection traces, but the public comparison
target is a pure Boolean, not traversal order. Order **within** each group determines
its head and the concatenation of its child selections. Initially preserve both orders.
If replacing group iteration with unordered traversal, justify preservation of the final
Boolean separately and keep diagnostic traversal order outside that semantic claim.

For raw duplicate inputs, argument and shared-definition comparisons use bidirectional
existence, not multiplicity equality. Input-object canonicalization instead retains
every pair and the relative order of equal-name pairs when sorting. Replacing either
behavior with a map that overwrites duplicates changes the raw comparison target.

Keep value tags distinct: enum, string, variable, integer, and float constructors are
not interchangeable. Lean integers are unbounded, while modeled float literals are
strings compared exactly; converting them to `f64` would change the contract. Preserve
float text, and either represent integers exactly or declare and enforce a narrower
interchange domain. Preserve all list/non-null wrappers in shared variable types even
though runtime object lookup unwraps output types with `namedType`.

Interface reachability has its own bounded Boolean helper, with bound
`schema.types.length + 1`. Preserve it for initial raw parity. Schema well-formedness
here does not exclude interface cycles. A graph traversal with a visited set may replace
the bounded search only after establishing the same applicability results on the
declared input domain; do not introduce acyclicity as an unstated extra premise.

## Replace proof machinery and optimize in separate steps

Porting this checker does not require `executeQuery`, resolver dispatch, value
completion, non-null bubbling, execution-error counts, or argument/default coercion.
Field collection and Boolean lookup are the relevant execution dependencies. Likewise,
do not copy the proof scaffold's alternative collectors, readiness predicates, or
historical witnesses merely because they are executable Lean definitions: none is
called by the public checker. Classify helpers by their actual caller, not their directory.

Keep explicit comparison fuel in the first parity implementation. A native structural
traversal or explicit stack can later replace it if the result agrees with the reference
bound on the supported domain. Native recursion limits and integer overflow remain
separate obligations; a timeout or stack limit does not prove non-inclusion.

| Proposed optimization | Work removed and invariant to establish |
| --- | --- |
| Schema and response-group indexes | Avoid repeated linear name scans. Preserve first-match lookup, group head, and ordered accumulation on every insertion. Hash lookup bounds are representation-dependent, not a proved worst-case timing result. |
| Lazy assignment generation | Avoid retaining `2^b` environments for `b` distinct condition variables. Visit every assignment with correct parent/child correlation; restore bindings when backtracking. The number of cases remains exponential. |
| Cached possible types or canonical arguments | Avoid repeated schema scans or recursive canonicalization. Bind caches to immutable schema/AST snapshots; rebuild or invalidate them on replacement. Preserve exact value tags and duplicate policy. |
| Memoized recursive checks | Avoid repeated comparisons of the same contexts. Keys must identify schema, parent/runtime scope as applicable, both ordered selection contexts, fuel when retained, and relevant Boolean values. A hash collision or reused syntax handle must not substitute a different context. |

There is no optimized search algorithm in this branch to inherit automatically. Stronger
changes such as pruning Boolean support, grouping runtime regions, or removing fuel
need their own correspondence argument and differential checks. Additional cached state
should have a named reader, a complete key, an invalidation rule, and a measured benefit.

## Build the comparison path and validate the port

Start with the pinned Lean project and run the checks in the
[development guide](../development.md). Port small dependencies first: tagged values,
syntactic equality, schema lookup, directives, collection, and then the recursive checker.
Keep the initial implementation simple enough to compare helper outputs on a mismatch.

The repository supplies Lean regression fixtures, not a Rust crate, JSON codec, or
cross-language fuzz runner. Those are port deliverables. A comparison harness must call
the actual Lean `includesBoolReference` and the actual native checker on the same decoded
schema and operations; a Rust wrapper that delegates its answer to Lean is not a port.

For a working Lean-only smoke/replay command using existing fixtures:

```sh
lake build Tests
cat > /tmp/query-inclusion-oracle-smoke.lean <<'EOF'
import Tests.GraphQL.Theories.QueryInclusion
open GraphQL GraphQL.QueryInclusion GraphQL.Tests GraphQL.Tests.QueryInclusion
#eval includesBoolReference sampleSchema sampleHeroQuery sampleHeroQuery
#eval includesBoolReference sampleSchema sampleHeroQuery heroQueryWithExtraRootField
EOF
lake env lean /tmp/query-inclusion-oracle-smoke.lean
```

The expected answers are `true` and `false`. This checks the Lean fixture path only;
it is not yet differential evidence for Rust.

For a shared interchange format, encode constructors with explicit tags and ordered
lists as arrays, including lists of name/value pairs. Distinguish absent defaults from
explicit nulls; preserve float strings, exact integers, aliases, wrappers, and duplicate
entries. Add built-in schema scalars exactly once. Test each decoder against hand-written
AST fixtures before using a common codec to generate all expected answers. A GraphQL-text
parser, named-fragment expansion, or schema adapter introduces another boundary to test.

Use the [retained regressions](../../Tests/GraphQL/Theories/QueryInclusion.lean) as
initial cases, then add port-specific cases:

| Cases | Behavior to protect |
| --- | --- |
| Reflexivity, extra left fields, reversed operands | Inclusion direction; extra left selections are allowed. |
| Same alias with different field calls; reordered arguments and input-object fields; reordered input lists | Response-name lookup remains distinct from field identity, and syntactic equivalence has the correct ordering rules. |
| Shared default/type differences, reordered definitions, one-sided declarations, absent versus null defaults | Intersection-only compatibility, exact type wrappers, and default syntax. |
| Complementary clauses, nested conditions, contradictory parent/child guards, distinct variable names | Exhaustive correlated assignments, including variables used only in children. |
| Repeated response names with children split across multiple fields | Full ordered child merging rather than retaining only the head's subselections. |
| Interfaces, unions, covariant child outputs, and a failure visible only at a later possible object | All runtime cases and the concrete child lookup scope. |
| Empty condition support, empty possible-type lists, zero-fuel helper cases, missing lookups, cyclic interface declarations | Empty-list truth, fuel boundaries, and explicitly scoped raw-input behavior. |

Some existing fixtures exercise permissive syntax rather than witnessing all correctness
premises. Keep raw-checker agreement and valid-domain theorem tests distinguishable.
For fuzzing, generate schemas first and validate dependent operations when testing the
correctness domain. An additional raw-AST campaign can compare totalized behavior.
Record the supported numeric/size domain, generator version, seed, case count, both
answers, and any native errors. Save and minimize each mismatch as a self-contained
replay case with the runner invocation. Avoid changing both implementations together
to make a failure disappear.

Check the harness with deliberate mutations: reverse inclusion, ignore shared defaults,
keep only one possible runtime type, or discard later fields in a group. It should find
a corresponding mismatch. Benchmark separately across Boolean-support size, nesting,
same-name group width, possible-object counts, schema size, and repeated comparisons.
Report latency and allocations with input shapes and cache policy; the Lean proof does
not supply native time or memory bounds.

## Evidence and remaining obligations

The committed exercise baseline defines the final soundness/completeness propositions
without their final witness modules. Its
[support import](../../Proofs/GraphQL/Theories/QueryInclusion/Support.lean) does contain
checked bridges:

| Symbol | Evidence and scope |
| --- | --- |
| `includesBoolReference_to_selectionSetChecks` | A proved model result: acceptance supplies root/shared-definition guards and recursive checks for every environment. |
| `includes_of_complete_reference_checks` | A conditional reduction: with schema well-formedness, both validity premises, compatible roots/definitions, and checks on complete cases, selected-path inclusion follows. |
| `ResponsePath.selectionSetChecks_of_includes`, `booleanVariableAssignments_complete` | Proved model bridges supplying recursive checks from inclusion and complete environments from enumeration, respectively. The former requires schema well-formedness, both valid operations, inclusion, and environment completeness. |

These support the proof exercise. They establish no native representation relation,
codec correctness, host validation correspondence, or Rust implementation equivalence.
Native types and indexes in this guide are representation guidance; differential tests
are regression evidence. Calling the port verified would require a refinement result
for its actual implementation and admitted inputs. Preserve this distinction when
reporting successful proofs, fuzz runs, or performance improvements.
