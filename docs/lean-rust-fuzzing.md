# Lean–Rust differential fuzzing plan

## Executive summary

The current query-inclusion fuzzer is a useful proof-of-plumbing, not yet a
general fuzzing system. Its target-owned shared input crate has a fixed
10-object schema and renders both a seed-compatible, fragment-free model pair
and a full GraphQL pair with named fragments. Its exact 26,880-case model period has been exhausted with no
Lean/Rust disagreement; the separate named-fragment smoke corpus also completed
without a panic. The portable comparison starts Lean as a subprocess. A
reproducible native builder is now available for this fixed model corpus: it
lowers the runner to C, links it against the model's native objects, and is
selected with `--lean-oracle`. It reduced a 1,000-case oracle invocation from
1.09 s to 0.10 s on the development machine, with identical output. This is an
interim step, rather than the serialized arbitrary-IR oracle needed for direct
coverage-guided differential fuzzing.

With the native oracle, the full 26,880-case Lean/Rust sweep completed with
exact agreement. The remaining time is
therefore primarily GraphQL parsing/validation and Rust checking, rather than
the Lean runner.

The recommended end state is **verification-guided testing**: a fast Lean oracle
for the modeled subset, combined with type-directed generation and mutation of
valid GraphQL artifacts, plus Rust-only property and crash fuzzing for the parts
outside the model.

## What Cedar demonstrates

The Cedar team calls this workflow *verification-guided development*: prove
properties of a readable executable Lean model, then use differential randomized
testing (DRT) to check a production Rust implementation against it. They use
property-based testing (PBT) directly against Rust for components that have no
Lean model, such as parsers. [The paper](https://bhaktishh.github.io/papers/how-we-built-cedar.pdf)
reports that DRT and PBT found 21 bugs.

Four practices transfer directly:

1. Generate correlated inputs. Cedar first generates a schema, then conforming
   data, then conforming policies and requests. Independent random generation
   mostly exercises rejection paths; their type-directed generator found deeper
   core coverage and bugs faster.
2. Keep complementary targets. Cedar uses both mostly well-typed and deliberately
   ill-typed generators, and uses PBT where Lean is deliberately incomplete.
3. Use coverage-guided fuzzing and retain a minimized corpus. Cedar runs
   `cargo-fuzz`, saves minimized corpus cases for CI, and runs longer campaigns
   when coverage growth has flattened.
4. Make the oracle cheap. Cedar compiles/links its Lean model for testing; its
   paper reports microsecond-scale model execution. Its repository separates the
   formalization, DRT harness, and `arbitrary`-based generators.
   [Cedar paper](https://bhaktishh.github.io/papers/how-we-built-cedar.pdf),
   [Cedar specification repository](https://github.com/cedar-policy/cedar-spec).

## Current state

`fuzz/examples/differential_lean.rs` has two lanes:

- `query-inclusion`: validates each generated GraphQL pair, compares the Rust
  result with the Lean model, and exercises nested scopes; arguments; Boolean
  variables, constants, infeasible and contradictory directives; variable
  mismatch; repeated response names; interfaces; and unions.
- `query-inclusion-fragments`: validates named-fragment documents and executes
  the Rust checker without a Lean comparison, covering the model gap safely.

This is intentionally not a general `apollo-smith` export yet. The schema fixture
belongs to the query-inclusion target. `apollo-smith` should contribute
fixture-free generation/adapters, not a target schema.

To rebuild the native oracle and exhaust this finite model domain in one step:

```sh
tools/static-analysis-fuzz/run_query_inclusion_differential.sh \
  /path/to/graphql-lean
```

Replay every coverage-guided input against Lean after a fuzz campaign:

```sh
CPLUS_INCLUDE_PATH="$(xcrun --sdk macosx --show-sdk-path)/usr/include/c++/v1" \
cargo run --release --manifest-path fuzz/Cargo.toml --example differential_lean -- \
  query-inclusion --lean-oracle /path/to/query-inclusion-oracle \
  --corpus fuzz/corpus/query_inclusion
```

## Target architecture

```text
structured bytes ─► Common GraphQL fuzz IR ─► schema + right operation
                                         └► valid positive/negative left mutation
                                                        │
             ┌──────────────────────────────────────────┴─────────────────────┐
             │                                                                │
       model-supported lowering                                      full Rust document
             │                                                                │
      compiled Lean oracle                                          Rust implementation
             │                                                                │
             └──────── normalized outcome comparison ─────────────────────────┘
```

### 1. A common, typed fuzz IR

Create a small target-owned `fuzz_ir` module/crate with schema, input-value,
selection, condition, named-fragment, and operation-pair nodes. Derive it from
`arbitrary` bytes through a **type-directed builder**, not by deriving
`Arbitrary` for unrestricted ASTs.

`apollo-static-analysis::fuzzing` now provides a target-owned typed fixture IR
and both renderers. The next general builder must carry a schema environment and a current output type. It should
only emit fields valid on that type, legal fragment type conditions, variables
with compatible types, unique argument names, and finite fragment graphs. It
should deliberately choose duplicate response names and overlapping conditions;
validity does not mean triviality.

Use `apollo-smith` as an adapter and source of general GraphQL-generation
experience, but keep query-inclusion fixture configuration and pair mutations in
the target. A generic `apollo_smith::lean` exporter may lower a supported subset
and return `UnsupportedFeature`; it must never silently erase constructs.

### 2. Generate a base, then mutate directionally

Generate `(schema, right)` first. Produce `left` with a tagged mutation:

- **positive:** add a field, duplicate/merge an equivalent field, widen a type
  condition, weaken a directive clause, inline a fragment, or reorder arguments.
- **negative:** remove a required field, narrow a condition, strengthen a
  directive, change a field argument, change a recursive child, or alter a
  variable definition/support.

The mutation tag supplies an expected relation for metamorphic tests, while Lean
remains the oracle for the modeled subset. It also gives balanced, observable
distribution across positive and negative cases.

### 3. Three explicit test lanes

| Lane | Scope | Oracle |
|---|---|---|
| Model DRT | Lean-supported, fragment-free valid IR | Lean result equals Rust result |
| Rust semantic PBT | Full valid GraphQL, including named fragments | Directional/metamorphic laws and no panic |
| Parser/validator robustness | Arbitrary and near-valid bytes/documents | No panic; parser/validator round trips and stable diagnostics |

Add a fourth, optional lane when the federation comparison harness is available:
for its common subset, require all three implementations to agree and preserve
the full input on disagreement.

### 4. Replace subprocess Lean with a stable oracle boundary

The current native executable exposes a persistent, versioned stdin protocol.
`QI2 <id> <fixture-profile>` requests produce `id=true|false` responses. The
profile contains the independent choices in the current common fixture; Lean
evaluates it directly rather than regenerating it from a seed. `QI1 <seed>` and
bare command-line seeds remain available for compatibility. This removes
interpreter startup and establishes a stable request/response boundary. The
next expansion is a serialized general common IR (or a C ABI), which will
remove the fixture-specific text parser and make `cargo fuzz` practical at
Cedar-like scale.

On the Rust side, `LeanModelCase` supplies opaque `LeanRequest { id, payload }`
values to the generic runner. New targets therefore define only their case
encoding and Rust result; batching, transport, and response correlation are
shared. `QI2` is target-defined rather than a runner-level special case.

The boundary should report `true`, `false`, and structured unsupported/invalid
outcomes. Rust and Lean must normalize names, unordered arguments/input objects,
and diagnostics before comparison.

### 5. Corpus, shrinking, and CI

- Use `cargo fuzz`/libFuzzer for the long-running DRT and Rust-only targets.
- Make the byte input deterministic and retain every minimized disagreement or
  crash under `fuzz/corpus/` plus a human-readable GraphQL/Lean reproduction.
- Add the minimized corpus to fast CI; run a bounded randomized DRT job on PRs;
  run coverage-guided campaigns nightly and track coverage/time-to-new-edge.
- Promote every fixed bug to a small unit regression and retain its fuzz seed.

## Delivery plan

1. **Common IR and serializer** — introduce the target-owned typed IR, GraphQL
   renderer, and fallible Lean lowering; preserve the current fixed corpus as a
   deterministic regression target.
2. **Pair-mutation generator** — implement the balanced positive/negative
   mutation table and coverage counters; add named-fragment DAG generation to
   the Rust-only lane.
3. **Oracle service** — replace per-run `lake` startup with a compiled Lean FFI
   adapter or persistent worker; benchmark cases/second and confirm result
   parity with the current runner.
4. **Coverage-guided campaigns** — add `cargo fuzz` targets, corpus persistence,
   shrinking/reproduction output, and CI/nightly budgets.
5. **Expand formal coverage** — model named fragments (or prove a lowering to
   the fragment-free core), richer input values, and the remaining static
   analyses; migrate their DRT targets onto the same harness.

## Success criteria

- Every generated model-lane case validates and has exact Lean/Rust parity.
- The target reports mutation-family counts and maintains a balanced positive/
  negative mix.
- A minimized failing input reproduces locally with one command and is suitable
  for a unit test.
- Lean-oracle throughput is high enough for million-case nightly runs.
- The full-GraphQL Rust-only lane continuously covers named fragments, parser,
  validator, and error handling that the formal model intentionally omits.
