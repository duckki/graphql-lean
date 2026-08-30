import GraphQL.Theories.TreeSummary.ExactCases
import Tests.GraphQL.Common

/-! Adversarial exact-case scheduling benchmark.

The field scope has two disjoint abstract-type regions. For an even total `K`, each
region contains conditional fields controlled by its own disjoint `K / 2` variables.
An analytically eager operation-wide Boolean expansion has `2^K` assignments; the
branch-local scheduler should construct only `2 * 2^(K / 2)` terminal boundary cases.

The structural assertions test that separation directly. Timings measure only the
current branch-local implementation after warmup; the eager assignment count is a
complexity reference, not a measured baseline. Paper-level performance comparisons
should additionally preserve and measure an eager implementation or baseline commit,
and report the commit, Lean toolchain, build mode, and host hardware.
-/

namespace GraphQL.Benchmarks.ExactCases

open GraphQL.ConditionTree
open GraphQL.TreeSummary
open GraphQL.TreeSummary.ExactCases
open GraphQL.TreeSummary.ExactCases.Internal
open GraphQL.Tests

def indexedName (stem : String) (index : Nat) : Name :=
  s!"{stem}{index}"

def benchmarkSchema : Schema :=
  let idField := testStringFieldDefinition "id"
  {
    queryType := "Query"
    types :=
      [
        .object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "entity" "Entity"]
          },
        .interface { name := "Entity", fields := [idField] },
        .interface { name := "LeftRegion", fields := [idField] },
        .interface { name := "RightRegion", fields := [idField] },
        .object
          {
            name := "Left0"
            fields := [idField]
            interfaces := ["Entity", "LeftRegion"]
          },
        .object
          {
            name := "Left1"
            fields := [idField]
            interfaces := ["Entity", "LeftRegion"]
          },
        .object
          {
            name := "Right0"
            fields := [idField]
            interfaces := ["Entity", "RightRegion"]
          },
        .object
          {
            name := "Right1"
            fields := [idField]
            interfaces := ["Entity", "RightRegion"]
          }
      ]
  }

def variableNames (count : Nat) : List Name :=
  (List.range count).map (indexedName "enabled")

def conditionalFields (start count : Nat) : List Selection :=
  (List.range count).map
    fun offset =>
      let index := start + offset
      .field (indexedName "conditionalId" index) "id" []
        [.include (.variable (indexedName "enabled" index))] []

def benchmarkSelectionSet (booleanCount : Nat) : List Selection :=
  let perRegion := booleanCount / 2
  [
    .inlineFragment (some "LeftRegion") [] (conditionalFields 0 perRegion),
    .inlineFragment (some "RightRegion") [] (conditionalFields perRegion perRegion)
  ]

def benchmarkTree (booleanCount : Nat) : Tree :=
  ConditionTree.ofSelectionSet benchmarkSchema "Entity"
    (benchmarkSelectionSet booleanCount)

-- The leaf value records the number of active response-name groups in that case.
def workloadAlgebra : Algebra :=
  {
    Summary := Nat
    empty := 0
    field := fun _group children => children + 1
    combine := Nat.add
    join := Nat.add
  }

def decisionLeafCount : BooleanDecision α -> Nat
  | .leaf _summary => 1
  | .split _test onFalse onTrue =>
      decisionLeafCount onFalse + decisionLeafCount onTrue
  | .join left right => decisionLeafCount left + decisionLeafCount right

def decisionNodeCount : BooleanDecision α -> Nat
  | .leaf _summary => 1
  | .split _variableName onFalse onTrue =>
      1 + decisionNodeCount onFalse + decisionNodeCount onTrue
  | .join left right => 1 + decisionNodeCount left + decisionNodeCount right

def decisionLeafSummarySum : BooleanDecision Nat -> Nat
  | .leaf summary => summary
  | .split _test onFalse onTrue =>
      decisionLeafSummarySum onFalse + decisionLeafSummarySum onTrue
  | .join left right =>
      decisionLeafSummarySum left + decisionLeafSummarySum right

structure DecisionMetrics where
  nodes : Nat
  leaves : Nat
  leafGroupSum : Nat
deriving Repr

def decisionMetrics (decision : BooleanDecision Nat) : DecisionMetrics :=
  {
    nodes := decisionNodeCount decision
    leaves := decisionLeafCount decision
    leafGroupSum := decisionLeafSummarySum decision
  }

def boundaryMetrics (booleanCount : Nat) : DecisionMetrics :=
  let tree := benchmarkTree booleanCount
  let variables := variableNames booleanCount
  let decision :=
    Internal.summarizeConditionTreeDecision workloadAlgebra benchmarkSchema [] tree
      variables BooleanEnvironment.unresolved
  decisionMetrics decision

def nanosecondsToMilliseconds (nanoseconds : Nat) : Float :=
  nanoseconds.toFloat / 1000000.0

def timeMetrics (compute : Unit -> DecisionMetrics) : IO (DecisionMetrics × Nat) := do
  let started ← IO.monoNanosNow
  let metrics := compute ()
  let checksum := metrics.nodes + metrics.leaves + metrics.leafGroupSum
  if checksum == 0 then
    throw <| IO.userError "exact-cases benchmark unexpectedly produced no work"
  let finished ← IO.monoNanosNow
  pure (metrics, finished - started)

def insertSorted (value : Nat) : List Nat -> List Nat
  | [] => [value]
  | head :: tail =>
      if value ≤ head then
        value :: head :: tail
      else
        head :: insertSorted value tail

def sortNats (values : List Nat) : List Nat :=
  values.foldl (fun sorted value => insertSorted value sorted) []

structure TimingSummary where
  medianNanos : Nat
  minimumNanos : Nat
  maximumNanos : Nat
deriving Repr

def summarizeTimings (samples : List Nat) : TimingSummary :=
  let sorted := sortNats samples
  {
    medianNanos := sorted[sorted.length / 2]?.getD 0
    minimumNanos := sorted.head?.getD 0
    maximumNanos := sorted.foldl Nat.max 0
  }

def warmupCount : Nat := 3

def sampleCount : Nat := 11

def sampleMetrics (compute : Unit -> DecisionMetrics)
    : IO (DecisionMetrics × List Nat) := do
  for _ in List.range warmupCount do
    let _ ← timeMetrics compute
  let (metrics, firstElapsed) ← timeMetrics compute
  let mut samples := [firstElapsed]
  for _ in List.range (sampleCount - 1) do
    let (_, elapsed) ← timeMetrics compute
    samples := elapsed :: samples
  pure (metrics, samples)

def runScenario (booleanCount : Nat) : IO Unit := do
  if booleanCount % 2 != 0 then
    throw <| IO.userError "exact-cases benchmark requires an even Boolean count"
  let eagerAssignments := 2 ^ booleanCount
  let perRegion := booleanCount / 2
  let expectedLocalCases := 2 * 2 ^ perRegion
  let expectedNodes := 2 * expectedLocalCases - 1
  let expectedLeafGroupSum := perRegion * 2 ^ perRegion
  let (metrics, samples) ← sampleMetrics fun _ => boundaryMetrics booleanCount
  if metrics.leaves != expectedLocalCases then
    throw
    <| IO.userError
        s!"expected {expectedLocalCases} traversal leaves, got {metrics.leaves}"
  if metrics.nodes != expectedNodes then
    throw
    <| IO.userError s!"expected {expectedNodes} traversal nodes, got {metrics.nodes}"
  if metrics.leafGroupSum != expectedLeafGroupSum then
    throw
    <| IO.userError
        s!"expected leaf group sum {expectedLeafGroupSum}, got {metrics.leafGroupSum}"
  let timing := summarizeTimings samples
  IO.println
  <| s!"{booleanCount},{eagerAssignments},{expectedLocalCases},{metrics.nodes},"
      ++ s!"{metrics.leaves},{metrics.leafGroupSum},{samples.length},"
      ++ s!"{nanosecondsToMilliseconds timing.medianNanos},"
      ++ s!"{nanosecondsToMilliseconds timing.minimumNanos},"
      ++ s!"{nanosecondsToMilliseconds timing.maximumNanos}"

def run : IO Unit := do
  IO.println "# ExactCases disjoint-region Boolean benchmark"
  IO.println
    "# eager assignments are analytical; timings measure branch-local traversal only"
  IO.println
  <| "k,analytical_eager_assignments,expected_local_cases,nodes,leaves,"
      ++ "leaf_group_sum,samples,median_ms,min_ms,max_ms"
  for booleanCount in [8, 12, 16, 20] do
    runScenario booleanCount

end GraphQL.Benchmarks.ExactCases

def main : IO Unit :=
  GraphQL.Benchmarks.ExactCases.run
