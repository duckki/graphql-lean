import GraphQL.Theories.TreeSummary.ExactCases
import Tests.GraphQL.Common

/-! Adversarial exact-case scheduling benchmark.

The field scope has two disjoint abstract-type regions. For an even total `K`, each
region contains conditional fields controlled by its own disjoint `K / 2` variables.
An eager operation-wide Boolean expansion visits `2^K` assignments; a region-local
scheduler needs only `2 * 2^(K / 2)` terminal boundary cases.

The measurement goes through the public unresolved-context constructor.
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

def elapsedMilliseconds (started finished : Nat) : Float :=
  (finished - started).toFloat / 1000000.0

def timeMetrics (compute : Unit -> DecisionMetrics) : IO (DecisionMetrics × Float) := do
  let started ← IO.monoNanosNow
  let metrics := compute ()
  let checksum := metrics.nodes + metrics.leaves + metrics.leafGroupSum
  if checksum == 0 then
    throw <| IO.userError "exact-cases benchmark unexpectedly produced no work"
  let finished ← IO.monoNanosNow
  pure (metrics, elapsedMilliseconds started finished)

def runScenario (booleanCount : Nat) : IO Unit := do
  if booleanCount % 2 != 0 then
    throw <| IO.userError "exact-cases benchmark requires an even Boolean count"
  let eagerAssignments := 2 ^ booleanCount
  let perRegion := booleanCount / 2
  let expectedLocalCases := 2 * 2 ^ perRegion
  let expectedLeafGroupSum := perRegion * 2 ^ perRegion
  let (metrics, elapsedMs) ← timeMetrics fun _ => boundaryMetrics booleanCount
  if metrics.leaves != expectedLocalCases then
    throw
    <| IO.userError
        s!"expected {expectedLocalCases} traversal leaves, got {metrics.leaves}"
  if metrics.leafGroupSum != expectedLeafGroupSum then
    throw
    <| IO.userError
        s!"expected leaf group sum {expectedLeafGroupSum}, got {metrics.leafGroupSum}"
  IO.println
    s!"K={booleanCount}: eagerAssignments={eagerAssignments}, expectedLocalCases={expectedLocalCases}"
  IO.println
    s!"  traversal: nodes={metrics.nodes}, leaves={metrics.leaves}, leafGroupSum={metrics.leafGroupSum}, ms={elapsedMs}"

def run : IO Unit := do
  IO.println "ExactCases disjoint-region Boolean benchmark"
  for booleanCount in [8, 12, 16, 20] do
    runScenario booleanCount

end GraphQL.Benchmarks.ExactCases

def main : IO Unit :=
  GraphQL.Benchmarks.ExactCases.run
