import GraphQL.Theories.QueryInclusion
import Tests.GraphQL.Common

namespace GraphQL.Benchmarks.QueryInclusion

open GraphQL.QueryInclusion
open GraphQL.Tests

def indexedName (namePrefix : String) (index : Nat) : Name :=
  s!"{namePrefix}{index}"

def bitSet (value bit : Nat) : Bool :=
  value / (2 ^ bit) % 2 == 1

def benchmarkSchema (objectCount markerCount : Nat) : Schema :=
  let markerFields :=
    (List.range markerCount).map
      fun marker =>
        testStringFieldDefinition (indexedName "metric" marker)
  let entity :=
    TypeDefinition.interface
      {
        name := "Entity"
        fields :=
          [testStringFieldDefinition "id", testObjectFieldDefinition "next" "Entity"]
      }
  let markers :=
    (List.range markerCount).map
      fun marker =>
        TypeDefinition.interface
          {
            name := indexedName "Marker" marker
            fields := [testStringFieldDefinition (indexedName "metric" marker)]
          }
  let objects :=
    (List.range objectCount).map
      fun objectIndex =>
        let markerInterfaces :=
          (List.range markerCount).filterMap
            fun marker =>
              if bitSet objectIndex marker then
                some (indexedName "Marker" marker)
              else
                none
        TypeDefinition.object
          {
            name := indexedName "Object" objectIndex
            fields :=
              [testStringFieldDefinition "id", testObjectFieldDefinition "next" "Entity"]
              ++ markerFields
            interfaces := "Entity" :: markerInterfaces
          }
  {
    queryType := "Query"
    types :=
      TypeDefinition.object
          {
            name := "Query"
            fields := [testObjectFieldDefinition "entity" "Entity"]
          }
        :: entity
        :: markers
      ++ objects
  }

def booleanFields (booleanCount : Nat) : List Selection :=
  (List.range booleanCount).map
    fun index =>
      .field (indexedName "conditionalId" index) "id" []
        [.include (.variable (indexedName "enabled" index))] []

def markerFragments (markerCount : Nat) (omittedMarker : Option Nat) : List Selection :=
  (List.range markerCount).filterMap
    fun marker =>
      if omittedMarker == some marker then
        none
      else
        some
        <| .inlineFragment (some (indexedName "Marker" marker)) []
            [.field (indexedName "metric" marker) (indexedName "metric" marker) [] [] []]

def extraAliasFields (count : Nat) : List Selection :=
  (List.range count).map fun index => .field (indexedName "extra" index) "id" [] [] []

def entityScope (depth booleanCount markerCount extraAliasCount : Nat)
    (omitMarkerAtDepth : Option Nat)
    : List Selection :=
  let omittedMarker :=
    if omitMarkerAtDepth == some depth then some (markerCount - 1) else none
  let localSelections :=
    [.field "id" "id" [] [] []]
    ++ extraAliasFields extraAliasCount
    ++ booleanFields booleanCount
    ++ markerFragments markerCount omittedMarker
  match depth with
  | 0 => localSelections
  | depth + 1 =>
      localSelections
      ++ [.field "next" "next" [] []
            (entityScope depth booleanCount markerCount 0 omitMarkerAtDepth)]

def benchmarkOperation (depth booleanCount markerCount extraAliasCount : Nat)
    (omitMarkerAtDepth : Option Nat)
    : Operation :=
  {
    variableDefinitions :=
      (List.range booleanCount).map
        fun index =>
          { name := indexedName "enabled" index, typeRef := .named "Boolean" }
    selectionSet :=
      [.field "entity" "entity" [] []
        (entityScope depth booleanCount markerCount extraAliasCount omitMarkerAtDepth)]
  }

def clauseCoverageFields (booleanCount : Nat) (left : Bool) : List Selection :=
  let redundant :=
    (List.range booleanCount).map
      fun index =>
        .field "covered" "id" [] [.include (.variable (indexedName "enabled" index))] []
  let coverage :=
    if left then
      [
        .field "covered" "id" [] [.include (.variable "enabled0")] [],
        .field "covered" "id" [] [.skip (.variable "enabled0")] []
      ]
    else
      [.field "covered" "id" [] [] []]
  coverage ++ redundant

def clauseCoverageOperation (booleanCount : Nat) (left : Bool) : Operation :=
  {
    variableDefinitions :=
      (List.range booleanCount).map
        fun index =>
          { name := indexedName "enabled" index, typeRef := .named "Boolean" }
    selectionSet :=
      [.field "entity" "entity" [] [] (clauseCoverageFields booleanCount left)]
  }

def runChecker (iterations : Nat) (expected : Bool) (checker : Unit -> Bool)
    : IO Nat := do
  let mut accepted := 0
  for _ in List.range iterations do
    let actual := checker ()
    if actual != expected then
      throw
      <| IO.userError s!"query-inclusion benchmark expected {expected}, got {actual}"
    if actual then
      accepted := accepted + 1
  pure accepted

def timeChecker (label : String) (iterations : Nat) (expected : Bool)
    (checker : Unit -> Bool)
    : IO Unit := do
  let _ ← runChecker 1 expected checker
  let started ← IO.monoNanosNow
  let accepted ← runChecker iterations expected checker
  let finished ← IO.monoNanosNow
  let elapsedMs := (finished - started).toFloat / 1000000.0
  let perRunMs := elapsedMs / iterations.toFloat
  IO.println s!"{label}: {elapsedMs} ms total, {perRunMs} ms/run, accepted={accepted}"

def runScenario (label : String)
    (objectCount markerCount booleanCount depth iterations : Nat)
    : IO Unit := do
  let schema := benchmarkSchema objectCount markerCount
  let positive := benchmarkOperation depth booleanCount markerCount 3 none
  let base := benchmarkOperation depth booleanCount markerCount 0 none
  let negative := benchmarkOperation depth booleanCount markerCount 0 (some 0)
  IO.println
    s!"\n{label}: objects={objectCount}, markers={markerCount}, booleans={booleanCount}, depth={depth}"
  timeChecker "positive extra-field shortcut" iterations true
    fun _ => includesBool schema positive base
  timeChecker "negative deep missing field" iterations false
    fun _ => includesBool schema negative base
  timeChecker "reflexive shortcut" iterations true fun _ => includesBool schema base base

def runClauseCoverageScenario (booleanCount iterations : Nat) : IO Unit := do
  let schema := benchmarkSchema 1 0
  let left := clauseCoverageOperation booleanCount true
  let right := clauseCoverageOperation booleanCount false
  let checker := fun _ => includesBool schema left right
  IO.println s!"\nsymbolic clause coverage: booleans={booleanCount}"
  timeChecker "complementary clauses" iterations true checker

def run : IO Unit := do
  runScenario "wide type regions" 96 3 0 0 500
  runScenario "Boolean conditions" 48 3 7 0 200
  runScenario "nested response scopes" 12 2 2 2 100
  runClauseCoverageScenario 18 500

end GraphQL.Benchmarks.QueryInclusion

def main : IO Unit :=
  GraphQL.Benchmarks.QueryInclusion.run
