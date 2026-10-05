import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureCoverageAlgebra
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A deferred failure below a non-null object explains an ordinary nullable ancestor. -/

namespace GraphQL.IncrementalDelivery.Tests.NestedFailureCoverage
open GraphQL.IncrementalDelivery.Execution
open Correctness
open WorkQueueSemantics

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query", fields := [{ name := "user", outputType := .named "User" }]
          },
        .object
          {
            name := "User",
            fields := [{ name := "details", outputType := .nonNull (.named "Details") }]
          },
        .object
          {
            name := "Details",
            fields := [{ name := "required", outputType := .nonNull (.named "String") }]
          }
      ]
  }

private def resolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ _ =>
        match name with
        | "user" => some (.object "User" 1)
        | "details" => some (.object "Details" 2)
        | _ => none,
    resolve_argumentsEquivalent := by intros; rfl
  }

private def selections : List Selection :=
  [field "user" [field "details" [defer [field "required"]] [] (some "content")] []
    (some "viewer")]

private def completed :=
  ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
      selections).run
    0).1

private def task : SourceTask :=
  (sourceTasks [] none [] completed.work).headD
    ⟨.executionGroup [], none, .object [] (.error 1), 0⟩

/-- Ordinary non-null bubbling nulls viewer, above the deferred task's content attachment.
Witness: reduction of ordinary execution, retaining the response aliases in the result.
-/
example
    : GraphQL.Execution.executeRootSelectionSet schema resolvers [] 30 "Query"
        (.object "Query" 0) (SelectionSet.eraseIncrementalDirectives selections)
      = .ok ([("viewer", .null)], 1) := by cbv

/-- Initial execution is error-free and exposes the descendant object before its failure.
Witness: reduction of the incremental core, not an assumed initial envelope.
-/
example
    : completed.result = .ok ([("viewer", .object [("content", .object [])])], 0) := by
  cbv

/-- The retained task is below the ordinary null, so direct scope-prefix coverage fails.
Witness: the actual source payload and strict path-length difference. The null-ancestor
branch is necessary here, rather than a permissive alternative that this case could skip.
-/
example
    : task.payload = .object [.field "viewer", .field "content"] (.error 1)
      ∧ ¬task.payload.path.IsPrefix [.field "viewer"] := by
  constructor
  · cbv
  · have payload
        : task.payload = .object [.field "viewer", .field "content"] (.error 1) := by
      cbv
    rw [payload]
    intro ⟨suffix, equality⟩
    have length := congrArg List.length equality
    simp [Payload.path] at length

/-- The prepared response covers ordinary null viewer via its actual descendant failure.
Witness: source-task provenance recovers a real TaskAt, then the null-field algebra uses
the reference ancestor and the response-alias attachment. No event history is assumed.
-/
private theorem prepared_coverage (containers : Bool)
    : PreparedResponseCovers (.object [("viewer", .null)])
        (selectionSetResultToResponse completed.result) completed.work containers := by
  have member : task ∈ sourceTasks [] none [] completed.work := by
    cbv
    exact .head _
  obtain ⟨owners, known⟩ := sourceTasks_known .root [] member
  have payload
      : task.payload = .object [.field "viewer", .field "content"] (.error 1) := by
    cbv
  rw [payload] at known
  have initial : completed.result
      = .ok ([("viewer", .object [("content", .object [])])], 0) := by cbv
  rw [initial]
  exact preparedResponseCovers_nullField_of_failedTask known rfl "viewer" (by decide)
    [("viewer", .object [("content", .object [])])] 0 containers

/-- Every conforming complete observation of this query explains the ordinary null.
Witness: the actual nested execution certificate, generated ownership/cursor witnesses,
and the general decoded-failure coverage theorem. No notice path or ID is stipulated.
-/
example (createWorkQueue : Work → WorkQueue) (result : ExecutionObservation)
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers []
          { selectionSet := selections } 30 (.object "Query" 0))
    (outcome
      : queryOutcome createWorkQueue schema resolvers []
          { selectionSet := selections } 30 (.object "Query" 0) result)
    (containers : Bool)
    : result.AddressesResponsePositions containers (.object [("viewer", .null)]) := by
  have observed := queryObservation_workHistory conforms outcome
  have applies : rootSourceAppliesBool schema { selectionSet := selections }
      (.object "Query" 0 : ResolverValue Nat) = true := by cbv
  simp only [applies, ↓reduceIte] at observed
  change WorkObservation (selectionSetResultToResponse completed.result) completed.work
    true result at observed
  obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers []
    30 "Query" (.object "Query" 0) selections 0
  obtain ⟨slices, seeded, unique⟩ := executeRoot_source_positions schema
    resolvers [] 30 "Query" (.object "Query" 0) selections 0
  exact observed.addresses_reference coherent seeded unique (prepared_coverage containers)

end GraphQL.IncrementalDelivery.Tests.NestedFailureCoverage
