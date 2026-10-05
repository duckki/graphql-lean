import Proofs.GraphQL.IncrementalDelivery.Correctness.ContextFailureCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Public client coverage for root defers containing nullable and bubbling errors. -/

namespace GraphQL.IncrementalDelivery.Tests.ContextFailureCoverage
open Correctness

private def nullableBody : List Selection :=
  [field "user" [field "required"], field "users" [field "required"], field "fail"]

private def strictBody : List Selection :=
  [field "a", field "required", field "strict"]

/-- Every conforming complete observation covers this nullable-error defer's reference.
Witness: the syntax-restricted public theorem, not a hand-picked implementation replay.
The quantified proposition includes all resolver environments and explicit fuel values.
-/
example
    : ResponsePositionsDeliveredOrFailed schema
        { selectionSet := [defer nullableBody] } := by
  apply ResponsePositionsDeliveredOrFailed_of_singleDefer schema _ nullableBody none rfl
  cbv

/-- Deferred non-null failure also satisfies the public client-coverage proposition.
Witness: the same universal theorem; the fixture's default resolvers bubble at required,
while the statement allows arbitrary resolvers rather than assuming that outcome.
-/
example
    : ResponsePositionsDeliveredOrFailed schema
        { selectionSet := [defer strictBody (some "strict")] } := by
  apply ResponsePositionsDeliveredOrFailed_of_singleDefer schema _ strictBody
    (some (.string "strict")) rfl
  cbv

end GraphQL.IncrementalDelivery.Tests.ContextFailureCoverage
