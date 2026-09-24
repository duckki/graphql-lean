import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryStreamExistence
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Stream existence through actual query execution, including nested lists and errors. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryStreamExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- A streamed object list whose objects each contain another streamed list. -/
def nested : Operation :=
  { selectionSet := [field "users" [field "values" [] [.stream]] [.stream]] }

/-- An item error in a non-null element stops the stream and still admits a complete run.
-/
def failing : Operation := { selectionSet := [field "strict" [] [.stream]] }

/-- The nested query has a complete outcome without an externally supplied history.
Witness: the query theorem and direct reduction of its finite prepared-work shape.
-/
example
    : ∃ result, queryOutcome schema resolvers [] nested 8 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_streamOnly
  intro _
  cbv
  simp [StreamOnly]

/-- Resolver errors need not make the complete-observation relation empty. Witness:
stream-only generated work, without a zero-error or success assumption.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] failing 8 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_streamOnly
  intro _
  cbv
  simp [StreamOnly]

/-- With exhausted fuel the same query completes by the ordinary error-response branch.
Witness: its empty prepared work, not an unavailable scheduler law.
-/
example
    : ∃ result, queryOutcome schema resolvers [] nested 0 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_streamOnly
  intro _
  cbv

/-- Invalid roots require no condition on unused generated work. Witness: the impossible
root-applicability premise and the inherited ordinary error response.
-/
example : ∃ result, queryOutcome schema resolvers [] nested 8 .null result := by
  apply queryOutcome_exists_of_streamOnly
  intro applies
  cases applies

end GraphQL.IncrementalDelivery.Tests.QueryStreamExistence
