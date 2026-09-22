import Proofs.GraphQL.IncrementalDelivery.Correctness.SuccessfulWork
import Tests.GraphQL.IncrementalDelivery.FailureReporting

/-! Zero-error outcomes cannot conceal actual deferred or streamed failures. -/

namespace GraphQL.IncrementalDelivery.Tests.ExecutionErrors
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

/-- The review counterexample fails for every conforming source and response grouping,
not only the originally proposed trace; witness: its actual failing task.
-/
example {result : ExecutionObservation}
    (observed
      : queryOutcome Tests.schema Tests.resolvers [] FailureReporting.op 10
          (.object "Query" 0) result)
    : result.totalErrors ≠ 0 := by
  intro zero
  have known : TaskAt
      ((executeRootSelectionSetCore Tests.schema Tests.resolvers [] 10 "Query"
          (.object "Query" 0) FailureReporting.op.selectionSet).run 0).1.work
      FailureReporting.badID [1] none (.object [] (.error 1)) := by
    rw [FailureReporting.prepared]
    exact FailureReporting.badTask
  have success := queryOutcome_tasks_succeed observed zero (by decide) known
  cases success

/-- A streamed non-null item failure inherits positivity from real execution. -/
example
    : Correctness.ExecutionErrors.Positive
        ((executeRootSelectionSetCore Tests.schema Tests.resolvers [] 10 "Query"
            (.object "Query" 0) [Tests.field "strict" [] [.stream]]).run
          0).1 :=
  Correctness.ExecutionErrors.executeRootSelectionSetCore_positive _ _ _ _ _ _ _ _

/-- Exhausted fuel also carries a positive failure count; no fuel adequacy premise is
introduced by the execution certificate.
-/
example
    : Correctness.ExecutionErrors.Positive
        ((executeRootSelectionSetCore Tests.schema Tests.resolvers [] 0 "Query"
            (.object "Query" 0) [Tests.defer [Tests.field "a"]]).run
          0).1 :=
  Correctness.ExecutionErrors.executeRootSelectionSetCore_positive _ _ _ _ _ _ _ _

/-- Completion counts survive both work and response aggregation, by actual replay. -/
example
    : 2
      ≤ (replayResponse { data := .object [] } [Tests.WorkScheduler.node] []
          [[[Tests.WorkScheduler.failure], [.workQueueTermination]]]).totalErrors := by
  exact replayResponse_failureErrors_le { data := .object [] } [Tests.WorkScheduler.node]
    [] [[[Tests.WorkScheduler.failure], [.workQueueTermination]]]

end GraphQL.IncrementalDelivery.Tests.ExecutionErrors
