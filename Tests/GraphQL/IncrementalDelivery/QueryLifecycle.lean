import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryLifecycle
import Tests.GraphQL.IncrementalDelivery.WorkScheduler

/-! Full lifecycle regressions include an independently batched termination-only response. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryLifecycle
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The public lifecycle witness has no error-freedom or syntax restriction. -/
example (schema : Schema) (operation : Operation)
    : deliveryLifecycleValid schema operation :=
  deliveryLifecycleValid_holds schema operation

def separated : List (List (List WorkEvent)) :=
  [[[WorkScheduler.value, WorkScheduler.success]], [[.workQueueTermination]]]

/-- The queue can close its last ID before a separate termination-only batch. -/
theorem separatedRun
    : GraphQL.IncrementalDelivery.WorkScheduler.AdmissibleRun
        WorkScheduler.work ⟨[WorkScheduler.node], [], separated.flatten⟩ := by
  refine ⟨WorkScheduler.events, WorkScheduler.matching, [], WorkScheduler.explained,
    WorkScheduler.terminal, ?_⟩
  exact .cons (by simp [WorkScheduler.events]) (.separate _ (.separate _ .nil))
    (.cons (tail := []) (by simp) (.separate _ .nil) .nil)

/-- Independent work admission yields the exact two-response replay witness. -/
theorem separatedObservation (response : Response)
    : WorkObservation response WorkScheduler.work true
        (replayResponse response [WorkScheduler.node] [] separated) :=
  .incremental [WorkScheduler.node] [] separated (by decide) (by simp [separated])
    (Or.inr separatedRun) (fun _ => separatedRun)

/-- Full lifecycle validity retains hasNext=true after last-ID closure, by the witness. -/
example (response : Response)
    : (replayResponse response [WorkScheduler.node] [] separated).deliveryComplete
      = true :=
  (separatedObservation response).deliveryComplete

/-- The actual mapper emits a continuation after closure and then a termination-only
response, by computation of the supplied batches.
-/
example
    : replayResponse { data := .object [] } [WorkScheduler.node] [] separated
      = .incremental
          { data := .object [], pending := [{ id := "0", path := [] }], hasNext := true }
          [
            {
              hasNext := true,
              incremental := [.object "0" []],
              completed := [{ id := "0" }]
            },
            { hasNext := false }
          ] := by rfl

/-- Failure outcomes satisfy lifecycle validity too; successful reconstruction is not
an assumption of the lifecycle theorem.
-/
example (response : Response)
    : (replayResponse response [WorkScheduler.node] []
        [[[WorkScheduler.failure, .workQueueTermination]]]).deliveryComplete
      = true := by
  apply WorkObservation.deliveryComplete
    (work := WorkScheduler.failingWork) (response := response)
  exact .incremental [WorkScheduler.node] [] _ (by decide) (by simp)
    (Or.inr WorkScheduler.failedRun) (fun _ => WorkScheduler.failedRun)

end GraphQL.IncrementalDelivery.Tests.QueryLifecycle
