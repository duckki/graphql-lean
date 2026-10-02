import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryLifecycle
import Tests.GraphQL.IncrementalDelivery.WorkQueueSemantics

/-! Full lifecycle regressions include an independently batched termination-only response. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryLifecycle
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The public lifecycle witness has no error-freedom or syntax restriction. -/
example (schema : Schema) (operation : Operation)
    : deliveryLifecycleValid schema operation :=
  deliveryLifecycleValid_holds schema operation

def separated : List (List (List WorkQueueEvent)) :=
  [[[WorkQueueSemantics.value, WorkQueueSemantics.success]], [[.workQueueTermination]]]

/-- The queue can close its last ID before a separate termination-only batch. -/
theorem separatedRun
    : GraphQL.IncrementalDelivery.WorkQueueSemantics.AdmissibleRun
        WorkQueueSemantics.work ⟨[WorkQueueSemantics.node], [], separated.flatten⟩ := by
  refine ⟨
    WorkQueueSemantics.events,
    WorkQueueSemantics.matching,
    [],
    WorkQueueSemantics.explained,
    WorkQueueSemantics.terminal,
    ?_
  ⟩
  exact .cons (by simp [WorkQueueSemantics.events]) (.separate _ (.separate _ .nil))
    (.cons (tail := []) (by simp) (.separate _ .nil) .nil)

/-- Independent work admission yields the exact two-response replay witness. -/
theorem separatedObservation (response : Response)
    : WorkObservation response WorkQueueSemantics.work true
        (replayResponse response [WorkQueueSemantics.node] [] separated) :=
  .incremental [WorkQueueSemantics.node] [] separated (by decide) (by simp [separated])
    (Or.inr separatedRun) (fun _ => separatedRun)

/-- Full lifecycle validity retains hasNext=true after last-ID closure, by the witness. -/
example (response : Response)
    : (replayResponse response [WorkQueueSemantics.node] [] separated).lifecycleValid
      = true :=
  (separatedObservation response).lifecycleValid

/-- The actual mapper emits a continuation after closure and then a termination-only
response, by computation of the supplied batches.
-/
example
    : replayResponse { data := .object [] } [WorkQueueSemantics.node] [] separated
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
    : (replayResponse response [WorkQueueSemantics.node] []
        [[[WorkQueueSemantics.failure, .workQueueTermination]]]).lifecycleValid
      = true := by
  apply WorkObservation.lifecycleValid
    (work := WorkQueueSemantics.failingWork) (response := response)
  exact .incremental [WorkQueueSemantics.node] [] _ (by decide) (by simp)
    (Or.inr WorkQueueSemantics.failedRun) (fun _ => WorkQueueSemantics.failedRun)

end GraphQL.IncrementalDelivery.Tests.QueryLifecycle
