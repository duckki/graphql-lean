import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization
import Tests.GraphQL.IncrementalDelivery.WorkScheduler
import Tests.GraphQL.IncrementalDelivery.HistoryScheduling
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Maximal sources retain alternative outputs and realize successful/failed histories. -/

namespace GraphQL.IncrementalDelivery.Tests.Realization
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

/-- One conforming source admits both owner choices from the same initialization;
witness: maximal-source conformance and the two independent history witnesses.
-/
example
    : (specificationSource HistoryScheduling.shared
        [HistoryScheduling.left, HistoryScheduling.right] []).Conforms
        HistoryScheduling.shared
      ∧ ∀ node ∈ [HistoryScheduling.left, HistoryScheduling.right],
          (specificationSource HistoryScheduling.shared
            [
              HistoryScheduling.left,
              HistoryScheduling.right
            ] []).workEventStream.admissible
            [[HistoryScheduling.value node]] := by
  exact ⟨specificationSource_conforms HistoryScheduling.initialized,
    fun node member => (HistoryScheduling.nextOwner node member).2.2.2⟩

/-- A complete successful history has a real conforming factory, with no manually
implemented replay source; witness: work-observation realization.
-/
example (response : Response)
    : ∃ scheduler : Execution.WorkScheduler,
        scheduler.Conforms WorkScheduler.work
        ∧ (executionFromWork scheduler response WorkScheduler.work).Observes
            (replayResponse response [WorkScheduler.node] []
              [[[WorkScheduler.value, WorkScheduler.success, .workQueueTermination]]])
            true := by
  apply WorkObservation.realizes
  exact .incremental _ _ _ (by decide) (by simp)
    (Or.inr WorkScheduler.completedRun) (fun _ => WorkScheduler.completedRun)

/-- Realizability includes failure and error notifications; witness: the existing
failure-cut run transported through the maximal source and actual mapper.
-/
example (response : Response)
    : ∃ scheduler : Execution.WorkScheduler,
        scheduler.Conforms WorkScheduler.failingWork
        ∧ (executionFromWork scheduler response WorkScheduler.failingWork).Observes
            (replayResponse response [WorkScheduler.node] []
              [[[WorkScheduler.failure, .workQueueTermination]]]) true := by
  apply WorkObservation.realizes
  exact .incremental _ _ _ (by decide) (by simp)
    (Or.inr WorkScheduler.failedRun) (fun _ => WorkScheduler.failedRun)

/-- Truncating an explained output sequence retains only earlier failure cuts;
witness: the general prefix theorem, not a new cancellation assumption.
-/
example {work groups streams head tail matching failures}
    (explained : Explains work groups streams (head ++ tail) matching failures)
    : Explains work groups streams head matching
        (failures.filter (fun entry => entry.1 ≤ head.length)) :=
  explained.prefix

/-- Invalid-root observations are realizable without a usable queue; witness: the
query/history equivalence's ordinary error branch.
-/
example
    : queryOutcome schema resolvers [] { selectionSet := [field "a"] } 5
        (.scalar "invalid") (.single { data := .null, errors := 1 }) := by
  apply queryObservation_iff_workHistory.mpr
  rfl

/-- The ordinary empty query has a complete observation without any work history;
witness: query/history equivalence and the zero-work constructor.
-/
example
    : queryOutcome schema resolvers [] { selectionSet := [] } 5
        (.object "Query" 0) (.single { data := .object [] }) := by
  apply queryObservation_iff_workHistory.mpr
  simp [executeRootSelectionSetCore, executeExecutionPlan, executeCollectedFields,
    collectExecutionGroups, collectFields, buildExecutionPlan, getNewDeferMap,
    Completion.pure, StateT.run, selectionSetResultToResponse,
    show rootSourceAppliesBool schema { selectionSet := [] }
      (.object "Query" 0) = true from rfl]
  exact .single rfl

end GraphQL.IncrementalDelivery.Tests.Realization
