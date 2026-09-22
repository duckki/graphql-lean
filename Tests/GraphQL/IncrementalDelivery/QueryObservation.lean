import Proofs.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.SourceObservation

/-! Query/work-history bridge regressions. Replay is a proof witness, not a query scheduler. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryObservation

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- This fixture queue constructor need only conform for the particular work submitted in this test.
-/
def scheduler : Execution.Work → Execution.WorkQueue := fun _ => SourceObservation.queue

/-- Local conformance follows from the checked replay source, with no law for unrelated
work.
-/
theorem conforms
    : (WorkQueueSemantics.work.size ≠ 0
        → (scheduler WorkQueueSemantics.work).Conforms WorkQueueSemantics.work) :=
  fun _ => SourceObservation.conforms

/-- Actual root packaging allocates initial IDs and then observes the supplied finite
response group.
-/
theorem observed (response : Response)
    : (executionFromWork scheduler response WorkQueueSemantics.work).Observes
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) true := by
  change ({ toResponse := response, pending := [{ id := "0", path := [] }], hasNext := true }
      : InitialIncrementalStreamResult) = _ ∧ _
  exact ⟨rfl, _, SourceObservation.observed, fun _ => SourceObservation.finished⟩

/-- The completed packaging observation yields a source-free witness for every initial
envelope.
-/
example (response : Response)
    : WorkObservation response WorkQueueSemantics.work true
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) :=
  executionFromWork_observes_workHistory scheduler response WorkQueueSemantics.work
    conforms (observed response)

/-- Dropping completion keeps the same response and work history, by the forgetting
witness.
-/
example (response : Response)
    : WorkObservation response WorkQueueSemantics.work false
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) :=
  (executionFromWork_observes_workHistory scheduler response WorkQueueSemantics.work
    conforms (observed response)).forgetComplete

/-- Stopping before the first update also has a work-history witness, by the nil
observation.
-/
example (response : Response)
    : WorkObservation response WorkQueueSemantics.work false
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams []) := by
  apply executionFromWork_observes_workHistory scheduler response WorkQueueSemantics.work
    conforms
  change ({ toResponse := response, pending := [{ id := "0", path := [] }], hasNext := true }
      : InitialIncrementalStreamResult) = _ ∧ _
  exact ⟨rfl, _, .nil _, by simp⟩

/-- Finite replay retains initial data/errors and the mapper's stable initial ID, by
computation.
-/
example
    : replayResponse { data := .scalar "initial", errors := 2 }
        [WorkQueueSemantics.node] [] [[SourceObservation.events]]
      = .incremental
          {
            data := .scalar "initial",
            errors := 2,
            pending := [{ id := "0", path := [] }],
            hasNext := true
          }
          [{
            hasNext := false,
            incremental := [.object "0" []],
            completed := [{ id := "0" }]
          }] := by
  rfl

/-- Root packaging with empty work never needs a usable source; its history witness is the
single case.
-/
example (response : Response)
    : WorkObservation response .empty true (.single response) := by
  apply executionFromWork_observes_workHistory unavailable response .empty
  · intro nonempty
    exact False.elim (nonempty rfl)
  · rfl

/-- The actual empty query reaches a zero-work witness through the operation-local query
theorem.
-/
example
    : WorkObservation { data := .object [] } (.combine .empty .empty) true
        (.single { data := .object [] }) := by
  have run : queryWorkQueueConforms unavailable schema resolvers [] { selectionSet := [] } 5
        (.object "Query" 0)
      ∧ queryOutcome unavailable schema resolvers [] { selectionSet := [] } 5
        (.object "Query" 0) (.single { data := .object [] }) := by
    refine ⟨?_, ?_⟩
    all_goals
      simp [queryWorkQueueConforms, queryOutcome, queryObservation,
        queryCompletion,
        executeQueryWithFuel, executeRootSelectionSet,
        executeRootSelectionSetCore, executeExecutionPlan, executeCollectedFields,
        collectExecutionGroups, collectFields, buildExecutionPlan, getNewDeferMap,
        Completion.pure, StateT.run, ExecutionResult.Observes,
        show rootSourceAppliesBool schema { selectionSet := [] }
          (.object "Query" 0) = true from rfl]
    · exact fun nonempty => False.elim (nonempty rfl)
    · rfl
  have witnessed := queryObservation_workHistory run.1 run.2
  simp [executeRootSelectionSetCore, executeExecutionPlan, executeCollectedFields,
    collectExecutionGroups, collectFields, buildExecutionPlan, getNewDeferMap,
    Completion.pure, StateT.run, selectionSetResultToResponse,
    show rootSourceAppliesBool schema { selectionSet := [] }
      (.object "Query" 0) = true from rfl] at witnessed
  exact witnessed

/-- Invalid roots retain the inherited counted error and require no contract on the unused
queue constructor.
-/
example {createWorkQueue : Work → WorkQueue} {result : ExecutionObservation}
    (run
      : queryOutcome createWorkQueue schema resolvers [] { selectionSet := [field "a"] } 5
          (.scalar "invalid") result)
    : result = .single { data := .null, errors := 1 } :=
  queryObservation_workHistory (by intro applies; cases applies) run

/-- A property derived for all independent work witnesses transfers to complete query
outcomes.
-/
example (property : ExecutionObservation → Prop)
    (proved
      : ∀ response work result,
          WorkObservation response work true result → property result)
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : ExecutionObservation}
    {createWorkQueue : Work → WorkQueue}
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers variables operation fuel
          source)
    (run
      : queryOutcome createWorkQueue schema resolvers variables operation fuel source
          result)
    : property result :=
  queryObservation_property property proved conforms run

/-- The default-fuel entry point feeds the same bridge; no alternative fuel or scheduler
is selected.
-/
example (createWorkQueue : (Execution.Work → Execution.WorkQueue)) (operation : Operation)
    {result : ExecutionObservation}
    (run
      : (executeQuery createWorkQueue schema resolvers [] operation
          (.object "Query" 0)).Observes
          result)
    : queryObservation createWorkQueue schema resolvers [] operation
        (executeQueryFuelBound schema operation) (.object "Query" 0) result :=
  run

end GraphQL.IncrementalDelivery.Tests.QueryObservation
