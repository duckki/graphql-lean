import Proofs.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.SourceObservation

/-! Query/work-history bridge regressions. Replay is a proof witness, not a query scheduler. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryObservation

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- This fixture factory need only conform for the particular work submitted in this test.
-/
def scheduler : Execution.WorkScheduler := ⟨fun _ => SourceObservation.queue⟩

/-- Local conformance follows from the checked replay source, with no law for unrelated
work.
-/
theorem conforms : scheduler.Conforms WorkScheduler.work :=
  fun _ => SourceObservation.conforms

/-- Actual root packaging allocates initial IDs and then observes the supplied finite
response group.
-/
theorem observed (response : Response)
    : (executionFromWork scheduler response WorkScheduler.work).Observes
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) true := by
  change ({ toResponse := response, pending := [{ id := "0", path := [] }], hasNext := true }
      : InitialIncrementalStreamResult) = _ ∧ _
  exact ⟨rfl, _, SourceObservation.observed, fun _ => SourceObservation.finished⟩

/-- The completed packaging observation yields a source-free witness for every initial
envelope.
-/
example (response : Response)
    : WorkObservation response WorkScheduler.work true
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) :=
  executionFromWork_observes_workHistory scheduler response WorkScheduler.work conforms
    (observed response)

/-- Dropping completion keeps the same response and work history, by the forgetting
witness.
-/
example (response : Response)
    : WorkObservation response WorkScheduler.work false
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams [[SourceObservation.events]]) :=
  (executionFromWork_observes_workHistory scheduler response WorkScheduler.work conforms
    (observed response)).forgetComplete

/-- Stopping before the first update also has a work-history witness, by the nil
observation.
-/
example (response : Response)
    : WorkObservation response WorkScheduler.work false
        (replayResponse response SourceObservation.queue.initialGroups
          SourceObservation.queue.initialStreams []) := by
  apply executionFromWork_observes_workHistory scheduler response WorkScheduler.work
    conforms
  change ({ toResponse := response, pending := [{ id := "0", path := [] }], hasNext := true }
      : InitialIncrementalStreamResult) = _ ∧ _
  exact ⟨rfl, _, .nil _, by simp⟩

/-- Finite replay retains initial data/errors and the mapper's stable initial ID, by
computation.
-/
example
    : replayResponse { data := .scalar "initial", errors := 2 }
        [WorkScheduler.node] [] [[SourceObservation.events]]
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
    : WorkObservation { data := .object [] } (.append .empty .empty) true
        (.single { data := .object [] }) := by
  have run : queryOutcome schema resolvers [] { selectionSet := [] } 5
      (.object "Query" 0) (.single { data := .object [] }) := by
    refine ⟨unavailable, ?_, ?_⟩
    all_goals
      simp [Execution.WorkScheduler.Conforms, executeQueryWithFuel, executeRootSelectionSet,
        executeRootSelectionSetCore, executeExecutionPlan, executeCollectedFields,
        collectExecutionGroups, collectFields, buildExecutionPlan, getNewDeferMap,
        Completion.pure, StateT.run, ExecutionResult.Observes,
        show rootSourceAppliesBool schema { selectionSet := [] }
          (.object "Query" 0) = true from rfl]
    · exact fun nonempty => False.elim (nonempty rfl)
    · rfl
  have witnessed := queryObservation_workHistory run
  simp [executeRootSelectionSetCore, executeExecutionPlan, executeCollectedFields,
    collectExecutionGroups, collectFields, buildExecutionPlan, getNewDeferMap,
    Completion.pure, StateT.run, selectionSetResultToResponse,
    show rootSourceAppliesBool schema { selectionSet := [] }
      (.object "Query" 0) = true from rfl] at witnessed
  exact witnessed

/-- Invalid roots retain the inherited counted error and require no contract on the unused
factory.
-/
example {result : QueryResult}
    (run
      : queryOutcome schema resolvers [] { selectionSet := [field "a"] } 5
          (.scalar "invalid") result)
    : result = .single { data := .null, errors := 1 } :=
  queryObservation_workHistory run

/-- A property derived for all independent work witnesses transfers to complete query
outcomes.
-/
example (property : QueryResult → Prop)
    (proved
      : ∀ response work result,
          WorkObservation response work true result → property result)
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : QueryResult}
    (run : queryOutcome schema resolvers variables operation fuel source result)
    : property result :=
  queryObservation_property property proved run

/-- The default-fuel entry point feeds the same bridge; no alternative fuel or scheduler
is selected.
-/
example (factory : Execution.WorkScheduler) (operation : Operation) {result : QueryResult}
    (conforming
      : rootSourceAppliesBool schema operation (.object "Query" 0) = true
        → factory.Conforms
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation [])
                (executeQueryFuelBound schema operation) (operation.rootType schema)
                (.object "Query" 0) operation.selectionSet).run
              0).1.work)
    (run
      : (executeQuery factory schema resolvers [] operation (.object "Query" 0)).Observes
          result)
    : queryObservation schema resolvers [] operation
        (executeQueryFuelBound schema operation) (.object "Query" 0) result :=
  ⟨factory, conforming, run⟩

end GraphQL.IncrementalDelivery.Tests.QueryObservation
