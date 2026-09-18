import GraphQL.IncrementalDelivery.Correctness

/-! Direct-result root execution and scheduler-independent initial data/errors.
The proof-only factoring mirrors the public branch without restoring an effect program.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Package completed pure work using the supplied factory; this is only a proof helper.
-/
def executionFromWork (scheduler : Execution.WorkScheduler)
    (response : Response) (work : Work)
    : ExecutionResult :=
  if work.size == 0 then
    .single response
  else
    let (initial, subsequent) := yieldIncrementalResults scheduler response work
    .incremental initial (batchIncrementalResults subsequent)

/-- Root execution is exactly the pure core followed by response packaging; witness: rfl.
-/
theorem executeRootSelectionSet_fromWork (scheduler : Execution.WorkScheduler)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selections : List Selection)
    : executeRootSelectionSet scheduler schema resolvers variables fuel parentType source
        selections
      = let completed :=
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            0).1
        executionFromWork scheduler (selectionSetResultToResponse completed.result)
          completed.work :=
  rfl

/-- Empty work returns an ordinary response for every factory, by reducing the branch. -/
theorem executionFromWork_silent (scheduler : Execution.WorkScheduler)
    (response : Response) (work : Work) (h : Work.size work = 0)
    : executionFromWork scheduler response work = .single response := by
  simp [executionFromWork, h]

/-- Project only initial data/errors; notice metadata intentionally remains
scheduler-owned.
-/
def initialResponse : ExecutionResult → Response
  | .single response => response
  | .incremental initial _ => initial.toResponse

/-- Packaging preserves initial data/errors; witness: both work branches reduce
identically.
-/
theorem executionFromWork_initialResponse (scheduler : Execution.WorkScheduler)
    (response : Response) (work : Work)
    : initialResponse (executionFromWork scheduler response work) = response := by
  simp only [executionFromWork]
  split
  · rfl
  · simp only [yieldIncrementalResults]
    split
    rfl

/-- The root's initial envelope comes from pure completion, by the packaging witness
above.
-/
theorem executeRootSelectionSet_initialResponse (scheduler : Execution.WorkScheduler)
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (selections : List Selection)
    : initialResponse
        (executeRootSelectionSet scheduler schema resolvers variables fuel parentType
          source selections)
      = selectionSetResultToResponse
          ((executeRootSelectionSetCore schema resolvers variables fuel parentType source
              selections).run
            0).1.result := by
  rw [executeRootSelectionSet_fromWork, executionFromWork_initialResponse]

/-- Factories cannot change query initial data/errors; witness: root agreement or
invalid-root rfl.
-/
theorem executeQueryWithFuel_initialResponse_independent
    (left right : Execution.WorkScheduler) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : initialResponse
        (executeQueryWithFuel left schema resolvers variables operation fuel source)
      = initialResponse
          (executeQueryWithFuel right schema resolvers variables operation fuel
            source) := by
  simp only [executeQueryWithFuel]
  split
  · rw [executeRootSelectionSet_initialResponse, executeRootSelectionSet_initialResponse]
  · rfl

end GraphQL.IncrementalDelivery.Correctness
