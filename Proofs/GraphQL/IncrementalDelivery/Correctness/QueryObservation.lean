import Proofs.GraphQL.IncrementalDelivery.Correctness.RootExecution
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceObservation

/-! Query observations reduced to independent work-history witnesses.
Finite replay is proof-only and consumes supplied input groups; it is not a scheduler
or a new execution entry point. Every permitted response grouping remains explicit.
-/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution

/-- Replay initial ID allocation and the actual batching mapper on a supplied finite
history.
-/
def replayResponse (response : Response)
    (initialGroups initialStreams : List DeliveryNode)
    (groups : List (List (List WorkQueueEvent)))
    : ExecutionObservation :=
  let (pending, ids) :=
    (getPendingEntry (m := StateM IDState) initialGroups initialStreams ensureID).run {}
  let updates : StateM IDState (List IncrementalStreamUpdateResult) :=
    groups.mapM
      fun available => do
        let results ← available.mapM mapWorkEventBatch
        return combineIncrementalResults results
  .incremental { toResponse := response, pending, hasNext := true } (updates.run ids).1

/-- A source-free proof witness for the ordinary branch or one admitted incremental
observation. The history accounts for work, while replay determines the wire result
independently. QueryObservation proves soundness; QueryRealization proves the converse
using the maximal source. Neither direction assumes wire correctness.
-/
inductive WorkObservation (response : Response) (work : Work) (complete : Bool)
    : ExecutionObservation → Prop where
  | single (empty : work.size = 0)
    : WorkObservation response work complete (.single response)
  | incremental (initialGroups initialStreams : List DeliveryNode)
    (groups : List (List (List WorkQueueEvent)))
    (nonempty : work.size ≠ 0) (batches : ∀ group ∈ groups, group ≠ [])
    (admitted
      : WorkQueueSemantics.AdmissiblePrefix work
          ⟨initialGroups, initialStreams, groups.flatten⟩
        ∨ WorkQueueSemantics.AdmissibleRun work
            ⟨initialGroups, initialStreams, groups.flatten⟩)
    (finished
      : complete = true
        → WorkQueueSemantics.AdmissibleRun work
            ⟨initialGroups, initialStreams, groups.flatten⟩)
    : WorkObservation response work complete
        (replayResponse response initialGroups initialStreams groups)

/-- Forgetting completion retains the same work history and batching, dropping only
termination.
-/
theorem WorkObservation.forgetComplete {response : Response} {work : Work}
    {complete : Bool} {result : ExecutionObservation}
    (observed : WorkObservation response work complete result)
    : WorkObservation response work false result := by
  cases observed with
  | single empty => exact .single empty
  | incremental groups streams batches nonempty admittedGroups admitted _ =>
      exact .incremental groups streams batches nonempty admittedGroups admitted (by simp)

/-- Work packaging exposes either its ordinary response or the source-free work witness.
Witness: split the empty-work branch, then extract actual inputs through source
conformance.
-/
theorem executionFromWork_observes_workHistory
    (scheduler : (Execution.Work → Execution.WorkQueue)) (response : Response)
    (work : Work) (conforms : (work.size ≠ 0 → (scheduler work).Conforms work))
    {result : ExecutionObservation} {complete : Bool}
    (observed : (executionFromWork scheduler response work).Observes result complete)
    : WorkObservation response work complete result := by
  by_cases empty : work.size = 0
  · rw [executionFromWork_silent _ _ _ empty] at observed
    cases result with
    | single value =>
        have equal : response = value := observed
        subst value
        exact .single empty
    | incremental initial updates => cases observed
  · have sourceConforms := conforms empty
    cases allocated
          : (getPendingEntry (m := StateM IDState)
              (scheduler work).initialGroups
              (scheduler work).initialStreams ensureID).run
              {} with
    | mk pending ids =>
        simp only [executionFromWork, empty, beq_iff_eq, ↓reduceIte,
          yieldIncrementalResults, initializeIncrementalResponse, allocated] at observed
        cases result with
        | single value => cases observed
        | incremental initial updates =>
            obtain ⟨rfl, final, run, terminated⟩ := observed
            obtain ⟨groups, nonempty, _, admitted, outputs, terminal⟩ :=
              (scheduler work).observes_workHistory work ids sourceConforms run
            have witnessed := WorkObservation.incremental (response := response) (work := work)
              (complete := complete) (scheduler work).initialGroups
              (scheduler work).initialStreams groups empty nonempty admitted
              (fun finished => terminal.mp (terminated finished))
            simpa only [replayResponse, allocated, outputs,
              ResponseEventStream.mapInputs, batchIncrementalResults,
              mapIncrementalWorkEventsToResponseEvent] using witnessed

/-- Root observations retain the actual core response/work, by the checked packaging
equation.
-/
theorem executeRootSelectionSet_observes_workHistory
    (scheduler : (Execution.Work → Execution.WorkQueue)) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    {result : ExecutionObservation} {complete : Bool}
    (conforms
      : let work :=
          ((executeRootSelectionSetCore schema resolvers variables fuel
              parentType source selections).run
            0).1.work
        work.size ≠ 0 → (scheduler work).Conforms work)
    (observed
      : (executeRootSelectionSet scheduler schema resolvers variables fuel parentType
          source selections).Observes
          result complete)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType
            source selections).run
          0).1
      WorkObservation (selectionSetResultToResponse completed.result) completed.work
        complete result := by
  rw [executeRootSelectionSet_fromWork] at observed
  exact executionFromWork_observes_workHistory scheduler _ _ conforms observed

/-- Query observations reduce to the actual prepared root work, or the inherited
invalid-root error. Witness: retain the operation-local conformance premise and apply the
root-history theorem.
-/
theorem queryObservation_workHistory {createWorkQueue : Work → WorkQueue}
    {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : ExecutionObservation} {complete : Bool}
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers variables operation fuel
          source)
    (observed
      : queryObservation createWorkQueue schema resolvers variables operation fuel source
          result complete)
    : if rootSourceAppliesBool schema operation source then
        let completed :=
          ((executeRootSelectionSetCore schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source operation.selectionSet).run
            0).1
        WorkObservation (selectionSetResultToResponse completed.result) completed.work
          complete result
      else
        result = .single { data := .null, errors := 1 } := by
  split
  · rename_i applies
    simp only [queryObservation, executeQueryWithFuel, applies, ↓reduceIte] at observed
    exact executeRootSelectionSet_observes_workHistory createWorkQueue schema resolvers _ fuel
      (operation.rootType schema) source operation.selectionSet (conforms applies) observed
  · rename_i invalid
    simp only [queryObservation, executeQueryWithFuel, invalid] at observed
    cases result with
    | single response => exact congrArg ExecutionObservation.single observed.symm
    | incremental initial updates => cases observed

/-- Work-history correctness transfers to every query observation, including the
invalid-root branch. Witness: the query-history theorem and the single zero-work witness
for the counted root error.
-/
theorem queryObservation_property {createWorkQueue : Work → WorkQueue}
    {schema : Schema} {resolvers : Resolvers ObjectRef}
    {variables : VariableValues} {operation : Operation} {fuel : Nat}
    {source : ResolverValue ObjectRef} {result : ExecutionObservation} {complete : Bool}
    (property : ExecutionObservation → Prop)
    (workProperty
      : ∀ response work result,
          WorkObservation response work complete result → property result)
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers variables operation fuel
          source)
    (observed
      : queryObservation createWorkQueue schema resolvers variables operation fuel source
          result complete)
    : property result := by
  have witnessed := queryObservation_workHistory conforms observed
  split at witnessed
  · exact workProperty _ _ _ witnessed
  · subst result
    exact workProperty _ .empty _ (.single rfl)

end GraphQL.IncrementalDelivery.Correctness
