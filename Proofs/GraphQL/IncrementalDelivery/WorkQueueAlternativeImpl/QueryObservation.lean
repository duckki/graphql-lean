import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ResponseReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.Conformance
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorObservation
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! Actual alternative reader replay supplies the existing query observation and conformance
premises. The same executed work, source, inputs, and completion flag witness both sides;
no response-equivalence or native-runtime premise is added to the source contract.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue

private theorem executionFromWork_congr (left right : Work → Execution.WorkQueue)
    (response : Execution.Response) (work : Work) (same : left work = right work)
    : Correctness.executionFromWork left response work
      = Correctness.executionFromWork right response work := by
  simp only [Correctness.executionFromWork]
  split
  · rfl
  · simp only [Execution.yieldIncrementalResults, same]

-----------------------------------------------------------------------------------------
-- Actual reader prefixes and complete query outcomes
-----------------------------------------------------------------------------------------

/-- The current reader observes the actual alternative query factory and its derived work.
Witness: exact reader replay and factory equality transfer the reference observation bridge.
-/
theorem ResponseStreamCursor.queryObservation
    (sources : Work → EventSource (List GraphEvent)) (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef) (variables : Execution.VariableValues)
    (operation : Operation) (fuel : Nat) (root : Execution.ResolverValue ObjectRef)
    (inputs : List (List GraphEvent)) (complete : Bool)
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.buildResponse response work
      let (updates, finalCursor, _) := cursor.run inputs
      let createWorkQueue := fun work => createWorkQueueForSchedule work (sources work)
      work.size ≠ 0
      → (sources work).ValidFor work
      → (sources work).admissible inputs
      → (complete = true → finalCursor.queue.queue.terminated = true)
      → queryWorkQueueConforms createWorkQueue schema resolvers variables
          operation fuel root
        ∧ queryObservation createWorkQueue schema resolvers variables
            operation fuel root (.incremental initial updates) complete := by
  dsimp only
  intro nonempty valid admitted finished
  have generated : ReferenceWorkQueue.ExecutedWork
      (queryCompletion schema resolvers variables operation fuel root).work :=
    ⟨ObjectRef, schema, resolvers, _, fuel, operation.rootType schema, root,
      operation.selectionSet, rfl⟩
  obtain ⟨matching, started, _⟩ := valid.2.2.2.2 inputs admitted
  have factory := createWorkQueueForSchedule_eq_reference _ _ generated nonempty valid
  have referenceFinished : complete = true
      → ((ReferenceWorkQueue.ResponseStreamCursor.initialize
            (Execution.selectionSetResultToResponse
              (queryCompletion schema resolvers variables operation fuel root).result)
            (queryCompletion schema resolvers variables operation fuel root).work).2.run
          inputs).2.queue.terminated = true := by
    intro done
    rw [← ResponseStreamCursor.run_buildResponse_terminated _ _ inputs generated matching started]
    exact finished done
  have observed := ReferenceWorkQueue.ResponseStreamCursor.queryObservation sources schema
    resolvers variables operation fuel root inputs complete applies nonempty valid admitted
    referenceFinished
  refine ⟨
    fun _ _ => createWorkQueueForScheduleConforms_holds _ _ generated
      ((Execution.Work.isEmpty_eq_false _).mpr nonempty) valid,
    ?_
  ⟩
  have observation := observed.2
  simp only [GraphQL.IncrementalDelivery.queryObservation, Execution.executeQueryWithFuel, applies,
    ↓reduceIte, Correctness.executeRootSelectionSet_fromWork] at observation ⊢
  rw [executionFromWork_congr _
      (fun work => ReferenceWorkQueue.createWorkQueueForSchedule work (sources work)) _ _ factory,
    ResponseStreamCursor.buildResponse_initial,
    ResponseStreamCursor.run_buildResponse_updates _ _ inputs generated matching started]
  exact observation

/-- An admitted terminated reader is a complete query outcome, not merely a closed reader. -/
theorem ResponseStreamCursor.queryOutcome
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (inputs : List (List GraphEvent))
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.buildResponse response work
      let (updates, finalCursor, _) := cursor.run inputs
      work.size ≠ 0
      → schedule.ValidFor work
      → schedule.admissible inputs
      → finalCursor.queue.queue.terminated = true
      → queryOutcome (fun work => createWorkQueueForSchedule work schedule) schema
          resolvers variables operation fuel root (.incremental initial updates) := by
  dsimp only
  intro nonempty valid admitted finished
  exact (ResponseStreamCursor.queryObservation (fun _ => schedule) schema resolvers variables
    operation fuel root inputs true applies nonempty valid admitted (fun _ => finished)).2

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
