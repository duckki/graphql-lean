import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.Conformance
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (ExecutionObservation)

-----------------------------------------------------------------------------------------
-- The reference queue supplies the existing work contract
-----------------------------------------------------------------------------------------

/-- Executed work needs no separate node-coherence or initialization assumption.
Witness: specialize the public conformance theorem, which derives both from execution.
-/
theorem createWorkQueueForSchedule_conforms_executed
    (source : EventSource (List GraphEvent))
    (work : Execution.Work) (generated : ExecutedWork work)
    (valid : source.ValidFor work)
    (nonempty : work.size ≠ 0)
    : (createWorkQueueForSchedule work source).Conforms work :=
  createWorkQueueForScheduleConforms_holds work source generated nonempty valid

-----------------------------------------------------------------------------------------
-- Canonical response replay includes the cursor's singleton response grouping
-----------------------------------------------------------------------------------------

/-- Grouping each upstream batch separately leaves the spec mapper unchanged.
Witness: a singleton response combination is the identity, with identical ID threading.
-/
private theorem map_singleton_batches (batches : List (List Execution.WorkQueueEvent))
    : ((batches.map (fun batch => [batch])).mapM
          (fun available => do
            let results ← available.mapM Execution.mapWorkEventBatch
            pure (Execution.combineIncrementalResults results))
        : StateM Execution.IDState (List Execution.IncrementalStreamUpdateResult))
      = batches.mapM Execution.mapWorkEventBatch := by
  rw [List.mapM_map]
  congr 1

/-- Actual cursor outputs equal canonical response replay with one update per emitted
queue batch. Witness: shared replay agreement and the singleton batching identity.
-/
theorem ResponseStreamCursor.observation_eq_replay (response : Execution.Response)
    (work : Execution.Work) (inputs : List (List GraphEvent))
    : let queue := State.initialize (Work.fromExecution work)
      let (initial, cursor) := ResponseStreamCursor.initialize response work
      ExecutionObservation.incremental initial (cursor.run inputs).1
      = Correctness.replayResponse response queue.initialGroups queue.initialStreams
          ((queue.runNormalized inputs).2.map (fun batch => [batch])) := by
  have outputs : ((ResponseStreamCursor.initialize response work).2.run inputs).1 =
      ((((State.initialize (Work.fromExecution work)).runNormalized inputs).2.mapM
        Execution.mapWorkEventBatch).run
        ((Execution.getPendingEntry (m := StateM Execution.IDState)
          (State.initialize (Work.fromExecution work)).initialGroups
          (State.initialize (Work.fromExecution work)).initialStreams Execution.ensureID).run {}).2).1 :=
    (ResponseStreamCursor.run_initialize response work inputs).1
  simp only [Correctness.replayResponse, map_singleton_batches]
  rw [ResponseStreamCursor.initialize_eq] at outputs ⊢
  cases allocated
        : (Execution.getPendingEntry (m := StateM Execution.IDState)
            (State.initialize (Work.fromExecution work)).initialGroups
            (State.initialize (Work.fromExecution work)).initialStreams
            Execution.ensureID).run
            {} with
  | mk pending ids =>
      simp only [allocated] at outputs ⊢
      exact congrArg (ExecutionObservation.incremental _) outputs

-----------------------------------------------------------------------------------------
-- Cursor prefixes and terminal runs inherit independent work accounting
-----------------------------------------------------------------------------------------

/-- The cursor replays the reference queue constructor's response stream, not merely an
equivalent history under another constructor. Witness: exact response replay and admission
of the supplied host inputs in the reference adapter, including concrete termination.
-/
theorem ResponseStreamCursor.executionObservation
    (response : Execution.Response) (work : Execution.Work)
    (source : EventSource (List GraphEvent)) (inputs : List (List GraphEvent))
    (complete : Bool) (nonempty : work.size ≠ 0)
    (conforms : (createWorkQueueForSchedule work source).Conforms work)
    (admitted : source.admissible inputs)
    (finished
      : complete = true
        → ((ResponseStreamCursor.initialize response work).2.run
            inputs).2.queue.terminated
          = true)
    : let (initial, cursor) := ResponseStreamCursor.initialize response work
      (Correctness.executionFromWork (fun work => createWorkQueueForSchedule work source)
        response work).Observes
        (.incremental initial (cursor.run inputs).1) complete := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let batches := (queue.runNormalized inputs).2
  have replay : ExecutionObservation.incremental
      (ResponseStreamCursor.initialize response work).1
      ((ResponseStreamCursor.initialize response work).2.run inputs).1 =
      Correctness.replayResponse response queue.initialGroups queue.initialStreams
        (batches.map (fun batch => [batch])) :=
    ResponseStreamCursor.observation_eq_replay response work inputs
  rw [replay]
  have flattened : (batches.map (fun batch => [batch])).flatten = batches := by
    change (batches.flatMap fun batch => [batch]) = batches
    simp
  apply Correctness.executionFromWork_observes_replay _ _ _ _ complete nonempty conforms
  · simp
  · rw [flattened]
    exact ⟨inputs, admitted, rfl⟩
  · intro done
    rw [flattened]
    refine ⟨inputs, admitted, rfl, ?_⟩
    change (queue.runNormalized inputs).1.terminated = true
    rw [← (ResponseStreamCursor.run_initialize response work inputs).2]
    exact finished done

/-- Every admitted cursor prefix is an independently accounted work observation.
Witness: the actual adapter's conformance, exact cursor replay, and concrete termination.
No response-correctness property is assumed; unfinished observations remain permitted.
-/
theorem ResponseStreamCursor.workObservation
    (response : Execution.Response) (work : Execution.Work)
    (source : EventSource (List GraphEvent)) (inputs : List (List GraphEvent))
    (complete : Bool) (nonempty : work.size ≠ 0)
    (conforms : (createWorkQueueForSchedule work source).Conforms work)
    (admitted : source.admissible inputs)
    (finished
      : complete = true
        → (((ResponseStreamCursor.initialize response work).2.run
              inputs).2.queue).terminated
          = true)
    : let (initial, cursor) := ResponseStreamCursor.initialize response work
      Correctness.WorkObservation response work complete
        (.incremental initial (cursor.run inputs).1) := by
  let queue := State.initialize (Work.fromExecution work)
  let batches := (queue.runNormalized inputs).2
  have allowed : (createWorkQueueForSchedule work source).workEventStream.admissible batches :=
    ⟨inputs, admitted, rfl⟩
  have accounted := conforms.2.2.1 batches allowed
  have terminal : complete = true →
      AdmissibleRun work ⟨queue.initialGroups, queue.initialStreams, batches⟩ := by
    intro done
    apply ((conforms.2.2.2 batches).mp ?_).2
    refine ⟨inputs, admitted, rfl, ?_⟩
    change ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.terminated = true
    rw [← (ResponseStreamCursor.run_initialize response work inputs).2]
    exact finished done
  change Correctness.WorkObservation response work complete
    (.incremental (ResponseStreamCursor.initialize response work).1
      ((ResponseStreamCursor.initialize response work).2.run inputs).1)
  have replay : ExecutionObservation.incremental
      (ResponseStreamCursor.initialize response work).1
      ((ResponseStreamCursor.initialize response work).2.run inputs).1 =
      Correctness.replayResponse response queue.initialGroups queue.initialStreams
        (batches.map (fun batch => [batch])) :=
    ResponseStreamCursor.observation_eq_replay response work inputs
  have flattened : (batches.map (fun batch => [batch])).flatten = batches := by
    change (batches.flatMap fun batch => [batch]) = batches
    simp
  rw [replay]
  apply Correctness.WorkObservation.incremental _ _ _ nonempty
  · simp
  · rw [flattened]
    exact accounted
  · intro done
    rw [flattened]
    exact terminal done

-----------------------------------------------------------------------------------------
-- Reuse all public query-correctness theorems without restating their conclusions
-----------------------------------------------------------------------------------------

/-- Cursor execution supplies both query-local conformance and an observation of the
actual reference queue constructor. Witness: generated-work conformance and exact cursor
replay; terminal observations additionally use concrete queue termination.
-/
theorem ResponseStreamCursor.queryObservation
    (sources : Execution.Work → EventSource (List GraphEvent)) (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef) (variables : Execution.VariableValues)
    (operation : Operation) (fuel : Nat) (root : Execution.ResolverValue ObjectRef)
    (inputs : List (List GraphEvent)) (complete : Bool)
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.initialize response work
      let (updates, finalCursor) := cursor.run inputs
      let createWorkQueue := fun work => createWorkQueueForSchedule work (sources work)
      work.size ≠ 0
      → (sources work).ValidFor work
      → (sources work).admissible inputs
      → (complete = true → finalCursor.queue.terminated = true)
      → queryWorkQueueConforms createWorkQueue schema resolvers variables
          operation fuel root
        ∧ queryObservation createWorkQueue schema resolvers variables
            operation fuel root (.incremental initial updates) complete := by
  dsimp only
  intro nonempty valid admitted finished
  have generated : ExecutedWork
      (queryCompletion schema resolvers variables operation fuel root).work :=
    ⟨ObjectRef, schema, resolvers, _, fuel, operation.rootType schema, root,
      operation.selectionSet, rfl⟩
  have conforms := createWorkQueueForSchedule_conforms_executed (sources _) _ generated
    valid nonempty
  refine ⟨fun _ _ => conforms, ?_⟩
  simp only [GraphQL.IncrementalDelivery.queryObservation, Execution.executeQueryWithFuel, applies,
    ↓reduceIte, Correctness.executeRootSelectionSet_fromWork]
  exact ResponseStreamCursor.executionObservation _ _ _ inputs complete nonempty
    conforms admitted finished

/-- Public implementation correctness follows for one supplied source.
Witness: unpack the admitted input history and use the cursor bridge with a constant
source family. The optional cursor packages exactly the predicate's queue/publisher replay;
both prefix and complete observations use the same execution-derived work.
-/
theorem implementationCorrect_holds (schema : Schema) (operation : Operation)
    : ImplementationCorrect schema operation := by
  intro ObjectRef resolvers variables fuel root schedule result complete
  dsimp only
  intro observed
  rcases observed with ⟨applies, nonempty, valid, inputs, admitted, finished, same⟩
  subst result
  exact ResponseStreamCursor.queryObservation (fun _ => schedule) schema resolvers variables
    operation fuel root inputs complete applies nonempty valid admitted finished

/-- A terminated admitted cursor run is a complete public query outcome.
Witness: specialize `implementationCorrect_holds` to `complete = true`.
The termination premise refers to the concrete queue, not the host source's finished flag.
-/
theorem ResponseStreamCursor.queryOutcome
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (inputs : List (List GraphEvent))
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.initialize response work
      let (updates, finalCursor) := cursor.run inputs
      work.size ≠ 0
      → schedule.ValidFor work
      → schedule.admissible inputs
      → finalCursor.queue.terminated = true
      → queryOutcome (fun work => createWorkQueueForSchedule work schedule)
          schema resolvers variables operation fuel root
          (.incremental initial updates) := by
  dsimp only
  intro nonempty valid admitted finished
  exact (implementationCorrect_holds schema operation resolvers variables fuel root
    schedule _ true
    ⟨applies, nonempty, valid, inputs, admitted, (fun _ => finished), rfl⟩).2

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
