import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorCorrectness

namespace GraphQL.IncrementalDelivery.Tests.ReferenceCorrectness
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (ExecutionObservation)

-----------------------------------------------------------------------------------------
-- The shared representation retains the two publication boundaries
-----------------------------------------------------------------------------------------

/-- The raw queue emits the canonical execution event type without a conversion. -/
example (queue : State) (batch : List GraphEvent)
    : State × List Execution.WorkQueueEvent :=
  queue.handleGraphEvents batch

/-- Reference tasks store the canonical execution-group value directly. -/
example (result : TaskResult) : Execution.ExecutionGroupValue := result.value

/-- Stream payloads require no representation conversion. -/
example (item : StreamItem) : Execution.StreamItemValue := item.value

/-- Public conformance derives node coherence and initialization from executed work. -/
example (sources : Execution.Work → EventSource (List GraphEvent))
    (work : Execution.Work) (generated : ExecutedWork work)
    (valid : (sources work).ValidFor work)
    (nonempty : work.size ≠ 0)
    : (createWorkQueueForSchedule work (sources work)).Conforms work :=
  createWorkQueueForScheduleConforms_holds work (sources work) generated nonempty valid

/-- Finite replay can be consumed online, including silent input batches. -/
example (cursor : ResponseStreamCursor) (batch : List GraphEvent)
    (rest : List (List GraphEvent))
    : cursor.run (batch :: rest)
      = let next := cursor.step batch
        let last := next.2.run rest
        (next.1.toList ++ last.1, last.2) :=
  cursor.run_cons batch rest

private def group : Execution.DeliveryNode := { key := 0, path := [] }
private def deepGroup : Execution.DeliveryNode := { key := 1, path := [.field "obj"] }

private def sharedWork : Execution.Work :=
  .executionGroup [{ node := group }, { node := deepGroup }] [.field "obj"]
    (.ok ([("x", .scalar "X")], 0)) .empty

private def sharedSuccess : GraphEvent :=
  .taskSuccess (.executionGroup [])
    {
      value :=
        {
          deliveryGroups := [group, deepGroup]
          path := [.field "obj"]
          data := [("x", .scalar "X")]
        }
    }

private def response : Execution.Response := { data := .object [("obj", .object [])] }

private def sharedCompletion
    : Execution.Completion (List (Name × Execution.ResponseValue)) :=
  { result := .ok ([("obj", .object [])], 0), work := sharedWork }

/-- The finite runner and optional cursor share initialization, replay, and termination.
Witness: the definitionally equal projections proved by `replayIncrementalResponse_eq_cursor`.
-/
example (completed : Execution.Completion (List (Name × Execution.ResponseValue)))
    (inputs : List (List GraphEvent))
    : replayIncrementalResponse completed inputs
      = let response := Execution.selectionSetResultToResponse completed.result
        let (initial, cursor) := ResponseStreamCursor.initialize response completed.work
        let (updates, finalCursor) := cursor.run inputs
        (initial, updates, finalCursor.queue.terminated) :=
  replayIncrementalResponse_eq_cursor completed inputs

/-- A silent host batch emits no update and leaves this outstanding task pending. -/
example : ((ResponseStreamCursor.initialize response sharedWork).2.step []).1 = none := by
  rfl

/-- Silent finite replay retains outstanding work without emitting an update. -/
example : (replayIncrementalResponse sharedCompletion [[]]).2 = ([], false) := by
  rfl

/-- The finite runner selects the deepest open owner, closes both IDs, and terminates. -/
example
    : (replayIncrementalResponse sharedCompletion [[], [sharedSuccess]]).2
      = (
        [{
          hasNext := false
          incremental := [.object "1" [("x", .scalar "X")]]
          completed := [{ id := "0" }, { id := "1" }]
        }],
        true
      ) := by
  rfl

/-- Empty streams retain a pending/completed lifecycle without an item patch. -/
example
    : (replayIncrementalResponse { result := .ok ([], 0), work := .stream group [] }
        [[.streamSuccess group]]).2
      = ([{ hasNext := false, completed := [{ id := "0" }] }], true) := by
  rfl

-----------------------------------------------------------------------------------------
-- Existing correctness witnesses apply to executable cursor outputs
-----------------------------------------------------------------------------------------

/-- Query conformance checks exactly the queue constructed for the execution-derived work.
Witness: unfold the predicate, retaining ordinary/invalid-root guards and no global law.
-/
example (createWorkQueue : Execution.Work → Execution.WorkQueue) (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef) (variables : Execution.VariableValues)
    (operation : Operation) (fuel : Nat) (root : Execution.ResolverValue ObjectRef)
    : queryWorkQueueConforms createWorkQueue schema resolvers variables
        operation fuel root
      ↔ let work := (queryCompletion schema resolvers variables operation fuel root).work
        Execution.rootSourceAppliesBool schema operation root = true
        → work.size ≠ 0
        → (createWorkQueue work).Conforms work :=
  Iff.rfl

/-- Separating conformance from observation preserves the former combined assumption.
Witness: unfold both definitions; the existential queue constructor and its local contract agree.
-/
example (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (result : ExecutionObservation)
    (complete : Bool)
    : (∃ createWorkQueue,
        queryWorkQueueConforms createWorkQueue schema resolvers variables
          operation fuel root
        ∧ queryObservation createWorkQueue schema resolvers variables
            operation fuel root result complete)
      ↔ ∃ createWorkQueue : Execution.Work → Execution.WorkQueue,
          (Execution.rootSourceAppliesBool schema operation root = true
            → let prepared := Execution.coerceVariableValues operation variables
              let completed :=
                ((Execution.executeRootSelectionSetCore schema resolvers prepared fuel
                    (operation.rootType schema) root operation.selectionSet).run
                  0).1
              completed.work.size ≠ 0
              → (createWorkQueue completed.work).Conforms completed.work)
          ∧ (Execution.executeQueryWithFuel createWorkQueue schema resolvers variables
              operation fuel root).Observes
              result complete :=
  Iff.rfl

/-- The public observation predicate is exactly observation of the supplied query queue constructor.
Witness: definitional equality; no root-work extraction or conformance is hidden here.
-/
example (createWorkQueue : Execution.Work → Execution.WorkQueue) (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef) (variables : Execution.VariableValues)
    (operation : Operation) (fuel : Nat) (root : Execution.ResolverValue ObjectRef)
    (result : ExecutionObservation) (complete : Bool)
    : queryObservation createWorkQueue schema resolvers variables operation
        fuel root result complete
      ↔ (Execution.executeQueryWithFuel createWorkQueue schema resolvers variables
          operation fuel root).Observes
          result complete :=
  Iff.rfl

/-- The public bridge has a witness for every schema and operation.
Witness: implementation correctness, with all run premises inside the statement.
-/
example (schema : Schema) (operation : Operation)
    : ImplementationCorrect schema operation :=
  implementationCorrect_holds schema operation

/-- The observation-based statement is equivalent to the former input-wise cursor law.
Witness: introduce or unpack the admitted input history; cursor and direct replay agree.
-/
example (schema : Schema) (operation : Operation)
    : ImplementationCorrect schema operation
      ↔ ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
          (variables : Execution.VariableValues) (fuel : Nat)
          (root : Execution.ResolverValue ObjectRef)
          (schedule : EventSource (List GraphEvent)) (inputs : List (List GraphEvent))
          (complete : Bool),
          let completed := queryCompletion schema resolvers variables operation fuel root
          let work := completed.work
          let response := Execution.selectionSetResultToResponse completed.result
          let (initial, cursor) := ResponseStreamCursor.initialize response work
          let (updates, finalCursor) := cursor.run inputs
          let createWorkQueue := fun work => createWorkQueueForSchedule work schedule
          Execution.rootSourceAppliesBool schema operation root = true
          → work.size ≠ 0
          → schedule.ValidFor work
          → schedule.admissible inputs
          → (complete = true → finalCursor.queue.terminated = true)
          → queryWorkQueueConforms createWorkQueue schema resolvers variables
              operation fuel root
            ∧ queryObservation createWorkQueue schema resolvers variables
                operation fuel root (.incremental initial updates) complete := by
  constructor
  · intro holds ObjectRef resolvers variables fuel root schedule inputs complete
    dsimp only
    intro applies nonempty valid admitted finished
    exact holds resolvers variables fuel root schedule _ complete
      ⟨applies, nonempty, valid, inputs, admitted, finished, rfl⟩
  · intro holds ObjectRef resolvers variables fuel root schedule result complete
    dsimp only
    intro observed
    rcases observed with ⟨applies, nonempty, valid, inputs, admitted, finished, same⟩
    subst result
    exact holds resolvers variables fuel root schedule inputs complete
      applies nonempty valid admitted finished

/-- Prefix observations require no termination premise.
Witness: the public statement at `complete = false` makes the finish implication vacuous.
-/
example (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (inputs : List (List GraphEvent))
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let (initial, updates, _) := replayIncrementalResponse completed inputs
      completed.work.size ≠ 0 → schedule.ValidFor completed.work
      → schedule.admissible inputs
      → queryObservation
          (fun work => createWorkQueueForSchedule work schedule) schema resolvers
          variables operation fuel root (.incremental initial updates) := by
  dsimp only
  intro nonempty valid admitted
  exact (implementationCorrect_holds schema operation resolvers variables fuel
          root schedule _ false
          ⟨
            applies,
            nonempty,
            valid,
            inputs,
            admitted,
            (by intro impossible; cases impossible),
            rfl
          ⟩).2

/-- Concrete termination yields the exact `queryOutcome` premise of complete correctness.
Witness: the named complete-run wrapper, with no host-finished or initialization premise.
-/
example (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (inputs : List (List GraphEvent))
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let (initial, cursor) :=
        ResponseStreamCursor.initialize
          (Execution.selectionSetResultToResponse completed.result) completed.work
      let (updates, finalCursor) := cursor.run inputs
      completed.work.size ≠ 0 → schedule.ValidFor completed.work
      → schedule.admissible inputs → finalCursor.queue.terminated = true
      → queryOutcome (fun work => createWorkQueueForSchedule work schedule)
          schema resolvers variables operation fuel root (.incremental initial updates) :=
  ResponseStreamCursor.queryOutcome schema resolvers variables operation fuel root
    schedule inputs applies

/-- Under the existing work/source premises, cursor prefixes have safe IDs and disjoint
slices; terminated cursors have valid lifecycles and zero-error response reconstruction.
Witness: the reusable end-to-end theorem; its proof no longer lives in this regression.
-/
example (sources : Execution.Work → EventSource (List GraphEvent))
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (inputs : List (List GraphEvent))
    (complete : Bool)
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.initialize response work
      let (updates, finalCursor) := cursor.run inputs
      let result := ExecutionObservation.incremental initial updates
      work.size ≠ 0 → (sources work).ValidFor work → (sources work).admissible inputs
      → (complete = true → finalCursor.queue.terminated = true)
      → result.idUsageValid
        ∧ (∃ slices, result.DeliversSlices true slices ∧ slices.flatten.Nodup)
        ∧ (complete = true
            → result.idsCompleteExactlyOnce
              ∧ result.lifecycleValid = true
              ∧ (result.totalErrors = 0
                  → ∃ response,
                      Execution.mergeExecutionObservation result = some response
                      ∧ GraphQL.Execution.Response.semanticEquivalent response
                          (GraphQL.Execution.executeQueryWithFuel schema resolvers
                            variables operation.eraseIncrementalDirectives fuel
                            root))) := by
  dsimp only
  intro nonempty valid admitted finished
  exact ResponseStreamCursor.queryCorrectness schema resolvers variables operation fuel root
    (sources _) inputs complete applies nonempty valid admitted finished

end GraphQL.IncrementalDelivery.Tests.ReferenceCorrectness
