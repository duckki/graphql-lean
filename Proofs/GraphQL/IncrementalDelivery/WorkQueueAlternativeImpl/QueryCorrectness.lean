import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.QueryObservation
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryLifecycle

/-! End-to-end alternative reader correctness, inherited from the independent query
theorems through actual-factory observation. Concrete host refinement remains separate.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionObservation)

-----------------------------------------------------------------------------------------
-- Prefix safety, complete lifecycle, and zero-error reconstruction
-----------------------------------------------------------------------------------------

/-- Actual reader prefixes have valid IDs and disjoint slices. Semantic termination gives
exactly-once completion and lifecycle; zero counted errors additionally give reconstruction.
No eventual host termination or effect quiescence follows from this finite bridge.
-/
theorem ResponseStreamCursor.queryCorrectness
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (inputs : List (List GraphEvent)) (complete : Bool)
    (applies : Execution.rootSourceAppliesBool schema operation root = true)
    : let completed := queryCompletion schema resolvers variables operation fuel root
      let work := completed.work
      let response := Execution.selectionSetResultToResponse completed.result
      let (initial, cursor) := ResponseStreamCursor.buildResponse response work
      let (updates, finalCursor, _) := cursor.run inputs
      let result := ExecutionObservation.incremental initial updates
      work.size ≠ 0
      → schedule.ValidFor work
      → schedule.admissible inputs
      → (complete = true → finalCursor.queue.queue.terminated = true)
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
  obtain ⟨conforms, observed⟩ := ResponseStreamCursor.queryObservation (fun _ => schedule)
    schema resolvers variables operation fuel root inputs complete applies
    nonempty valid admitted finished
  have observedPrefix := Execution.ExecutionResult.Observes.forgetComplete observed
  refine ⟨Correctness.deliveryIDUsageValid_holds schema operation resolvers variables fuel
      root _ _ conforms observedPrefix,
    Correctness.deliverySlicesDisjoint_holds schema operation resolvers variables fuel
      root _ _ true conforms observedPrefix, ?_⟩
  intro done
  subst complete
  exact ⟨Correctness.deliveryIDsCompleteExactlyOnce_holds schema operation resolvers variables
      fuel root _ _ conforms observed,
    Correctness.deliveryLifecycleValid_holds schema operation resolvers variables fuel root
      _ _ conforms observed,
    Correctness.mergedExecutionEquivalentToBasic_holds schema operation resolvers variables
      fuel root _ _ conforms observed⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue
