import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorObservation
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryLifecycle

/-! End-to-end cursor correctness by reuse of the independent public query theorems.
The observation bridge supplies their premises; no new response law is imposed on inputs.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionObservation)

-----------------------------------------------------------------------------------------
-- Safety for admitted prefixes, lifecycle and reconstruction for completed runs
-----------------------------------------------------------------------------------------

/-- Actual cursor runs inherit ID safety and disjoint slices; terminated runs have
exactly-once ID completion and a valid lifecycle, and zero-error runs reconstruct basic
execution. Witness: `implementationCorrect_holds` supplies the observation;
`deliveryIDUsageValid_holds`, `deliverySlicesDisjoint_holds`,
`deliveryIDsCompleteExactlyOnce_holds`, `deliveryLifecycleValid_holds`, and
`mergedExecutionEquivalentToBasic_holds` in `Correctness` provide the conclusions.
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
      let (initial, cursor) := ResponseStreamCursor.initialize response work
      let (updates, finalCursor) := cursor.run inputs
      let result := ExecutionObservation.incremental initial updates
      work.size ≠ 0
      → schedule.ValidFor work
      → schedule.admissible inputs
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
  obtain ⟨conforms, observed⟩ := implementationCorrect_holds schema operation
    resolvers variables fuel root schedule _ complete
    ⟨applies, nonempty, valid, inputs, admitted, finished, rfl⟩
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

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
