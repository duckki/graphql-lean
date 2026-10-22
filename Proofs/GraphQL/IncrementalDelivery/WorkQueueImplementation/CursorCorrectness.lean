import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CursorObservation
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryLifecycle
import Proofs.GraphQL.IncrementalDelivery.Correctness.RecursiveValueCoverage
import Proofs.GraphQL.IncrementalDelivery.Semantics.WorkSize

/-! End-to-end cursor correctness by reuse of the independent public query theorems.
The observation bridge supplies their premises; no new response law is imposed on inputs.
-/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionObservation)

-----------------------------------------------------------------------------------------
-- Safety for admitted prefixes, lifecycle and reconstruction for completed runs
-----------------------------------------------------------------------------------------

set_option maxHeartbeats 800000 in
/-- Actual cursor runs inherit ID safety and disjoint slices; terminated runs have
exactly-once ID completion and a valid lifecycle, and zero-error runs reconstruct basic
execution. Witness: the checked cursor observation bridge supplies the premises;
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
  obtain ⟨conforms, observed⟩ := ResponseStreamCursor.queryObservation
    (fun _ => schedule) schema resolvers variables operation fuel root inputs complete
    applies nonempty valid admitted finished
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

-----------------------------------------------------------------------------------------
-- Complete reference observations inherit client-facing coverage despite later errors
-----------------------------------------------------------------------------------------

/-- A complete admitted reference observation addresses every ordinary response position.
Witness: `implementationCorrect_holds` supplies query-local queue conformance and actual
observation; `ResponsePositionsDeliveredOrFailed_holds` then supplies delivered data
or a decoded failure scope. Only initial errors are excluded; later errors are allowed.
The statement uses the shared replay predicate and does not require the optional cursor.
-/
theorem queryScheduleMatches_addressesResponsePositions
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variables : Execution.VariableValues) (operation : Operation) (fuel : Nat)
    (root : Execution.ResolverValue ObjectRef) (schedule : EventSource (List GraphEvent))
    (result : ExecutionObservation)
    (validArguments : operation.incrementalArgumentsValid variables)
    (observed
      : queryScheduleMatches schema resolvers variables operation fuel root schedule
          result true)
    (initialErrorFree : result.initialErrors = 0)
    : ∀ containers,
        result.AddressesResponsePositions containers
          (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
            operation.eraseIncrementalDirectives fuel root).data := by
  obtain ⟨conforms, outcome⟩ := implementationCorrect_holds schema operation resolvers variables
    fuel root schedule result true observed
  exact Correctness.ResponsePositionsDeliveredOrFailed_holds schema operation resolvers
    variables fuel root _ result validArguments conforms outcome initialErrorFree

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
