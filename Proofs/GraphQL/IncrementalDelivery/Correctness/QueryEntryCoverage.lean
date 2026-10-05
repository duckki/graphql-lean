import Proofs.GraphQL.IncrementalDelivery.Correctness.FieldExecutionCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryFailureReflection
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicPositions

/-! Actual root-entry comparison connects recursive value coverage to client coverage. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- Successful ordinary roots obtain prepared certificates from covered response fields
-----------------------------------------------------------------------------------------

/-- Covered actual root fields yield the full existing prepared response certificate.
Witness: root collection/plan comparison, actual initial-success identification, object
entry assembly, and ordinary reference-path uniqueness. Counted errors are unrestricted.
-/
theorem executeRoot_preparedCovers_of_fields (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (valid : SelectionSet.hasValidIncrementalArguments variables selections = true)
    (fieldsCovered
      : ResponseFieldCoverage containers schema resolvers variables fuel
          parentType source)
    (state : NodeRef) (reference : List (Name × ResponseValue)) (errors : Nat)
    (success
      : GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
          parentType source (SelectionSet.eraseIncrementalDirectives selections)
        = .ok (reference, errors))
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel parentType
            source selections).run
          state).1
      PreparedResponseCovers (.object reference)
        (selectionSetResultToResponse completed.result) completed.work containers := by
  obtain ⟨initial, count, actualSuccess, covered⟩ :=
    executeRoot_entriesCovered_of_fields containers schema resolvers variables fuel
      parentType source selections valid fieldsCovered state reference errors success
  apply EntriesCovered.to_prepared
  · simp only [actualSuccess, selectionSetResultToResponse,
      GraphQL.Execution.selectionSetResultToResponse]
    exact covered.object reference initial
  · rw [TypedResponse.value_paths, source_value_eq_positions]
    have unique := BasicPositions.rootResponse_nodup schema resolvers variables fuel parentType
      source (SelectionSet.eraseIncrementalDirectives selections) true
    simpa only [success, GraphQL.Execution.selectionSetResultToResponse] using unique

-----------------------------------------------------------------------------------------
-- The client-facing statement follows from recursive response-field comparisons
-----------------------------------------------------------------------------------------

/-- General client failure coverage follows from the query's response-field comparisons.
Witness: the actual root certificate supplies every nonbubbling ordinary reference; the
already proved mixed failure reflection supplies every bubbling reference.
`fieldsCovered` is an intermediate pure-execution obligation, not a public contract law.
-/
theorem ResponsePositionsDeliveredOrFailed_of_fields (schema : Schema)
    (operation : Operation)
    (fieldsCovered
      : ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef) variables fuel
          (source : ResolverValue ObjectRef) containers,
          operation.incrementalArgumentsValid variables
          → ResponseFieldCoverage containers schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source)
    : ResponsePositionsDeliveredOrFailed schema operation := by
  apply ResponsePositionsDeliveredOrFailed_of_nonbubblingComparison
    schema operation
  intro ObjectRef resolvers variables fuel source data errors
  dsimp only
  intro valid _ _ success containers
  exact executeRoot_preparedCovers_of_fields containers schema resolvers
    (coerceVariableValues operation variables) fuel (operation.rootType schema) source
    operation.selectionSet valid (fieldsCovered resolvers variables fuel source containers valid)
    0 data errors success

end GraphQL.IncrementalDelivery.Correctness
