import Proofs.GraphQL.IncrementalDelivery.Correctness.OrdinaryFailureReflection

/-! Ordinary root-null coverage and the remaining nonbubbling query comparison. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open OrdinaryFailures

-----------------------------------------------------------------------------------------
-- Actual query observations whose ordinary reference is null
-----------------------------------------------------------------------------------------

/-- Every complete conforming mixed-query observation addresses an ordinary null root.
Witness: actual query history, generated ownership/cursor certificates, and mixed root
failure reflection. The initial-error premise is the public coverage statement's premise;
it excludes invalid roots, not errors discovered in subsequent work.
-/
theorem queryOutcome_addresses_nullReference (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef) (createWorkQueue : Work → WorkQueue)
    (result : ExecutionObservation)
    (valid : operation.incrementalArgumentsValid variables)
    (conforms
      : queryWorkQueueConforms createWorkQueue schema resolvers variables operation
          fuel source)
    (outcome
      : queryOutcome createWorkQueue schema resolvers variables operation fuel source
          result)
    (initialZero : result.initialErrors = 0)
    (referenceNull
      : (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
          operation.eraseIncrementalDirectives fuel source).data
        = .null)
    (containers : Bool)
    : result.AddressesResponsePositions containers .null := by
  have observed := queryObservation_workHistory conforms outcome
  split at observed
  · rename_i applies
    have ordinary : GraphQL.Execution.executeQueryWithFuel schema resolvers variables
        operation.eraseIncrementalDirectives fuel source
        = GraphQL.Execution.selectionSetResultToResponse
            (GraphQL.Execution.executeRootSelectionSet schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source (SelectionSet.eraseIncrementalDirectives operation.selectionSet)) := by
      have root : GraphQL.Execution.rootSourceAppliesBool schema
          operation.eraseIncrementalDirectives source = true := applies
      simp only [GraphQL.Execution.executeQueryWithFuel, root, ↓reduceIte]
      rfl
    rw [ordinary] at referenceNull
    cases reference
          : GraphQL.Execution.executeRootSelectionSet schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source (SelectionSet.eraseIncrementalDirectives operation.selectionSet) with
    | error errors =>
        obtain ⟨paths, coherent⟩ := Semantics.MixedOwnerPaths.executeRoot_owners schema resolvers
          (coerceVariableValues operation variables) fuel (operation.rootType schema) source
          operation.selectionSet 0
        obtain ⟨slices, seeded, unique⟩ := executeRoot_source_positions schema resolvers
          (coerceVariableValues operation variables) fuel (operation.rootType schema) source
          operation.selectionSet 0
        exact observed.addresses_reference coherent seeded unique
          (preparedResponseCovers_bubblingRoot schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema) source
            operation.selectionSet valid 0 errors reference containers)
    | ok pair =>
        simp [reference, GraphQL.Execution.selectionSetResultToResponse] at referenceNull
  · subst result
    simp [ExecutionObservation.initialErrors] at initialZero

-----------------------------------------------------------------------------------------
-- The remaining pure comparison excludes ordinary bubbling, not nullable errors
-----------------------------------------------------------------------------------------

/-- General client coverage now reduces only to nonbubbling ordinary root results.
Witness: mixed root reflection discharges every bubbling reference; the supplied
comparison is needed only for ordinary object fields. Those fields may contain nulls
and counted errors, so this is not a reduction to zero-error reconstruction.
The remaining comparison is a proof obligation, not an extra public queue premise.
-/
theorem ResponsePositionsDeliveredOrFailed_of_nonbubblingComparison
    (schema : Schema) (operation : Operation)
    (comparison
      : ∀ {ObjectRef : Type} (resolvers : Resolvers ObjectRef) variables fuel
          (source : ResolverValue ObjectRef) data errors,
          let completed :=
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation variables) fuel
                (operation.rootType schema) source operation.selectionSet).run
              0).1
          let response := selectionSetResultToResponse completed.result
          operation.incrementalArgumentsValid variables
          → rootSourceAppliesBool schema operation source = true
          → response.errors = 0
          → GraphQL.Execution.executeRootSelectionSet schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source (SelectionSet.eraseIncrementalDirectives operation.selectionSet)
            = .ok (data, errors)
          → ∀ containers,
              PreparedResponseCovers (.object data) response completed.work containers)
    : ResponsePositionsDeliveredOrFailed schema operation := by
  apply ResponsePositionsDeliveredOrFailed_of_preparedComparison schema operation
  intro ObjectRef resolvers variables fuel source
  dsimp only
  intro valid applies initialZero containers
  have ordinary : GraphQL.Execution.executeQueryWithFuel schema resolvers variables
      operation.eraseIncrementalDirectives fuel source
      = GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeRootSelectionSet schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema)
            source (SelectionSet.eraseIncrementalDirectives operation.selectionSet)) := by
    have root : GraphQL.Execution.rootSourceAppliesBool schema
        operation.eraseIncrementalDirectives source = true := applies
    simp only [GraphQL.Execution.executeQueryWithFuel, root, ↓reduceIte]
    rfl
  rw [ordinary]
  cases reference
        : GraphQL.Execution.executeRootSelectionSet schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema)
            source (SelectionSet.eraseIncrementalDirectives operation.selectionSet) with
  | error errors =>
      exact preparedResponseCovers_bubblingRoot schema resolvers
        (coerceVariableValues operation variables) fuel (operation.rootType schema) source
        operation.selectionSet valid 0 errors reference containers
  | ok pair =>
      obtain ⟨data, errors⟩ := pair
      exact comparison resolvers variables fuel source data errors valid applies initialZero
        reference containers

end GraphQL.IncrementalDelivery.Correctness
