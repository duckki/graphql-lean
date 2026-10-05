import Proofs.GraphQL.IncrementalDelivery.Correctness.ReferenceFailureCoverage

/-! Directive-free execution discharges the prepared-response coverage certificate. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

/-- A valid-root plain query has exactly its ordinary initial response positions.
Witness: directive-free completion equals ordinary root execution; every reference
position therefore belongs to the initial source inventory. Error counts are unrestricted.
-/
theorem preparedResponseCovers_plain (schema : Schema) (operation : Operation)
    (plain : SelectionsPlain operation.selectionSet) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (source : ResolverValue ObjectRef)
    (applies : rootSourceAppliesBool schema operation source = true) (containers : Bool)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema)
            source operation.selectionSet).run
          0).1
      PreparedResponseCovers
        (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
          operation.eraseIncrementalDirectives fuel source).data
        (selectionSetResultToResponse completed.result) completed.work containers := by
  have matched := executeRootSelectionSetCore_plain schema resolvers
    (coerceVariableValues operation variables) fuel (operation.rootType schema) source
    operation.selectionSet plain 0
  have root : GraphQL.Execution.rootSourceAppliesBool schema
      operation.eraseIncrementalDirectives source = true := applies
  have initial :
      GraphQL.Execution.executeQueryWithFuel schema resolvers variables
        operation.eraseIncrementalDirectives fuel source
      = selectionSetResultToResponse
          ((executeRootSelectionSetCore schema resolvers
              (coerceVariableValues operation variables) fuel (operation.rootType schema)
              source operation.selectionSet).run 0).1.result := by
    simp only [GraphQL.Execution.executeQueryWithFuel, root, ↓reduceIte, matched.2.1]
    rfl
  dsimp only
  intro path member
  rw [initial] at member
  exact Or.inl (List.mem_append_left _ member)

/-- The client-facing error-aware coverage statement holds for every plain query.
Witness: the pure plain-response certificate and the general observation reduction.
This is a proved syntax-restricted case, not the unrestricted incremental witness.
-/
theorem ResponsePositionsDeliveredOrFailed_of_plain (schema : Schema)
    (operation : Operation) (plain : SelectionsPlain operation.selectionSet)
    : ResponsePositionsDeliveredOrFailed schema operation := by
  apply ResponsePositionsDeliveredOrFailed_of_preparedComparison schema operation
  intro ObjectRef resolvers variables fuel source
  dsimp only
  intro _ applies _ containers
  exact preparedResponseCovers_plain schema operation plain resolvers variables fuel source
    applies containers

end GraphQL.IncrementalDelivery.Correctness
