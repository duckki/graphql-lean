import Proofs.GraphQL.IncrementalDelivery.Correctness.QuerySourceCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.RootSourceReconstruction
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceTypedEntries
import Proofs.GraphQL.IncrementalDelivery.Correctness.SourceSuccess
import Proofs.GraphQL.IncrementalDelivery.Correctness.LeafCoverage

/-! Public position coverage and exactly-once leaves for all successful query outcomes. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution

/-- Complete zero-error root observations have precisely the typed entries of ordinary
directive-erased execution. Witness: source success, the mutual reconstruction proof,
and exact identification of typed slices with the occurrence-labelled inventory.
-/
theorem root_source_entries (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List Selection) (state : Nat)
    {result : QueryResult}
    (observed
      : let completed :=
          ((executeRootSelectionSetCore schema resolvers variables
              fuel parentType source selections).run
            state).1
        WorkObservation (selectionSetResultToResponse completed.result) completed.work
          true result)
    (zero : result.totalErrors = 0)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables
            fuel parentType source selections).run
          state).1
      let response := selectionSetResultToResponse completed.result
      ∃ data,
        GraphQL.Execution.executeCollectedFields schema resolvers variables fuel
            parentType source
            (GraphQL.Execution.collectFields schema variables parentType source
              (SelectionSet.eraseIncrementalDirectives selections))
          = .ok (data, 0)
        ∧ (TypedResponse.value [] response.data
            ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
                  completed.work).flatMap
                SourceTask.entries).Perm
            (TypedResponse.value [] (.object data)) := by
  have success := observed.completionSuccess
    (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers variables fuel
      parentType source selections state) zero
  obtain ⟨data, slices, basic, typed, perm, seed⟩ :=
    SourceReconstruction.executeRoot_seeded_success schema resolvers variables fuel
      parentType source selections state success
  obtain ⟨initial, initialEq⟩ := success.1
  have identified := sourceTasks_typed typed seed
  refine ⟨data, basic, ?_⟩
  simp only [initialEq, Semantics.MixedPaths.resultCursors] at identified
  have full := perm.cons ([], TypedResponse.Atom.object)
  simpa only [initialEq, selectionSetResultToResponse,
    GraphQL.Execution.selectionSetResultToResponse, ResponsePositions.listCursors,
    List.flatMap, identified, TypedResponse.result, TypedResponse.value,
    List.cons_append] using full

/-- The full incremental source inventory has exactly the ordinary query's positions.
Witness: typed entry equality survives optional removal of container tags; invalid roots
are excluded by the zero-error premise, not by a new validity assumption.
-/
theorem queryOutcome_source_equivalent
    {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : QueryResult}
    (observed : queryOutcome schema resolvers variables operation fuel source result)
    (zero : result.totalErrors = 0) (containers : Bool)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema)
            source operation.selectionSet).run
          0).1
      let response := selectionSetResultToResponse completed.result
      (ResponsePositions.value containers [] response.data
        ++ (sourceTasks [] none (ResponsePositions.listCursors [] response.data)
              completed.work).flatMap
            (SourceTask.positions containers)).Perm
        (ResponsePositions.value containers []
          (GraphQL.Execution.executeQueryWithFuel schema resolvers variables
            operation.eraseIncrementalDirectives fuel source).data) := by
  have witnessed := queryObservation_workHistory observed
  cases applies : rootSourceAppliesBool schema operation source with
  | false =>
      simp only [applies, Bool.false_eq_true, ↓reduceIte] at witnessed
      subst result
      simp [QueryResult.totalErrors] at zero
  | true =>
      simp only [applies, ↓reduceIte] at witnessed
      obtain ⟨data, basic, entries⟩ := root_source_entries schema resolvers
        (coerceVariableValues operation variables) fuel (operation.rootType schema) source
        operation.selectionSet 0 witnessed zero
      have response : GraphQL.Execution.executeQueryWithFuel schema resolvers variables
          operation.eraseIncrementalDirectives fuel source = {data := .object data, errors := 0} := by
        have root : GraphQL.Execution.rootSourceAppliesBool schema
            operation.eraseIncrementalDirectives source = true := applies
        simp only [GraphQL.Execution.executeQueryWithFuel, root, ↓reduceIte,
          GraphQL.Execution.executeRootSelectionSet]
        change GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeCollectedFields schema resolvers
            (coerceVariableValues operation variables) fuel (operation.rootType schema) source
            (GraphQL.Execution.collectFields schema (coerceVariableValues operation variables)
              (operation.rootType schema) source
              (SelectionSet.eraseIncrementalDirectives operation.selectionSet))) = _
        rw [basic]
        rfl
      rw [response]
      simpa only [List.filterMap_append, List.filterMap_flatMap,
        TypedResponse.value_entryPaths, SourceTask.entries_positions,
        source_value_eq_positions]
        using entries.filterMap (TypedResponse.entryPath containers)

/-- Every successful complete query delivers precisely all ordinary response positions,
including optional containers. Witness: terminal wire/source coverage followed by typed
source/basic reconstruction. No scheduler, syntax, or resolver restriction is added.
-/
theorem deliveredResponsePositionsEquivalentToBasic_holds (schema : Schema)
    (operation : Operation)
    : deliveredResponsePositionsEquivalentToBasic schema operation := by
  intro ObjectRef resolvers variables fuel source result observed zero containers
  obtain ⟨slices, delivered, covered⟩ := queryOutcome_source_coverage observed zero containers
  exact ⟨slices, delivered,
    covered.trans (queryOutcome_source_equivalent observed zero containers)⟩

/-- Each ordinary scalar/null leaf occurs once across all delivered slices. Witness:
public position coverage and ordinary response-path uniqueness.
-/
theorem basicLeavesDeliveredExactlyOnce_holds (schema : Schema) (operation : Operation)
    : basicLeavesDeliveredExactlyOnce schema operation :=
  basicLeavesDeliveredExactlyOnce_of_positions
    (deliveredResponsePositionsEquivalentToBasic_holds schema operation)

end GraphQL.IncrementalDelivery.Correctness
