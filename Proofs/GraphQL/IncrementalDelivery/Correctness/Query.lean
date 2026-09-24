import Proofs.GraphQL.IncrementalDelivery.Semantics.DirectiveFree
import Proofs.GraphQL.IncrementalDelivery.Correctness.RootExecution

/-! Query-level correctness witnesses for the directive-free fragment. -/

namespace GraphQL.IncrementalDelivery.Correctness

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

variable {ObjectRef : Type}

/-- Plain collection and plan execution preserve the basic result and generate no work.
Witness: compose collectFields_plain, executeCollectedFields_plain, and executePlan_plain.
-/
theorem executeRootSelectionSetCore_plain (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (hplain : SelectionsPlain selections) (state : Nat)
    : RunMatches
        (executeRootSelectionSetCore schema resolvers variables fuel parentType source
          selections)
        (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
          parentType source (SelectionSet.eraseIncrementalDirectives selections))
        state := by
  simp only [executeRootSelectionSetCore, GraphQL.Execution.executeRootSelectionSet]
  apply runMatches_after_collection _ _ _ _ _
    (collectFields_plain schema variables parentType source selections hplain state)
  intro collection hn hp he
  have hr := executeCollectedFields_plain schema resolvers variables fuel parentType source
    collection.fields hp [] state
  rw [he] at hr
  exact executePlan_plain schema resolvers variables fuel parentType source collection [] state _
    hn hp hr

/-- Public equivalence for every factory, with no scheduler law or error-free premise.
Witness: the plain core generates no work, so root packaging takes the ordinary branch.
-/
theorem incrementalDirectiveFreeExecutionEquivalentToBasic_holds
    (schema : Schema) (operation : Operation)
    : incrementalDirectiveFreeExecutionEquivalentToBasic schema operation := by
  intro hplain ObjectRef resolvers variables fuel source scheduler
  have hv : coerceVariableValues operation variables =
      GraphQL.Execution.coerceVariableValues operation.eraseIncrementalDirectives variables := rfl
  have hroot : rootSourceAppliesBool schema operation source =
      GraphQL.Execution.rootSourceAppliesBool schema
        operation.eraseIncrementalDirectives source := rfl
  cases hs : rootSourceAppliesBool schema operation source
  · simp [executeQueryWithFuel, GraphQL.Execution.executeQueryWithFuel, ← hroot, hs]
  · have hr := executeRootSelectionSetCore_plain schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet hplain 0
    have hresult := hr.2.1
    have hwork := hr.2.2
    simp only [executeQueryWithFuel, executeRootSelectionSet_fromWork,
      GraphQL.Execution.executeQueryWithFuel,
      ← hroot, hs, ↓reduceIte]
    generalize (executeRootSelectionSetCore schema resolvers (coerceVariableValues operation variables)
      fuel (operation.rootType schema) source operation.selectionSet).run 0 = output
      at hresult hwork ⊢
    rcases output with ⟨completed, final⟩
    dsimp only at hresult hwork ⊢
    rw [executionFromWork_silent _ _ _ hwork, hresult]
    rfl

mutual
  /-- Erasing directives preserves a selection's size; witness: structural mutual
  induction.
  -/
  theorem eraseSelection_size (selection : Selection)
      : selection.eraseIncrementalDirectives.size = selection.size := by
    cases selection with
    | field responseName fieldName arguments directives children =>
        exact congrArg (1 + ·) (eraseSelectionSet_size children)
    | inlineFragment condition directives children =>
        exact congrArg (1 + ·) (eraseSelectionSet_size children)
  termination_by sizeOf selection

  /-- Selection-list size is also preserved, using the head and tail induction witnesses.
  -/
  theorem eraseSelectionSet_size (selections : List Selection)
      : GraphQL.SelectionSet.size (SelectionSet.eraseIncrementalDirectives selections)
        = SelectionSet.size selections := by
    cases selections with
    | nil => rfl
    | cons selection rest =>
        simp [SelectionSet.eraseIncrementalDirectives, GraphQL.SelectionSet.size,
          SelectionSet.size, eraseSelection_size selection, eraseSelectionSet_size rest]
  termination_by sizeOf selections
end

/-- Both query entry points choose the same fuel bound, by size preservation under
erasure.
-/
theorem eraseOperation_fuelBound (schema : Schema) (operation : Operation)
    : GraphQL.Execution.executeQueryFuelBound schema operation.eraseIncrementalDirectives
      = executeQueryFuelBound schema operation := by
  simp [GraphQL.Execution.executeQueryFuelBound, executeQueryFuelBound,
    GraphQL.Operation.size, Operation.size, Operation.eraseIncrementalDirectives,
    eraseSelectionSet_size]

/-- Default-fuel equivalence follows from the public explicit-fuel witness and equal
bounds.
-/
theorem executeQuery_plain (scheduler : Execution.WorkScheduler)
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef) (hplain : operation.incrementalDirectiveFree)
    : executeQuery scheduler schema resolvers variables operation source
      = .single
          (GraphQL.Execution.executeQuery schema resolvers variables
            operation.eraseIncrementalDirectives source) := by
  simp only [executeQuery, GraphQL.Execution.executeQuery, eraseOperation_fuelBound]
  exact incrementalDirectiveFreeExecutionEquivalentToBasic_holds schema operation
    hplain resolvers variables _ source scheduler

end GraphQL.IncrementalDelivery.Correctness
