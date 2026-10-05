import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamExecutionCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryEntryCoverage

/-! Recursive mixed value coverage discharges the public client-facing failure statement. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open Semantics

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- Recursive value and response-field comparisons have no remaining coverage premises
-----------------------------------------------------------------------------------------

/-- Every valid ordinary successful value has covered actual initial/source data or failure.
Witness: strong execution-fuel induction with structural type descent for non-null
wrappers. Named objects reduce through the actual field/plan comparison; lists reduce
through actual prefix/tail stream assembly. Counted errors and partial initial data remain
unrestricted, and all retained failure explanations name actual failed tasks.
-/
theorem valueCompletionCoverage_holds (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    : ValueCompletionCoverage containers schema resolvers variables fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      cases fuel with
      | zero => exact valueCompletionCoverage_zero containers schema resolvers variables
      | succ fuel =>
          intro fieldType
          induction fieldType with
          | named parentType =>
              intro selected resolved valid path usages deferMap allowStream
              cases fuel with
              | zero =>
                  exact completeValue_named_entriesCovered_one containers schema resolvers
                    variables parentType selected resolved valid path usages deferMap allowStream
              | succ smaller =>
                  exact completeValue_named_entriesCovered_of_values containers schema
                    resolvers variables smaller (ih smaller (by omega)) parentType
                    selected resolved valid path usages deferMap allowStream
          | list inner _ =>
              intro selected resolved valid path usages deferMap allowStream
              cases resolved with
              | null | scalar _ | object _ _ =>
                  intro state
                  apply ValueCompletionCovered.of_result_eq
                  simp [completeValue, GraphQL.Execution.completeValue, Completion.pure,
                    Completion.error]
              | list values =>
                  simpa only [completeValue, GraphQL.Execution.completeValue]
                    using completeListValueWithStream_entriesCovered_of_values containers
                      schema resolvers variables fuel (ih fuel (by omega)) inner selected
                      values valid path usages deferMap allowStream
          | nonNull inner innerCovered =>
              intro selected resolved valid path usages deferMap allowStream
              exact completeValue_nonNull_entriesCovered_of_inner containers schema resolvers
                variables fuel inner selected resolved valid path usages deferMap allowStream
                (innerCovered selected resolved valid path usages deferMap allowStream)

/-- Every valid actual response field has the proved mixed failure-aware comparison.
Witness: exhausted-field agreement or resolver branching followed by the complete
recursive value witness; no scheduler assumption is used in this pure execution theorem.
-/
theorem responseFieldCoverage_holds (containers : Bool) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef)
    : ResponseFieldCoverage containers schema resolvers variables fuel parentType
        source := by
  cases fuel with
  | zero =>
      exact responseFieldCoverage_zero containers schema resolvers variables parentType source
  | succ fuel =>
      exact responseFieldCoverage_of_values containers schema resolvers variables fuel
        (valueCompletionCoverage_holds containers schema resolvers variables fuel) parentType source

-----------------------------------------------------------------------------------------
-- Public failure-aware position coverage follows from pure comparison and queue reporting
-----------------------------------------------------------------------------------------

/-- Every reference response position is delivered or explained by a client failure scope.
Witness: recursive mixed value/field coverage constructs the prepared-response certificate;
the conformant terminal queue reports every unavailable producer through an announced
failure ID. The public statement requires valid incremental arguments and an error-free
initial response, not zero errors in later incremental results or ordinary execution.
-/
theorem ResponsePositionsDeliveredOrFailed_holds (schema : Schema) (operation : Operation)
    : ResponsePositionsDeliveredOrFailed schema operation := by
  apply ResponsePositionsDeliveredOrFailed_of_fields
  intro ObjectRef resolvers variables fuel source containers _
  exact responseFieldCoverage_holds containers schema resolvers
    (coerceVariableValues operation variables) fuel (operation.rootType schema) source

end GraphQL.IncrementalDelivery.Correctness
