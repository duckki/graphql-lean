import Proofs.GraphQL.IncrementalDelivery.Correctness.RootSingletonExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryOutcomeExistence

/-! Compatibility query interfaces for root-singleton defer prepared work.
Root observations and query outcomes specialize the unconditional existence theorems,
retaining the original shape parameters for existing callers.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.GeneralScheduling

-----------------------------------------------------------------------------------------
-- Compatibility root observations
-----------------------------------------------------------------------------------------

/-- Compatibility specialization of complete root observation existence.
Witness: the unconditional theorem; the original work-shape parameter is retained for
existing callers but is no longer needed by the proof.
-/
theorem executeRoot_completeObservation_of_rootSingleton (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (shape
      : RootSingletonGroups
          ((executeRootSelectionSetCore schema resolvers variables fuel
              parentType source selections).run
            0).1.work)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          0).1
      ∃ result,
        WorkObservation (selectionSetResultToResponse completed.result)
          completed.work true result := by
  have _ := shape
  exact executeRoot_completeObservation schema resolvers variables fuel parentType source selections

-----------------------------------------------------------------------------------------
-- Compatibility query outcomes
-----------------------------------------------------------------------------------------

/-- Compatibility specialization of complete query outcome existence.
Witness: the unconditional query theorem, with the original shape premise retained.
This guarantees existence, not completion of every prefix or fairness of every source.
-/
theorem queryOutcome_exists_of_rootSingleton (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (shape
      : rootSourceAppliesBool schema operation source = true
        → RootSingletonGroups
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation variables) fuel
                (operation.rootType schema) source operation.selectionSet).run
              0).1.work)
    : ∃ result, queryOutcome schema resolvers variables operation fuel source result := by
  have _ := shape
  exact queryOutcome_exists schema resolvers variables operation fuel source

end GraphQL.IncrementalDelivery.Correctness
