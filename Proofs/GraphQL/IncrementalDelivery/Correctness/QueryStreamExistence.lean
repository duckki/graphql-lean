import Proofs.GraphQL.IncrementalDelivery.Correctness.NestedStreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryOutcomeExistence

/-! Raw stream observation existence and compatibility query interfaces.
The raw-work theorem retains its weaker metadata assumptions; query specializations use
general complete-outcome existence while preserving their original shape parameters.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

-----------------------------------------------------------------------------------------
-- Realize the constructed stream run through work packaging
-----------------------------------------------------------------------------------------

/-- Coherent stream-only work has a complete wire observation, including empty work.
Witness: constructive terminal-run existence followed by conforming-source realization,
or the ordinary-response branch. This is not a promise about every conforming source.
-/
theorem StreamOnly.workObservation_exists {paths bound work}
    (onlyStreams : StreamOnly work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work) (response : Response)
    : ∃ result, WorkObservation response work true result := by
  by_cases empty : work.size = 0
  · exact ⟨_, .single empty⟩
  · obtain ⟨scheduler, result, conforms, observed⟩ :=
      (completeObservation_exists_iff response work).mpr
        (Or.inr (onlyStreams.completeRun_exists coherent empty))
    exact ⟨result, (workObservation_iff_realizable response work true result).mpr
      ⟨scheduler, conforms, observed⟩⟩

-----------------------------------------------------------------------------------------
-- Compatibility root observations and query outcomes
-----------------------------------------------------------------------------------------

/-- Compatibility specialization of complete root observation existence.
Witness: the unconditional theorem; the original work-shape parameter is retained for
existing callers but is no longer needed by the proof.
-/
theorem executeRoot_completeObservation_of_streamOnly (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    (onlyStreams
      : StreamOnly
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
  have _ := onlyStreams
  exact executeRoot_completeObservation schema resolvers variables fuel parentType source selections

/-- Compatibility specialization of complete query outcome existence.
Witness: the unconditional query theorem, with the original shape premise retained.
This guarantees existence, not completion of every prefix or fairness of every source.
-/
theorem queryOutcome_exists_of_streamOnly (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (onlyStreams
      : rootSourceAppliesBool schema operation source = true
        → StreamOnly
            ((executeRootSelectionSetCore schema resolvers
                (coerceVariableValues operation variables) fuel
                (operation.rootType schema) source operation.selectionSet).run
              0).1.work)
    : ∃ result, queryOutcome schema resolvers variables operation fuel source result := by
  have _ := onlyStreams
  exact queryOutcome_exists schema resolvers variables operation fuel source

end GraphQL.IncrementalDelivery.Correctness
