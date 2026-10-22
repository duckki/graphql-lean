import Proofs.GraphQL.IncrementalDelivery.Correctness.NestedStreamExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization

/-! Stream-only query outcomes follow from generated locality and positive failures. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

-----------------------------------------------------------------------------------------
-- Realize the constructed stream run through work packaging
-----------------------------------------------------------------------------------------

/-- Certified stream-only work has a complete wire observation, including empty work.
Witness: constructive terminal-run existence followed by conforming-source realization,
or the ordinary-response branch. This is not a promise about every conforming source.
-/
theorem StreamOnly.workObservation_exists {paths bound work}
    (onlyStreams : StreamOnly work)
    (coherent : MixedOwnerPaths.WorkAt paths bound work)
    (under : ExecutionPaths.WorkUnder [] work)
    (positive : ExecutionErrors.WorkPositive work) (response : Response)
    : ∃ result, WorkObservation response work true result := by
  by_cases empty : work.size = 0
  · exact ⟨_, .single empty⟩
  · obtain ⟨scheduler, result, conforms, observed⟩ :=
      (completeObservation_exists_iff response work).mpr
        (Or.inr (onlyStreams.completeRun_exists coherent under positive empty))
    exact ⟨result, (workObservation_iff_realizable response work true result).mpr
      ⟨scheduler, conforms, observed⟩⟩

-----------------------------------------------------------------------------------------
-- Generated root observations and query outcomes
-----------------------------------------------------------------------------------------

/-- Stream-only root execution has a complete observation, including counted failures.
Witness: execution supplies owner paths, producer-local attachment bounds, and positive
failure counts. Constructive stream progress then supplies actual covering reports.
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
  intro completed
  obtain ⟨paths, coherent⟩ := MixedOwnerPaths.executeRoot_owners schema resolvers variables
    fuel parentType source selections 0
  exact onlyStreams.workObservation_exists coherent
    (ExecutionPaths.executeRootSelectionSetCore_under schema resolvers variables fuel
      parentType source selections 0)
    (ExecutionErrors.executeRootSelectionSetCore_positive schema resolvers variables fuel
      parentType source selections 0).2.1
    (selectionSetResultToResponse completed.result)

/-- Every stream-only query has a complete outcome through a conforming queue constructor.
Witness: generated stream progress followed by actual-query realization; invalid roots
use the ordinary error response and impose no queue law.
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
    : ∃ result createWorkQueue,
        queryWorkQueueConforms createWorkQueue schema resolvers variables operation fuel
          source
        ∧ queryOutcome createWorkQueue schema resolvers variables operation fuel source
            result := by
  by_cases applies : rootSourceAppliesBool schema operation source = true
  · obtain ⟨result, observed⟩ := executeRoot_completeObservation_of_streamOnly schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet (onlyStreams applies)
    refine ⟨result, queryObservation_iff_workHistory.mpr ?_⟩
    simpa only [applies, ↓reduceIte] using observed
  · refine ⟨.single { data := .null, errors := 1 },
      queryObservation_iff_workHistory.mpr ?_⟩
    simp [applies]

end GraphQL.IncrementalDelivery.Correctness
