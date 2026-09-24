import Proofs.GraphQL.IncrementalDelivery.Correctness.MixedExistence
import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRealization
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedKeyRoles

/-! Complete query outcomes for every finite execution-generated work tree.
Execution supplies all metadata; no scheduler, history, or work-shape premise is assumed.
-/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open Semantics.GeneralScheduling

-----------------------------------------------------------------------------------------
-- Generated work always has a complete finite observation
-----------------------------------------------------------------------------------------

/-- Every nonempty prepared root work tree has an admitted complete run.
Witness: execution's ancestry, continuity, key roles, stream order, and owner paths
instantiate general mixed progress. No validation or successful-execution premise is used.
-/
theorem executeRoot_completeRun_exists (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : let work :=
        ((executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          0).1.work
      work.size ≠ 0 → ∃ history, WorkScheduler.AdmissibleRun work history := by
  intro work nonempty
  obtain ⟨_, ancestry, valid, coherent, continuous⟩ :=
    executeRoot_continuity schema resolvers variables fuel parentType source selections 0
  obtain ⟨roles, roleCoherent⟩ := KeyRoles.executeRoot_roles schema resolvers variables fuel
    parentType source selections 0
  obtain ⟨paths, pathCoherent⟩ := MixedOwnerPaths.executeRoot_owners schema resolvers variables
    fuel parentType source selections 0
  exact mixed_completeRun_exists valid coherent roleCoherent continuous
    (executeRoot_streamOwnersOrdered schema resolvers variables fuel parentType source selections 0)
    pathCoherent nonempty

/-- Every prepared execution has a complete ordinary or incremental observation.
Witness: direct empty-work packaging, or the constructed terminal history followed by
conforming-source realization. The source is an existential witness, not a runtime choice.
-/
theorem executeRoot_completeObservation (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
    : let completed :=
        ((executeRootSelectionSetCore schema resolvers variables fuel
            parentType source selections).run
          0).1
      ∃ result,
        WorkObservation (selectionSetResultToResponse completed.result)
          completed.work true result := by
  intro completed
  by_cases empty : completed.work.size = 0
  · exact ⟨_, .single empty⟩
  · have run := executeRoot_completeRun_exists schema resolvers variables fuel parentType
      source selections empty
    obtain ⟨scheduler, result, conforms, observed⟩ :=
      (completeObservation_exists_iff (selectionSetResultToResponse completed.result)
        completed.work).mpr (Or.inr run)
    exact ⟨result, (workObservation_iff_realizable _ _ true result).mpr
      ⟨scheduler, conforms, observed⟩⟩

-----------------------------------------------------------------------------------------
-- Complete query outcomes without any progress premise
-----------------------------------------------------------------------------------------

/-- Every modeled query has a complete outcome, including arbitrary mixed defer/stream
nesting, shared selections, errors, and exhausted fuel. Witness: generated finite progress
and actual response realization; invalid roots return the ordinary error response.
This is existence of an allowed outcome, not fairness or completion of every admitted
prefix.
-/
theorem queryOutcome_exists (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef)
    : ∃ result, queryOutcome schema resolvers variables operation fuel source result := by
  by_cases applies : rootSourceAppliesBool schema operation source = true
  · obtain ⟨result, observed⟩ := executeRoot_completeObservation schema resolvers
      (coerceVariableValues operation variables) fuel (operation.rootType schema) source
      operation.selectionSet
    refine ⟨result, queryObservation_iff_workHistory.mpr ?_⟩
    simpa only [applies, ↓reduceIte] using observed
  · refine ⟨.single { data := .null, errors := 1 },
      queryObservation_iff_workHistory.mpr ?_⟩
    simp [applies]

/-- The public complete-outcome existence statement holds without extra premises.
Witness: the unconditional query theorem, universally quantified over execution inputs.
-/
theorem queryOutcomeExists_holds (schema : Schema) (operation : Operation)
    : queryOutcomeExists schema operation :=
  fun resolvers variables fuel source =>
    queryOutcome_exists schema resolvers variables operation fuel source

end GraphQL.IncrementalDelivery.Correctness
