import Proofs.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.Sources

/-! Public query witnesses and finite-observation laws for the direct-result model.
No obsolete program interpreter or executable scheduler is imported by these tests.
-/

namespace GraphQL.IncrementalDelivery.Tests.Query

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- The public statement has a kernel-checked witness for every schema and operation. -/
example (schema : Schema) (operation : Operation)
    : incrementalDirectiveFreeExecutionEquivalentToBasic schema operation :=
  incrementalDirectiveFreeExecutionEquivalentToBasic_holds schema operation

/-- Default-fuel agreement also accepts arbitrary factories, without a conformance
premise.
-/
example (scheduler : Execution.WorkScheduler) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef) (plain : operation.incrementalDirectiveFree)
    : executeQuery scheduler schema resolvers variables operation source
      = .single
          (GraphQL.Execution.executeQuery schema resolvers variables
            operation.eraseIncrementalDirectives source) :=
  executeQuery_plain scheduler schema resolvers variables operation source plain

/-- Initial data/errors agree even when the supplied factories are not known to conform.
-/
example (left right : Execution.WorkScheduler) (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (operation : Operation)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    : initialResponse
        (executeQueryWithFuel left schema resolvers variables operation fuel source)
      = initialResponse
          (executeQueryWithFuel right schema resolvers variables operation fuel source) :=
  executeQueryWithFuel_initialResponse_independent left right schema resolvers variables
    operation fuel source

/-- The batch witness accepts an admitted nonempty group from the actual work-event
mapper.
-/
example : Sources.responseStream.Accepts [Sources.events] :=
  (ResponseEventStream.batch_accepts_iff _ _).mpr ⟨by simp, fun _ h => h⟩

/-- The same batching witness excludes empty groups for every upstream stream. -/
example (stream : ResponseEventStream)
    : ¬(batchIncrementalResults stream).Accepts [] := by
  rw [ResponseEventStream.batch_accepts_iff]
  simp

/-- Composing source admission retains a chosen branch rather than mixing incompatible
suffixes.
-/
example : Sources.branching.Allows ([1] ++ [2]) := by
  apply (EventSource.allows_append_iff _ _ _).mpr
  constructor
  · intro initial before
    exact Or.inl (before.trans ⟨[2], rfl⟩)
  · intro initial before
    apply Or.inl
    exact (List.prefix_append_right_inj [1]).mpr before

/-- A completed mapped response remains a valid finite prefix when termination is
forgotten.
-/
example
    : (ExecutionResult.incremental Sources.initial Sources.responseStream).Observes
        (.incremental Sources.initial
          [(Sources.responseStream.next [Sources.events] Sources.allowed).1]) := by
  apply ExecutionResult.Observes.forgetComplete (complete := true)
  exact ⟨rfl, _, .cons _ _ Sources.allowed (.nil _), fun _ => Sources.finished⟩

/-- Every observation can be split and recombined using the intermediate-state witness. -/
example (start final : ResponseEventStream)
    (left right : List IncrementalStreamUpdateResult)
    (observed : start.Observes (left ++ right) final)
    : ∃ middle,
        start.Observes left middle
        ∧ middle.Observes right final
        ∧ start.Observes (left ++ right) final := by
  obtain ⟨middle, first, rest⟩ := observed.split left right
  exact ⟨middle, first, rest, first.append rest⟩

/-- Complete outcomes are admitted prefix observations, using the identical scheduler
witness.
-/
example {schema : Schema} {resolvers : Resolvers ObjectRef} {variables : VariableValues}
    {operation : Operation} {fuel : Nat} {source : ResolverValue ObjectRef}
    {result : QueryResult}
    (completed : queryOutcome schema resolvers variables operation fuel source result)
    : queryObservation schema resolvers variables operation fuel source result :=
  queryOutcome_observation completed

end GraphQL.IncrementalDelivery.Tests.Query
