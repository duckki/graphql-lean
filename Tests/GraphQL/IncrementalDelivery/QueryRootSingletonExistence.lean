import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryRootSingletonExistence
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Complete outcomes through actual execution of ancestor-dependent defer queries. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryRootSingletonExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open WorkScheduler

-----------------------------------------------------------------------------------------
-- A test-only structural certificate for computed work
-----------------------------------------------------------------------------------------

/-- Flat singleton boundaries may contain zero-size append trees but no hidden task.
This test-only certificate lets reduction check the shape of actual prepared work.
-/
def Flat : Work → Prop
  | .empty => True
  | .append left right => Flat left ∧ Flat right
  | .deferred groups _ _ children => (∃ group, groups = [group]) ∧ children.size = 0
  | .stream .. => False

/-- Navigation either stays among flat root boundaries or enters a task-free child.
Witness: append preserves the certificate; a deferred edge enters zero-size work.
-/
theorem Flat.located {work address current producer owners}
    (flat : Flat work) (located : Located work address current producer owners)
    : (Flat current ∧ producer = none) ∨ current.size = 0 := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact Or.inl ⟨flat, rfl⟩
  | left _ ih =>
      rcases ih with ⟨flat, root⟩ | empty
      · exact Or.inl ⟨flat.1, root⟩
      · exact Or.inr (Nat.add_eq_zero_iff.mp empty).1
  | right _ ih =>
      rcases ih with ⟨flat, root⟩ | empty
      · exact Or.inl ⟨flat.2, root⟩
      · exact Or.inr (Nat.add_eq_zero_iff.mp empty).2
  | deferred _ ih =>
      rcases ih with ⟨flat, _⟩ | impossible
      · exact Or.inr flat.2
      · simp [Work.size] at impossible
  | item _ _ ih =>
      rcases ih with ⟨impossible, _⟩ | impossible
      · exact False.elim impossible
      · simp [Work.size] at impossible

/-- The reducible test certificate implies the relational production theorem's shape.
Witness: structural node/task lookup and exclusion of task-free boundary locations.
-/
theorem Flat.root_singleton {work} (flat : Flat work) : RootSingletonGroups work := by
  constructor
  · intro node kind parents producer known
    cases StructuralEquivalence.nodeAt_of_current known with
    | group located member =>
        rcases flat.located located.toCurrent with ⟨_, root⟩ | impossible
        · exact ⟨rfl, root⟩
        · simp [Work.size] at impossible
    | stream located =>
        rcases flat.located located.toCurrent with ⟨impossible, _⟩ | impossible
        · exact False.elim impossible
        · simp [Work.size] at impossible
  · intro occurrence owners producer payload known
    cases StructuralEquivalence.taskAt_of_current known with
    | deferred located =>
        rcases flat.located located.toCurrent with ⟨⟨⟨group, rfl⟩, _⟩, _⟩ | impossible
        · exact ⟨group.node.key, rfl⟩
        · simp [Work.size] at impossible
    | item located entry =>
        rcases flat.located located.toCurrent with ⟨impossible, _⟩ | impossible
        · exact False.elim impossible
        · simp [Work.size] at impossible

-----------------------------------------------------------------------------------------
-- End-to-end queries, errors, and ordinary-response branches
-----------------------------------------------------------------------------------------

/-- Nested defer syntax introduces an ancestor-dependent ID without a value producer.
-/
def dependent : Operation :=
  { selectionSet := [defer [field "a", defer [field "b", defer [field "c"]]]] }

/-- A failing non-null parent group must still allow a complete, error-reporting outcome.
-/
def failing : Operation :=
  { selectionSet := [defer [field "required", defer [field "b"]]] }

#guard
  ((executeRootSelectionSetCore schema resolvers [] 8 "Query" (.object "Query" 0)
      failing.selectionSet).run
    0).1.work.size
  > 0

#guard
  ((executeRootSelectionSetCore schema resolvers [] 0 "Query" (.object "Query" 0)
      dependent.selectionSet).run
    0).1.work.size
  > 0

/-- Three ancestry levels admit a complete query outcome without supplied notices or
histories. Witness: computed root-singleton shape and the execution-metadata bridge.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] dependent 8 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_rootSingleton
  intro _
  apply Flat.root_singleton
  cbv
  simp

/-- Actual non-null failure retains complete-observation existence. Witness: the same
work-shape bridge, without a success or zero-error premise.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] failing 8 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_rootSingleton
  intro _
  apply Flat.root_singleton
  cbv
  simp

/-- Exhausted fuel can retain deferred error work and still admit a complete outcome.
Witness: reduction confirms singleton root groups even when their executions lack fuel.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] dependent 0 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_rootSingleton
  intro _
  apply Flat.root_singleton
  cbv
  simp

/-- Invalid roots require no work-shape evidence for unused execution. Witness: the
impossible applicability premise and the inherited ordinary error-response branch.
-/
example : ∃ result, queryOutcome schema resolvers [] dependent 8 .null result := by
  apply queryOutcome_exists_of_rootSingleton
  intro applies
  cases applies

end GraphQL.IncrementalDelivery.Tests.QueryRootSingletonExistence
