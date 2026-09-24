import Proofs.GraphQL.IncrementalDelivery.Correctness.QuerySingletonDeferExistence
import Tests.GraphQL.IncrementalDelivery.SingletonDeferExistence
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual deferred object/list queries with structurally nested task producers. -/

namespace GraphQL.IncrementalDelivery.Tests.QuerySingletonDeferExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open SingletonDeferExistence

/-- Deferred object completion reveals a further deferred selection inside that object.
-/
def nested : Operation :=
  { selectionSet := [defer [field "user" [field "name", defer [field "age"]]]] }

/-- One deferred producer reveals independent deferred children in each object-list item.
-/
def branching : Operation :=
  { selectionSet := [defer [field "users" [field "name", defer [field "age"]]]] }

/-- The produced child encounters a non-null failure inside the deferred object. -/
def failing : Operation :=
  { selectionSet := [defer [field "user" [field "name", defer [field "required"]]]] }

/-- Detect positive work under a deferred producer, beyond root-only defer syntax.
This Boolean is a test guard, not a scheduler or correctness premise.
-/
def hasProducedWork : Work → Bool
  | .empty => false
  | .combine left right => hasProducedWork left || hasProducedWork right
  | .executionGroup _ _ _ children => children.size > 0
  | .stream .. => false

#guard
  hasProducedWork
    ((executeRootSelectionSetCore schema resolvers [] 12 "Query"
        (.object "Query" 0) nested.selectionSet).run
      0).1.work

#guard
  hasProducedWork
    ((executeRootSelectionSetCore schema resolvers [] 12 "Query"
        (.object "Query" 0) branching.selectionSet).run
      0).1.work

#guard
  hasProducedWork
    ((executeRootSelectionSetCore schema resolvers [] 12 "Query"
        (.object "Query" 0) failing.selectionSet).run
      0).1.work

/-- Actual nested object producers admit a complete query outcome. Witness: compute only
the singleton work shape; execution supplies metadata and the theorem constructs a run.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] nested 12 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_singletonDefer
  intro _
  apply Tree.singleton_defer
  cbv
  simp

/-- Branching produced object-list regions with repeated defer IDs admit complete outcomes.
Witness: the same relational existence theorem, not a selected completion serialization.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] branching 12 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_singletonDefer
  intro _
  apply Tree.singleton_defer
  cbv
  simp

/-- A failing produced child still admits a complete, error-reporting observation.
Witness: computed singleton shape without any success premise.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] failing 12 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_singletonDefer
  intro _
  apply Tree.singleton_defer
  cbv
  simp

/-- Exhausted fuel remains covered, even when execution retains deferred error work.
Witness: the same generated-work bridge and direct shape reduction.
-/
example
    : ∃ result, queryOutcome schema resolvers [] nested 0 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_singletonDefer
  intro _
  apply Tree.singleton_defer
  cbv
  simp

/-- Invalid roots need no shape certificate for their unused work. Witness: the
impossible applicability premise and the ordinary error branch of query realization.
-/
example : ∃ result, queryOutcome schema resolvers [] nested 12 .null result := by
  apply queryOutcome_exists_of_singletonDefer
  intro applies
  cases applies

end GraphQL.IncrementalDelivery.Tests.QuerySingletonDeferExistence
