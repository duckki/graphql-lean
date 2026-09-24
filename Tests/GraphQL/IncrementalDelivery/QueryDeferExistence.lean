import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryDeferExistence
import Tests.GraphQL.IncrementalDelivery.DeferExistence
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Complete outcomes for overlapping defer selections through actual query execution. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryDeferExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open DeferExistence

/-- Overlapping outer and inner defer blocks share object and child field selections. -/
def nested : Operation :=
  {
    selectionSet :=
      [
        defer [field "user" [field "name", defer [field "age"]]],
        defer [field "user" [field "name", defer [field "age"]]]
      ]
  }

/-- The same overlap also produces independent child work for each object-list item. -/
def branching : Operation :=
  {
    selectionSet :=
      [
        defer [field "users" [field "name", defer [field "age"]]],
        defer [field "users" [field "name", defer [field "age"]]]
      ]
  }

/-- A shared produced selection fails non-null completion in both deferred contexts. -/
def failing : Operation :=
  {
    selectionSet :=
      [
        defer [field "user" [field "name", defer [field "required"]]],
        defer [field "user" [field "name", defer [field "required"]]]
      ]
  }

/-- Detect genuinely shared tasks with positive child work, not only repeated syntax.
This guard is test-only and does not prescribe how scheduling observes those tasks.
-/
def hasSharedProducer : Work → Bool
  | .empty => false
  | .combine left right => hasSharedProducer left || hasSharedProducer right
  | .executionGroup groups _ _ children =>
      (groups.length > 1 && children.size > 0) || hasSharedProducer children
  | .stream .. => false

#guard
  hasSharedProducer
    ((executeRootSelectionSetCore schema resolvers [] 12 "Query"
        (.object "Query" 0) nested.selectionSet).run
      0).1.work

#guard
  hasSharedProducer
    ((executeRootSelectionSetCore schema resolvers [] 12 "Query"
        (.object "Query" 0) branching.selectionSet).run
      0).1.work

#guard
  hasSharedProducer
    ((executeRootSelectionSetCore schema resolvers [] 12 "Query"
        (.object "Query" 0) failing.selectionSet).run
      0).1.work

/-- Overlapping object selections admit a complete query outcome without supplied notices.
Witness: compute only the defer-only shape; execution supplies the metadata and progress
constructs a terminal history rather than assuming one.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] nested 12 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_deferOnly
  intro _
  apply Tree.defer_only
  cbv

/-- Shared producers with branching object-list descendants admit complete outcomes.
Witness: the same query bridge with no restriction on co-owner choices or outcomes.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] branching 12 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_deferOnly
  intro _
  apply Tree.defer_only
  cbv

/-- Failure of a shared produced field still permits a complete, error-reporting outcome.
Witness: defer-only progress has no successful-execution premise.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] failing 12 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_deferOnly
  intro _
  apply Tree.defer_only
  cbv

/-- Exhausted fuel is covered even when deferred error work remains.
Witness: generated-work shape and the same finite progress theorem.
-/
example
    : ∃ result, queryOutcome schema resolvers [] nested 0 (.object "Query" 0) result := by
  apply queryOutcome_exists_of_deferOnly
  intro _
  apply Tree.defer_only
  cbv

/-- Invalid roots require no shape premise for unused prepared work.
Witness: the impossible applicability hypothesis and ordinary query error branch.
-/
example : ∃ result, queryOutcome schema resolvers [] nested 12 .null result := by
  apply queryOutcome_exists_of_deferOnly
  intro applies
  cases applies

end GraphQL.IncrementalDelivery.Tests.QueryDeferExistence
