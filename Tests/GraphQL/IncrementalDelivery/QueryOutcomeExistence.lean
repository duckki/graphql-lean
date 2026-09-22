import Proofs.GraphQL.IncrementalDelivery.Correctness.QueryOutcomeExistence
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Unconditional complete outcomes through genuinely alternating generated work. -/

namespace GraphQL.IncrementalDelivery.Tests.QueryOutcomeExistence
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-- Overlapping deferred selections produce streamed objects, which produce deferred
fields containing further streams. The pattern is defer, stream, defer, stream.
-/
def alternating : Operation :=
  {
    selectionSet :=
      [
        defer
          [field "users" [field "name", defer [field "values" [] [.stream]]] [.stream]],
        defer
          [field "users" [field "name", defer [field "values" [] [.stream]]] [.stream]]
      ]
  }

/-- A non-null deferred field fails inside each streamed object after shared production.
-/
def failingChild : Operation :=
  {
    selectionSet :=
      [
        defer [field "users" [field "name", defer [field "required"]] [.stream]],
        defer [field "users" [field "name", defer [field "required"]] [.stream]]
      ]
  }

/-- A shared deferred group produces a stream with a failing non-null item. -/
def failingItem : Operation :=
  {
    selectionSet :=
      [defer [field "strict" [] [.stream]], defer [field "strict" [] [.stream]]]
  }

/-- Bounded test-only search checks an actual work path for the requested node kinds.
False denotes defer, true stream. Unmatched nodes and append edges may be skipped.
-/
def containsPattern : Nat → List Bool → Work → Bool
  | _, [], _ => true
  | 0, _ :: _, _ => false
  | fuel + 1, pattern@(kind :: rest), work =>
      match work with
      | .empty => false
      | .combine left right =>
          containsPattern fuel pattern left || containsPattern fuel pattern right
      | .executionGroup _ _ _ children =>
          (!kind && containsPattern fuel rest children)
          || containsPattern fuel pattern children
      | .stream _ items =>
          (kind
            && (rest.isEmpty || items.any (fun item => containsPattern fuel rest item.2)))
          || items.any (fun item => containsPattern fuel pattern item.2)

/-- Detect a genuinely shared task with descendants anywhere in the bounded work tree.
-/
def containsSharedProducer : Nat → Work → Bool
  | 0, _ => false
  | fuel + 1, work =>
      match work with
      | .empty => false
      | .combine left right =>
          containsSharedProducer fuel left || containsSharedProducer fuel right
      | .executionGroup groups _ _ children =>
          (groups.length > 1 && children.size > 0) || containsSharedProducer fuel children
      | .stream _ items => items.any (fun item => containsSharedProducer fuel item.2)

/-- Prepared work is inspected only for fixture guards, never supplied as a proof premise.
-/
def prepared (operation : Operation) (fuel : Nat := 16) : Work :=
  ((executeRootSelectionSetCore schema resolvers [] fuel "Query" (.object "Query" 0)
      operation.selectionSet).run
    0).1.work

#guard containsPattern 20 [false, true, false, true] (prepared alternating)
#guard containsSharedProducer 20 (prepared alternating)
#guard containsPattern 20 [false, true, false] (prepared failingChild)
#guard containsSharedProducer 20 (prepared failingChild)
#guard containsPattern 20 [false, true] (prepared failingItem)
#guard (prepared alternating 0).size > 0

/-- All alternating/shared executions have complete outcomes, even with exhausted fuel.
Witness: the unconditional query theorem, without shape, success, or history evidence.
-/
example (fuel : Nat)
    : ∃ result,
        queryOutcome schema resolvers [] alternating fuel (.object "Query" 0) result :=
  queryOutcome_exists schema resolvers [] alternating fuel (.object "Query" 0)

/-- A produced defer failure inside a stream retains a complete error-reporting outcome.
Witness: mixed progress includes failure accounting and cancellation.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] failingChild 16 (.object "Query" 0) result :=
  queryOutcome_exists schema resolvers [] failingChild 16 (.object "Query" 0)

/-- Failure of a streamed item after shared deferred production also completes.
Witness: the same general query theorem with no zero-error premise.
-/
example
    : ∃ result,
        queryOutcome schema resolvers [] failingItem 16 (.object "Query" 0) result :=
  queryOutcome_exists schema resolvers [] failingItem 16 (.object "Query" 0)

/-- Invalid roots are covered without examining or constraining unused prepared work.
Witness: the ordinary error branch of the unconditional theorem.
-/
example : ∃ result, queryOutcome schema resolvers [] alternating 16 .null result :=
  queryOutcome_exists schema resolvers [] alternating 16 .null

end GraphQL.IncrementalDelivery.Tests.QueryOutcomeExistence
