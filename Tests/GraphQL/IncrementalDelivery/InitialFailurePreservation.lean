import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialFailurePreservation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Mixed failures persist after erasure, although ordinary error counts can differ. -/

namespace GraphQL.IncrementalDelivery.Tests.InitialFailurePreservation
open GraphQL.IncrementalDelivery.Execution
open Correctness.InitialFailures

private def selections : List Selection :=
  [field "required" [] [] (some "first"), defer [field "required" [] [] (some "later")]]

/-- A root bubble drops its deferred work, while ordinary execution counts both errors.
Witness: reduction of the actual completions; equal error counts would be too strong.
-/
example
    : ((executeRootSelectionSetCore schema resolvers [] 30 "Query" (.object "Query" 0)
          selections).run
          0).1.result
        = .error 1
      ∧ GraphQL.Execution.executeRootSelectionSet schema resolvers [] 30 "Query"
          (.object "Query" 0) (SelectionSet.eraseIncrementalDirectives selections)
        = .error 2 := by
  constructor <;> cbv

/-- Root failure preservation holds for every resolver, fuel, and fresh supply.
Witness: the mixed theorem with syntactic argument validity, not fixture evaluation.
-/
example {ObjectRef : Type} (environment : Resolvers ObjectRef) (fuel : Nat)
    (source : ResolverValue ObjectRef) (state errors : Nat)
    (failed
      : ((executeRootSelectionSetCore schema environment [] fuel "Query" source
            selections).run
          state).1.result
        = .error errors)
    : ∃ count,
        GraphQL.Execution.executeRootSelectionSet schema environment [] fuel "Query"
          source (SelectionSet.eraseIncrementalDirectives selections)
        = .error count := by
  exact executeRoot_preserves_failures schema environment [] fuel "Query" source
    selections (by cbv) state errors failed

private def fields : List FieldDetails :=
  [{ fieldName := "users", arguments := [], selectionSet := selections }]

private def values : List (ResolverValue Nat) :=
  [.object "User" 1, .object "User" 2]

/-- Stream short-circuiting retains one failure, while ordinary completion counts four.
Witness: two objects each contain immediate and deferred non-null failures. This is a
mixed stream-item example, outside the earlier plain-item comparison's hypothesis.
-/
example
    : ((completeStreamItems schema resolvers [] 30 (.nonNull (.named "User")) fields
          values [.field "users"] 0).run
          0).1
        = [({ result := .error 1, cause := some 1 }, .empty)]
      ∧ GraphQL.Execution.completeValueList schema resolvers [] 30
          (.nonNull (.named "User")) (fields.map Semantics.eraseField) values
        = .error 4 := by
  constructor <;> cbv

/-- Any retained failure for these mixed items implies ordinary full-list bubbling.
Witness: the generalized stream theorem; the retained count and child work are arbitrary.
-/
example {ObjectRef : Type} (environment : Resolvers ObjectRef) (fuel : Nat)
    (values : List (ResolverValue ObjectRef)) (state errors : Nat) (cause : Option Nat)
    (children : Work)
    (failed
      : ({ result := .error errors, cause }, children)
        ∈ ((completeStreamItems schema environment [] fuel (.nonNull (.named "User"))
              fields values [.field "users"] 0).run
            state).1)
    : ∃ count,
        GraphQL.Execution.completeValueList schema environment [] fuel
          (.nonNull (.named "User")) (fields.map Semantics.eraseField) values
        = .error count := by
  apply completeStreamItems_failure_bubbles schema environment [] fuel
    (.nonNull (.named "User")) fields values _ [.field "users"] 0 state errors cause children failed
  intro field member
  simp only [fields, List.mem_singleton] at member
  subst field
  constructor <;> cbv

#print axioms executeRoot_preserves_failures
#print axioms completeStreamItems_failure_bubbles

end GraphQL.IncrementalDelivery.Tests.InitialFailurePreservation
