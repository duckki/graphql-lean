import Proofs.GraphQL.IncrementalDelivery.Correctness.ListExecutionCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Lists retain nested deferred failures without equating ordinary and initial data. -/

namespace GraphQL.IncrementalDelivery.Tests.ListExecutionCoverage
open GraphQL.IncrementalDelivery.Execution
open Correctness

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [.object
        {
          name := "User",
          fields :=
            [
              { name := "required", outputType := .nonNull (.named "String") },
              { name := "a", outputType := .named "String" }
            ]
        }]
  }

private def resolvers : Resolvers Nat :=
  { resolve := fun _ _ _ _ => none, resolve_argumentsEquivalent := by intros; rfl }

private def selected (name : Name) : List FieldDetails :=
  [{ fieldName := "users", arguments := [], selectionSet := [defer [field name]] }]

private def values : List (ResolverValue Nat) := [.object "User" 0, .object "User" 1]
private def path : ResponsePath := [.field "users"]
private def itemType : TypeRef := .nonNull (.named "User")

private def completed (name : Name) (index : Nat) :=
  ((completeListValue schema resolvers [] 2 itemType (selected name) values path index
      [] []).run
    0).1

private theorem valid (name : Name)
    : ∀ field ∈ selected name, ArgumentValidity.FieldArgumentsValid [] field := by
  intro field member
  simp only [selected, List.mem_singleton] at member
  subst field
  constructor <;> cbv

/-- Every actual non-null user item has the checked named/wrapper comparison.
Witness: fuel-zero field values, the actual named-type plan, then guarded non-null wrapping.
-/
private theorem itemsCovered (containers : Bool) (name : Name) (index : Nat)
    : ItemsCompletionCovered containers path index
        (GraphQL.Execution.completeValueList schema resolvers [] 2 itemType
          ((selected name).map Semantics.eraseField) values)
        (completed name index) := by
  apply completeListValue_entriesCovered_of_items containers schema resolvers [] 2
    itemType (selected name) values path index [] []
  intro resolved itemPath
  apply completeValue_nonNull_entriesCovered_of_inner containers schema resolvers [] 1
    (.named "User") (selected name) resolved (valid name) itemPath [] [] false
  exact completeValue_named_entriesCovered_of_values containers schema resolvers [] 0
    (valueCompletionCoverage_zero containers schema resolvers []) "User" (selected name)
    resolved (valid name) itemPath [] [] false

/-- Nullable errors leave two partial non-null items and two retained child failures.
Witness: actual execution distinguishes two ordinary errors from zero initial errors.
-/
example
    : GraphQL.Execution.completeValueList schema resolvers [] 2 itemType
          ((selected "a").map Semantics.eraseField) values
        = .ok ([.object [("a", .null)], .object [("a", .null)]], 2)
      ∧ (completed "a" 3).result = .ok ([.object [], .object []], 0) := by
  constructor <;> cbv

/-- Actual item traversal covers reference entries at a nonzero absolute list offset.
Witness: threaded list composition, not reset-to-zero paths or error-free reconstruction.
-/
example (containers : Bool)
    : EntriesCovered containers
        (TypedResponse.items path 3 [.object [("a", .null)], .object [("a", .null)]])
        (preparedItemPositions containers path 3 [.object [], .object []]
          (completed "a" 3).work) (completed "a" 3).work := by
  obtain ⟨initial, errors, same, covered⟩ := itemsCovered containers "a" 3 _ 2 (by cbv)
  have actual : (completed "a" 3).result = .ok ([.object [], .object []], 0) := by cbv
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  exact covered

/-- Required errors bubble the ordinary list, while actual initial items remain partial.
Witness: two deferred item failures are retained rather than reported as initial errors.
-/
example
    : GraphQL.Execution.completeValueList schema resolvers [] 2 itemType
          ((selected "required").map Semantics.eraseField) values
        = .error 2
      ∧ (completed "required" 0).result = .ok ([.object [], .object []], 0) := by
  constructor <;> cbv

/-- Nullable list catching explains an ordinary null through retained item descendants.
Witness: the actual list seed and independently proved ordinary bubbling reflection.
-/
example (containers : Bool)
    : EntriesCovered containers (TypedResponse.value path .null)
        (preparedValuePositions containers path (.list [.object [], .object []])
          (completed "required" 0).work) (completed "required" 0).work := by
  obtain ⟨slices, seeded, _⟩ := Semantics.MixedPaths.completeListValue_seeded schema resolvers
    [] 2 itemType (selected "required") values path 0 [] [] 0
  have reflected := OrdinaryFailures.completeListValue_explains_failures schema resolvers
    [] 2 itemType (selected "required") values (valid "required") path 0 [] [] 0
  have covered := (itemsCovered containers "required" 0).catchList seeded reflected
  obtain ⟨initial, errors, same, covered⟩ := covered .null 2 (by cbv)
  have actual : ((completed "required" 0).catchNull ResponseValue.list).result
      = .ok (.list [.object [], .object []], 0) := by cbv
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  simpa only [Completion.catchNull,
    show (completed "required" 0).result
      = .ok ([.object [], .object []], 0) from by cbv]
    using covered

#print axioms ItemsCompletionCovered.cons
#print axioms completeListValue_entriesCovered_of_items
#print axioms completeListValue_entriesCovered_of_values
#print axioms ItemsCompletionCovered.catchList
#print axioms completeListValueWithStream_entriesCovered_of_inactive

end GraphQL.IncrementalDelivery.Tests.ListExecutionCoverage
