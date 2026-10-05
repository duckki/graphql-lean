import Proofs.GraphQL.IncrementalDelivery.Correctness.ValueWrapperCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Nullable object bubbles and non-null objects with nullable errors use different witnesses. -/

namespace GraphQL.IncrementalDelivery.Tests.ValueWrapperCoverage
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
  [{ fieldName := "user", arguments := [], selectionSet := [defer [field name]] }]

private def path : ResponsePath := [.field "user"]
private def source : ResolverValue Nat := .object "User" 0

private def requiredCompleted :=
  ((completeValue schema resolvers [] 2 (.named "User") (selected "required") source path
      [] [] true).run
    0).1

private def nullableCompleted :=
  ((completeValue schema resolvers [] 2 (.nonNull (.named "User")) (selected "a") source
      path [] [] true).run
    0).1

private theorem valid (name : Name)
    : ∀ field ∈ selected name, ArgumentValidity.FieldArgumentsValid [] field := by
  intro field member
  simp only [selected, List.mem_singleton] at member
  subst field
  constructor <;> cbv

/-- Deferred required failure nulls the ordinary user but leaves an error-free partial user. -/
example
    : GraphQL.Execution.completeValue schema resolvers [] 2 (.named "User")
          ((selected "required").map Semantics.eraseField) source
        = .ok (.null, 1)
      ∧ requiredCompleted.result = .ok (.object [], 0) := by
  constructor <;> cbv

/-- Named-type comparison proves nullable ancestor coverage from actual object execution. -/
private theorem requiredCovered (containers : Bool)
    : EntriesCovered containers (TypedResponse.value path .null)
        (preparedValuePositions containers path (.object []) requiredCompleted.work)
        requiredCompleted.work := by
  have covered := completeValue_named_entriesCovered_of_values containers schema resolvers [] 0
    (valueCompletionCoverage_zero containers schema resolvers []) "User" (selected "required")
    source (valid "required") path [] [] true 0
  obtain ⟨initial, errors, same, covered⟩ := covered .null 1 (by cbv)
  have actual : requiredCompleted.result = .ok (.object [], 0) := by cbv
  change requiredCompleted.result = .ok (initial, errors) at same
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  exact covered

/-- The named-type witness constructs a prepared certificate for the nullable user. -/
example (containers : Bool)
    : PreparedResponseCovers (.object [("user", .null)])
        { data := .object [("user", .object [])] } requiredCompleted.work containers := by
  apply EntriesCovered.to_prepared
  · apply EntriesCovered.object
    simpa only [TypedResponse.fields, List.append_nil, preparedFieldPositions_singleton,
      path, List.nil_append]
      using requiredCovered containers
  · decide

/-- A deferred nullable field counts an error without nulling the non-null ordinary user. -/
example
    : GraphQL.Execution.completeValue schema resolvers [] 2 (.nonNull (.named "User"))
          ((selected "a").map Semantics.eraseField) source
        = .ok (.object [("a", .null)], 1)
      ∧ nullableCompleted.result = .ok (.object [], 0) := by
  constructor <;> cbv

/-- Actual non-null completion keeps covered data and future work despite nullable errors. -/
private theorem nullableCovered (containers : Bool)
    : EntriesCovered containers (TypedResponse.value path (.object [("a", .null)]))
        (preparedValuePositions containers path (.object []) nullableCompleted.work)
        nullableCompleted.work := by
  have inner := completeValue_named_entriesCovered_of_values containers schema resolvers [] 0
    (valueCompletionCoverage_zero containers schema resolvers []) "User" (selected "a") source
    (valid "a") path [] [] true
  have covered := completeValue_nonNull_entriesCovered_of_inner containers schema resolvers [] 1
    (.named "User") (selected "a") source (valid "a") path [] [] true inner 0
  obtain ⟨initial, errors, same, covered⟩ := covered (.object [("a", .null)]) 1 (by cbv)
  have actual : nullableCompleted.result = .ok (.object [], 0) := by cbv
  change nullableCompleted.result = .ok (initial, errors) at same
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  exact covered

/-- Non-null object coverage assembles into a full prepared reference with nullable errors. -/
example (containers : Bool)
    : PreparedResponseCovers (.object [("user", .object [("a", .null)])])
        { data := .object [("user", .object [])] } nullableCompleted.work containers := by
  apply EntriesCovered.to_prepared
  · apply EntriesCovered.object
    simpa only [TypedResponse.fields, List.append_nil, preparedFieldPositions_singleton,
      path, List.nil_append]
      using nullableCovered containers
  · decide

#print axioms FieldsCompletionCovered.catchObject
#print axioms ValueCompletionCovered.nonNull
#print axioms completeValue_named_entriesCovered_of_values
#print axioms completeValue_nonNull_entriesCovered_of_inner

end GraphQL.IncrementalDelivery.Tests.ValueWrapperCoverage
