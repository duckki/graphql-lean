import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamFailureCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Plain streaming coverage distinguishes nullable item errors from bubbled tail failure. -/

namespace GraphQL.IncrementalDelivery.Tests.StreamFailureCoverage
open GraphQL.IncrementalDelivery.Execution
open Correctness

private def nullableFields : List FieldDetails :=
  [{
    fieldName := "users"
    arguments := []
    selectionSet := [field "required"]
    directives := [.stream (.boolean true) none (.int 0)]
  }]

private def nullableCompleted :=
  ((completeListValueWithStream schema resolvers [] 30 (.named "User") nullableFields
      [.object "User" 1] [] [] [] true).run
    0).1

/-- A nullable item error delivers the same null item as ordinary execution.
Witness: the actual stream hook's coverage certificate, including its positive-error
successful item. Such an item need not produce a failed completion scope.
-/
example (containers : Bool)
    : PreparedResponseCovers (.list [.null]) { data := .list [], errors := 0 }
        nullableCompleted.work containers := by
  have certified := completeListValueWithStream_plain_coverage schema resolvers [] 30
    (.named "User") nullableFields [.object "User" 1] none
    (by simp [Semantics.ContextWellFormed]) []
    (by intro field member; simp [nullableFields] at member; subst field; exact ⟨rfl, rfl⟩)
    (by intro field member; simp [nullableFields] at member; subst field; exact ⟨rfl, rfl⟩)
    true 0 containers
  dsimp only at certified
  obtain ⟨data, errors, initial, covered⟩ := certified
  change nullableCompleted.result = .ok (data, errors) at initial
  have actual : nullableCompleted.result = .ok (.list [], 0) := by cbv
  rw [actual] at initial
  obtain ⟨rfl, rfl⟩ := Except.ok.inj initial
  have ordinary : GraphQL.Execution.completeValueList schema resolvers [] 30 (.named "User")
      (nullableFields.map Semantics.eraseField) [.object "User" 1] = .ok ([.null], 1) := by
    cbv
  rw [ordinary] at covered
  exact covered

private def strictFields : List FieldDetails :=
  [{
    fieldName := "strict"
    arguments := []
    selectionSet := []
    directives := [.stream (.boolean true) none (.int 1)]
  }]

private def strictCompleted :=
  ((completeListValueWithStream schema resolvers [] 30 (.nonNull (.named "String"))
      strictFields [.scalar "x", .null, .scalar "z"] [] [] [] true).run
    0).1

/-- A later non-null item failure explains the ordinary null list via a retained task.
Witness: the stream hook's coverage certificate; the initial successful item remains
visible, while the failed task is attached to the list, not an invented absolute index.
-/
example (containers : Bool)
    : PreparedResponseCovers .null { data := .list [.scalar "x"], errors := 0 }
        strictCompleted.work containers := by
  have certified := completeListValueWithStream_plain_coverage schema resolvers [] 30
    (.nonNull (.named "String")) strictFields [.scalar "x", .null, .scalar "z"] none
    (by simp [Semantics.ContextWellFormed]) []
    (by intro field member; simp [strictFields] at member; subst field; exact ⟨rfl, rfl⟩)
    (by intro field member; simp [strictFields] at member; subst field; exact ⟨rfl, rfl⟩)
    true 0 containers
  dsimp only at certified
  obtain ⟨data, errors, initial, covered⟩ := certified
  change strictCompleted.result = .ok (data, errors) at initial
  have actual : strictCompleted.result = .ok (.list [.scalar "x"], 0) := by cbv
  rw [actual] at initial
  obtain ⟨rfl, rfl⟩ := Except.ok.inj initial
  have ordinary : GraphQL.Execution.completeValueList schema resolvers [] 30
      (.nonNull (.named "String")) (strictFields.map Semantics.eraseField)
      [.scalar "x", .null, .scalar "z"] = .error 1 := by cbv
  rw [ordinary] at covered
  exact covered

end GraphQL.IncrementalDelivery.Tests.StreamFailureCoverage
