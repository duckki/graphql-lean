import Proofs.GraphQL.IncrementalDelivery.Correctness.StreamSuccessAlignment
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Ordinary nullable item failures keep actual partial items and failed child work. -/

namespace GraphQL.IncrementalDelivery.Tests.StreamSuccessAlignment
open GraphQL.IncrementalDelivery.Execution
open Correctness

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [.object
        {
          name := "User",
          fields := [{ name := "required", outputType := .nonNull (.named "String") }]
        }]
  }

private def resolvers : Resolvers Nat :=
  { resolve := fun _ _ _ _ => none, resolve_argumentsEquivalent := by intros; rfl }

private def selected : List FieldDetails :=
  [{ fieldName := "users", arguments := [], selectionSet := [defer [field "required"]] }]

private def values : List (ResolverValue Nat) := [.object "User" 1, .object "User" 2]
private def path : ResponsePath := [.field "users"]
private def node : DeliveryNode := { ref := 10, path }

private def items :=
  ((completeStreamItems schema resolvers [] 20 (.named "User") selected values path 0).run
    0).1

private theorem valid
    : ∀ field ∈ selected, ArgumentValidity.FieldArgumentsValid [] field := by
  intro field member
  simp only [selected, List.mem_singleton] at member
  subst field
  constructor <;> cbv

/-- Ordinary items are nullable nulls, while both actual items expose partial objects. -/
private theorem ordinarySuccess
    : GraphQL.Execution.completeValueList schema resolvers [] 20 (.named "User")
        (selected.map Semantics.eraseField) values
      = .ok ([.null, .null], 2) := by
  cbv

/-- General alignment keeps the full tail without assuming error-count agreement. -/
example
    : items.length = 2
      ∧ ∀ entry ∈ items, entry.1 = { result := .ok (.object [], 0) } := by
  have aligned := completeStreamItems_aligns_ordinarySuccess schema resolvers [] 20
    (.named "User") selected values valid path 0 0 [.null, .null] 2 ordinarySuccess
  constructor
  · exact aligned.1
  · intro entry member
    have results : items.map Prod.fst = [{ result := .ok (.object [], 0) }, { result := .ok (.object [], 0) }] := by cbv
    have present : entry.1 ∈ items.map Prod.fst := List.mem_map.mpr ⟨entry, member, rfl⟩
    rw [results] at present
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- Every ordinary null item is explained by its actual retained deferred child failure.
The initial partial objects have no leaf positions, so no initial-data shortcut applies.
-/
private theorem tailCovered (containers : Bool)
    : EntriesCovered containers (TypedResponse.items path 0 [.null, .null])
        ((sourceTasks [] none [(path, 0)] (.stream node items)).flatMap
          (SourceTask.positions containers)) (.stream node items) := by
  intro entry member _
  change entry ∈ [(path ++ [.index 0], .null), (path ++ [.index 1], .null)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact completeStreamItems_nullEntry_covered schema resolvers [] 20 (.named "User")
      selected values valid path 0 0 [.null, .null] 2 ordinarySuccess node rfl [(path, 0)]
      rfl 0 rfl containers
  · exact completeStreamItems_nullEntry_covered schema resolvers [] 20 (.named "User")
      selected values valid path 0 0 [.null, .null] 2 ordinarySuccess node rfl [(path, 0)]
      rfl 1 rfl containers

/-- Actual streamed null-item coverage constructs a full prepared response certificate.
Container roots are supplied by the initial empty list; null leaves use child failures.
-/
example (containers : Bool)
    : PreparedResponseCovers (.object [("users", .list [.null, .null])])
        { data := .object [("users", .list [])] } (.stream node items) containers := by
  apply EntriesCovered.to_prepared
  · intro entry member visible
    change entry ∈ [([], .object), (path, .list),
      (path ++ [.index 0], .null), (path ++ [.index 1], .null)] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · have flag : containers = true := visible
      exact Or.inl (by simp [ResponsePositions.value, flag])
    · have flag : containers = true := visible
      exact Or.inl (by simp [ResponsePositions.value, ResponsePositions.fields, path, flag])
    · have covered := tailCovered containers
        (path ++ [ResponsePathSegment.index 0], TypedResponse.Atom.null)
        (by simp [TypedResponse.items, TypedResponse.value]) rfl
      exact covered.available_mono (fun _ future => List.mem_append_right _ future)
    · have covered := tailCovered containers
        (path ++ [ResponsePathSegment.index 1], TypedResponse.Atom.null)
        (by simp [TypedResponse.items, TypedResponse.value]) rfl
      exact covered.available_mono (fun _ future => List.mem_append_right _ future)
  · decide

/-- The full streamed-tail dependency edge reuses the proved local nullable-value witness.
This exercises the reference-entry decomposition and actual per-item threaded states.
-/
example (containers : Bool)
    : EntriesCovered containers (TypedResponse.items path 0 [.null, .null])
        ((sourceTasks [] none [(path, 0)] (.stream node items)).flatMap
          (SourceTask.positions containers)) (.stream node items) := by
  apply completeStreamItems_entriesCovered_of_values schema resolvers [] 20
    (.named "User") selected values valid path 0 0 [.null, .null] 2 ordinarySuccess node
    rfl [(path, 0)] rfl containers
  intro resolved member offset itemState data errors ordinary
  have outcome : GraphQL.Execution.completeValue schema resolvers [] 20 (.named "User")
      (selected.map Semantics.eraseField) resolved = .ok (.null, 1) := by
    simp only [values, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> cbv
  have same : data = .null ∧ errors = 1 := by
    rw [outcome] at ordinary
    have paired := Prod.mk.inj (Except.ok.inj ordinary)
    exact ⟨paired.1.symm, paired.2.symm⟩
  obtain ⟨rfl, rfl⟩ := same
  exact completeValue_nullEntries_covered schema resolvers [] 20 (.named "User") selected
    resolved valid (path ++ [.index (0 + offset)]) [] [] false itemState 1 outcome
    containers

#print axioms completeStreamItems_aligns_ordinarySuccess
#print axioms completeStreamItems_entriesCovered_of_values
#print axioms completeStreamItems_nullEntry_covered

end GraphQL.IncrementalDelivery.Tests.StreamSuccessAlignment
