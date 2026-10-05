import Proofs.GraphQL.IncrementalDelivery.Correctness.ValueFailureCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Typed local null coverage survives ancestor bubbling and field assembly. -/

namespace GraphQL.IncrementalDelivery.Tests.ValueFailureCoverage
open GraphQL.IncrementalDelivery.Execution
open Correctness

private def schema : Schema :=
  {
    queryType := "Query",
    types :=
      [
        .object
          {
            name := "Query", fields := [{ name := "user", outputType := .named "User" }]
          },
        .object
          {
            name := "User",
            fields :=
              [
                { name := "child", outputType := .nonNull (.named "User") },
                { name := "required", outputType := .nonNull (.named "String") }
              ]
          }
      ]
  }

private def resolvers : Resolvers Nat :=
  {
    resolve :=
      fun _ name _ _ =>
        if name == "required" then none else some (.object "User" 1),
    resolve_argumentsEquivalent := by intros; rfl
  }

private def fields : List FieldDetails :=
  [{
    fieldName := "user",
    arguments := [],
    selectionSet :=
      [field "child" [defer [field "required"]] [] (some "details")]
  }]

private def completed :=
  ((completeValue schema resolvers [] 30 (.named "User") fields (.object "User" 1)
      [.field "viewer"] [] [] true).run
    0).1

/-- Ordinary bubbling nulls viewer, while the initial value exposes a partial descendant.
Witness: actual mixed value completion and ordinary directive-erased completion.
-/
example
    : completed.result = .ok (.object [("details", .object [])], 0)
      ∧ GraphQL.Execution.completeValue schema resolvers [] 30 (.named "User")
          (fields.map Semantics.eraseField) (.object "User" 1)
        = .ok (.null, 1) := by
  constructor <;> cbv

/-- The ordinary null leaf has coverage even though no initial leaf is available.
Witness: general mixed null-entry coverage. Its failed task attaches below viewer, so
the preserved null tag, rather than a direct scope prefix, justifies the explanation.
-/
private theorem null_covered
    : EntryExplained [] completed.work ([.field "viewer"], .null) := by
  have covered := completeValue_nullEntry_covered schema resolvers [] 30 (.named "User")
    fields (.object "User" 1) (by
      intro field member
      simp only [fields, List.mem_singleton] at member
      subst field
      constructor <;> cbv) [.field "viewer"] [] [] true 0 1 (by cbv) false []
  have initial : completed.result = .ok (.object [("details", .object [])], 0) := by cbv
  change EntryExplained
    (DeliveryPaths.result (ResponsePositions.value false [.field "viewer"])
      completed.result ++ []) completed.work ([.field "viewer"], .null) at covered
  simpa [initial, DeliveryPaths.result, ResponsePositions.value, ResponsePositions.fields]
    using covered

/-- The same null evidence survives retention beside unrelated work.
Witness: typed-entry work embedding, without allocating or assuming a failure notice.
-/
example (other : Work)
    : EntryExplained [] (.combine other completed.work) ([.field "viewer"], .null) :=
  null_covered.combine_right other

/-- Typed null coverage bridges to the public prepared reference after field assembly.
Witness: typed visible-entry projection, null lookup in the unique ordinary response,
and the actual retained child failure. No public definition is strengthened.
-/
example
    : PreparedResponseCovers (.object [("viewer", .null)])
        { data := .object [("viewer", .object [("details", .object [])])] }
        completed.work false := by
  apply EntriesCovered.to_prepared
  · intro entry member visible
    simp only [TypedResponse.value, TypedResponse.fields, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp [TypedResponse.Atom.visible] at visible
    · apply null_covered.available_mono
      intro position impossible
      cases impossible
  · decide

/-- Leaf filtering keeps null/scalar paths while dropping object/list containers.
Witness: visible typed-entry projection, at both container flag settings.
-/
example (containers : Bool)
    : visibleEntryPaths containers
        (TypedResponse.value []
          (.object [("viewer", .null), ("other", .list [.scalar "x"])]))
      = ResponsePositions.value containers []
          (.object [("viewer", .null), ("other", .list [.scalar "x"])]) :=
  visibleEntryPaths_value containers _ _

/-- Duplicate reference aliases can make a typed null differ from the public lookup.
Witness: lookup selects the first scalar, demonstrating why the final bridge requires
ordinary-response path uniqueness rather than treating every local null tag as a lookup.
-/
example
    : (.object [("same", .scalar "x"), ("same", .null)] : ResponseValue).isNullAt
        [.field "same"]
      = false := by cbv

#print axioms completeValue_nullEntry_covered
#print axioms completeValue_initialNonNull_of_ordinaryNonNull
#print axioms EntriesCovered.to_prepared

end GraphQL.IncrementalDelivery.Tests.ValueFailureCoverage
