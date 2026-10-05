import Proofs.GraphQL.IncrementalDelivery.Correctness.RecursiveValueCoverage
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Actual streamed prefixes/tails and general client-facing failure coverage. -/

namespace GraphQL.IncrementalDelivery.Tests.StreamExecutionCoverage
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

private def selected (name : Name) (count : Nat) : List FieldDetails :=
  [{
    fieldName := "users"
    arguments := []
    selectionSet := [defer [field name]]
    directives := [.stream (.boolean true) none (.int (Int.ofNat count))]
  }]

private def values : List (ResolverValue Nat) := [.object "User" 0, .object "User" 1]
private def path : ResponsePath := [.field "users"]

private def completed (name : Name) (count : Nat) (itemType : TypeRef) :=
  ((completeListValueWithStream schema resolvers [] 20 itemType (selected name count)
      values path [] [] true).run
    0).1

private theorem valid (name : Name) (count : Nat)
    : ∀ field ∈ selected name count, ArgumentValidity.FieldArgumentsValid [] field := by
  intro field member
  simp only [selected, List.mem_singleton] at member
  subst field
  constructor <;> cbv <;> omega

/-- The proved recursive value comparison discharges both sides of the actual stream hook.
Witness: no supplied per-item coverage or zero-error premise remains.
-/
private theorem covered (containers : Bool) (name : Name) (count : Nat)
    (itemType : TypeRef)
    : ValueCompletionCovered containers path
        (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
          (GraphQL.Execution.completeValueList schema resolvers [] 20 itemType
            ((selected name count).map Semantics.eraseField) values))
        (completed name count itemType) :=
  completeListValueWithStream_entriesCovered_of_values containers schema resolvers [] 20
    (valueCompletionCoverage_holds containers schema resolvers [] 20) itemType
    (selected name count) values (valid name count) path [] [] true 0

/-- Required child failures null both ordinary users but leave a partial initial prefix.
Witness: actual execution has zero initial errors and retains both deferred failures.
-/
example
    : GraphQL.Execution.completeValueList schema resolvers [] 20 (.named "User")
          ((selected "required" 1).map Semantics.eraseField) values
        = .ok ([.null, .null], 2)
      ∧ (completed "required" 1 (.named "User")).result
        = .ok (.list [.object []], 0) := by
  constructor <;> cbv

/-- Both prefix and tail nulls are covered by real failures beneath their partial objects.
Witness: the complete recursive comparison followed by singleton/object assembly.
-/
example (containers : Bool)
    : PreparedResponseCovers (.object [("users", .list [.null, .null])])
        { data := .object [("users", .list [.object []])] }
        (completed "required" 1 (.named "User")).work containers := by
  obtain ⟨initial, errors, same, covered⟩ := covered containers "required" 1 (.named "User")
    (.list [.null, .null]) 2 (by cbv)
  have actual : (completed "required" 1 (.named "User")).result
      = .ok (.list [.object []], 0) := by cbv
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  apply EntriesCovered.to_prepared
  · apply EntriesCovered.object
    simpa only [TypedResponse.fields, List.append_nil, preparedFieldPositions_singleton,
      path, List.nil_append] using covered
  · decide

/-- An ordinary nullable-list bubble is covered even when the actual initial prefix lives.
Witness: actual non-null item failure reflection, not equality of ordinary/initial data.
-/
example (containers : Bool)
    : EntriesCovered containers (TypedResponse.value path .null)
        (preparedValuePositions containers path (.list [.object []])
          (completed "required" 1 (.nonNull (.named "User"))).work)
        (completed "required" 1 (.nonNull (.named "User"))).work := by
  obtain ⟨initial, errors, same, covered⟩ := covered containers "required" 1
    (.nonNull (.named "User")) .null 2 (by cbv)
  have actual : (completed "required" 1 (.nonNull (.named "User"))).result
      = .ok (.list [.object []], 0) := by cbv
  rw [actual] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same).symm
  exact covered

/-- Counts at and beyond exhaustion both retain nested failure-aware coverage.
Witness: the actual hook keeps the exhausted boundary but skips a never-reached boundary.
-/
example (containers : Bool)
    : ValueCompletionCovered containers path
        (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
          (GraphQL.Execution.completeValueList schema resolvers [] 20 (.named "User")
            ((selected "a" 2).map Semantics.eraseField) values))
        (completed "a" 2 (.named "User"))
      ∧ ValueCompletionCovered containers path
          (GraphQL.Execution.catchBubbleAsNull ResponseValue.list
            (GraphQL.Execution.completeValueList schema resolvers [] 20 (.named "User")
              ((selected "a" 3).map Semantics.eraseField) values))
          (completed "a" 3 (.named "User")) :=
  ⟨covered containers "a" 2 (.named "User"), covered containers "a" 3 (.named "User")⟩

/-- An initially empty stream boundary has covered empty-list data and nonempty work.
Witness: actual zero-item execution plus the general recursive stream-hook comparison.
-/
example (containers : Bool)
    : let empty :=
        ((completeListValueWithStream schema resolvers [] 0 (.named "String")
            (selected "a" 0) [] path [] [] true).run
          0).1
      empty.work ≠ .empty
      ∧ ValueCompletionCovered containers path (.ok (.list [], 0)) empty := by
  dsimp only
  constructor
  · cbv
    intro same
    cases same
  · simpa only [GraphQL.Execution.completeValueList, GraphQL.Execution.catchBubbleAsNull]
      using completeListValueWithStream_entriesCovered_of_values containers schema
        resolvers [] 0 (valueCompletionCoverage_zero containers schema resolvers [])
        (.named "String") (selected "a" 0) [] (valid "a" 0) path [] [] true 0

/-- The public client-facing failure-coverage statement has an unconditional proof witness.
Witness: recursive pure execution coverage plus the independent terminal reporting law.
-/
example (schema : Schema) (operation : Operation)
    : ResponsePositionsDeliveredOrFailed schema operation :=
  ResponsePositionsDeliveredOrFailed_holds schema operation

#print axioms EntriesCovered.streamPrefix
#print axioms completeListValueWithStream_listEntriesCovered_of_values
#print axioms completeListValueWithStream_entriesCovered_of_values
#print axioms valueCompletionCoverage_holds
#print axioms responseFieldCoverage_holds
#print axioms ResponsePositionsDeliveredOrFailed_holds

end GraphQL.IncrementalDelivery.Tests.StreamExecutionCoverage
