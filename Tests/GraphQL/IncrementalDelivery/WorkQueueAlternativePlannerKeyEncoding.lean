import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PlannerKeyEncoding

/-! Decimal delimiter boundaries, exact recovery and same-forest key comparisons.
The mathematical safe-integer bound does not certify native Number formatting.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerKeyEncoding.Tests

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning

example : DecimalTupleEncoding := DecimalTupleEncoding_holds
example : ForestStringKeyOptimization := ForestStringKeyOptimization_holds

example : encode [] = "" := rfl
example : encode [0] = "0" := rfl
example : encode [1, 23] = "1,23" := rfl

example : decode (encode [12, 0, 12, 3]) = [12, 0, 12, 3] :=
  DecimalTupleEncoding_holds _

example : encode [] ≠ encode [0] := by
  simp only [ne_eq, encode_eq_iff]
  decide

example : encode [1, 23] ≠ encode [12, 3] := by
  simp only [ne_eq, encode_eq_iff]
  decide

-- Concatenation without token boundaries is not an injective key encoding.
example : String.join ([1, 23].map Nat.repr) = String.join ([12, 3].map Nat.repr) := rfl

-- Serialization preserves tuple order and multiplicity, not just set membership.
example : encode [1, 1, 2] ≠ encode [2, 1] := by
  simp only [ne_eq, encode_eq_iff]
  decide

private def forest : Forest :=
  .node 10 (.node 11 (.node 12 .empty .empty) .empty) (.node 20 .empty .empty)

private theorem unique : forest.keys.Nodup := by decide

private def detail (key : Nat) (ancestors : List Nat := []) : FieldDetails :=
  {
    fieldName := "field",
    arguments := [],
    selectionSet := [],
    deferUsage := some { ref := key, ancestors }
  }

private def left : List FieldDetails := [detail 12 [11, 10], detail 20, detail 10]
private def right : List FieldDetails := [detail 10, detail 20]

private theorem leftFrom : FieldsFromForest forest left := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, left, detail]

private theorem rightFrom : FieldsFromForest forest right := by
  simp [FieldsFromForest, forest, Forest.encode, Forest.keys, right, detail]

example
    : stringKey (makeIndex (forest.encode 0 [])) left
      = stringKey (makeIndex (forest.encode 0 [])) right :=
  (ForestStringKeyOptimization_holds forest unique left right leftFrom rightFrom).2
    (by rfl)

example
    : stringKey (makeIndex (StackPlanning.traverse forest).completed) left
      = stringKey (makeIndex (StackPlanning.traverse forest).completed) right :=
  (stack_stringKey_eq_iff forest unique left right leftFrom rightFrom).2 (by rfl)

example (key : Nat) (present : key ∈ forest.keys)
    : let span := makeIndex (forest.encode 0 []) key
      span.start < maxSafeOrdinal ∧ span.stop ≤ maxSafeOrdinal :=
  forest_index_safe forest unique (by decide) key present

#print axioms DecimalTupleEncoding_holds
#print axioms ForestStringKeyOptimization_holds
#print axioms stack_stringKey_eq_iff
#print axioms forest_index_safe

end
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerKeyEncoding.Tests
