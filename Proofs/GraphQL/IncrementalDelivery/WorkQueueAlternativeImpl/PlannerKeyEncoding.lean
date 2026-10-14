import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.StackPlanning
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas.Intercalate
import Init.Data.List.SplitOn.Lemmas

/-! Collision-free comma-separated decimal encoding of numeric planner tuples. Lean Nat
decimal formatting is proved here; concrete number precision/formatting and string/map
correspondence remain distinct obligations. Neither a hash nor a queue identity is added.
-/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerKeyEncoding

open GraphQL.IncrementalDelivery.Execution
open PreorderPlanning IntervalPlanning

-----------------------------------------------------------------------------------------
-- Decimal tuple serialization and its exact inverse on encoded keys
-----------------------------------------------------------------------------------------

def encode (keys : List Nat) : String := ",".intercalate (keys.map Nat.repr)

/-- Empty tuple is the empty string, not a singleton empty decimal token. This inverse
is specified only on encode's output; it is not a public parser for arbitrary strings.
-/
def decode (text : String) : List Nat :=
  if text = "" then
    []
  else
    (text.toList.splitOn ',').map (fun digits => Nat.ofDigitChars 10 digits 0)

def DecimalTupleEncoding : Prop := ∀ keys : List Nat, decode (encode keys) = keys

def stringKey (index : Index) (fields : List FieldDetails) : String :=
  encode (tupleKey index fields)

def ForestStringKeyOptimization : Prop :=
  ∀ forest : Forest,
    forest.keys.Nodup
    → ∀ left right,
        FieldsFromForest forest left
        → FieldsFromForest forest right
        → (stringKey (makeIndex (forest.encode 0 [])) left
              = stringKey (makeIndex (forest.encode 0 [])) right
            ↔ deferUsageSetsEquivalent (getFilteredDeferUsageSet left)
                (getFilteredDeferUsageSet right)
              = true)

-----------------------------------------------------------------------------------------
-- Token boundaries are unambiguous and decimal parsing recovers each ordinal
-----------------------------------------------------------------------------------------

private theorem comma_absent (key : Nat) : ',' ∉ Nat.toDigits 10 key := by
  intro present
  have digit := Nat.isDigit_of_mem_toDigits (by decide) (by decide) present
  contradiction

theorem encode_ne_empty (keys : List Nat) (nonempty : keys ≠ []) : encode keys ≠ "" := by
  cases keys with
  | nil => contradiction
  | cons head rest =>
      cases rest with
      | nil => simp [encode]
      | cons next tail => simp [encode, String.append_eq_empty_iff]

theorem DecimalTupleEncoding_holds : DecimalTupleEncoding := by
  intro keys
  cases keys with
  | nil => simp [decode, encode]
  | cons head rest =>
      have nonempty := encode_ne_empty (head :: rest) (by simp)
      have characters : (encode (head :: rest)).toList
          = [','].intercalate ((head :: rest).map (Nat.toDigits 10)) := by
        simp [encode, String.toList_intercalate, List.map_map, Function.comp_def]
      have separated : ([','].intercalate ((head :: rest).map (Nat.toDigits 10))).splitOn ','
          = (head :: rest).map (Nat.toDigits 10) := by
        apply List.splitOn_intercalate
        · intro digits present
          obtain ⟨key, _, rfl⟩ := List.mem_map.mp present
          exact comma_absent key
        · simp
      simp only [decode, nonempty, ↓reduceIte, characters, separated, List.map_map]
      simp [Function.comp_def, Nat.ofDigitChars_ten_toDigits]

theorem encode_eq_iff (left right : List Nat)
    : encode left = encode right ↔ left = right := by
  constructor
  · intro same
    have recovered := congrArg decode same
    rw [DecimalTupleEncoding_holds left, DecimalTupleEncoding_holds right] at recovered
    exact recovered
  · exact congrArg encode

theorem ForestStringKeyOptimization_holds : ForestStringKeyOptimization := by
  intro forest unique left right leftFrom rightFrom
  rw [stringKey, stringKey, encode_eq_iff]
  exact forest_tupleKey_eq_iff forest unique left right leftFrom rightFrom

theorem stack_stringKey_eq_iff (forest : Forest) (unique : forest.keys.Nodup)
    (left right : List FieldDetails)
    (leftFrom : FieldsFromForest forest left) (rightFrom : FieldsFromForest forest right)
    : stringKey (makeIndex (StackPlanning.traverse forest).completed) left
        = stringKey (makeIndex (StackPlanning.traverse forest).completed) right
      ↔ deferUsageSetsEquivalent (getFilteredDeferUsageSet left)
          (getFilteredDeferUsageSet right)
        = true := by
  rw [StackPlanning.traverse_index forest unique]
  exact ForestStringKeyOptimization_holds forest unique left right leftFrom rightFrom

-----------------------------------------------------------------------------------------
-- Native arithmetic needs its own representation bound, not a new queue premise
-----------------------------------------------------------------------------------------

def maxSafeOrdinal : Nat := 2 ^ 53 - 1

theorem forest_index_safe (forest : Forest) (unique : forest.keys.Nodup)
    (fits : forest.keys.length ≤ maxSafeOrdinal) (key : Nat) (present : key ∈ forest.keys)
    : let span := makeIndex (forest.encode 0 []) key
      span.start < maxSafeOrdinal ∧ span.stop ≤ maxSafeOrdinal := by
  have bounds := forest_index_bounds forest unique key present
  omega

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.PlannerKeyEncoding
