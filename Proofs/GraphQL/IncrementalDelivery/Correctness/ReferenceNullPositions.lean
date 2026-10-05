import Proofs.GraphQL.IncrementalDelivery.Correctness.TypedListMerging

/-! Typed null entries justify the public reference-response bubbling test. -/

namespace GraphQL.IncrementalDelivery.Correctness.TypedResponse
open GraphQL.IncrementalDelivery.Execution

/-- The public null test is exactly successful lookup of an existing null value.
Witness: path induction follows the same alias and list-index lookups in both definitions.
Missing paths and paths descending through null are not mistaken for existing nulls.
-/
theorem isNullAt_iff_atPath_null (path : ResponsePath) (data : ResponseValue)
    : data.isNullAt path = true ↔ atPath path data = some .null := by
  induction path generalizing data with
  | nil => cases data <;> simp [GraphQL.Execution.ResponseValue.isNullAt, atPath]
  | cons segment rest ih =>
      cases segment with
      | field name =>
          cases data with
          | null | scalar _ | list _ =>
              simp [GraphQL.Execution.ResponseValue.isNullAt, atPath]
          | object fields =>
              cases found : fields.find? (fun field => field.1 == name) with
              | none => simp [GraphQL.Execution.ResponseValue.isNullAt, atPath, found]
              | some field =>
                  simp [GraphQL.Execution.ResponseValue.isNullAt, atPath, found, ih]
      | index index =>
          cases data with
          | null | scalar _ | object _ =>
              simp [GraphQL.Execution.ResponseValue.isNullAt, atPath]
          | list items =>
              cases found : items[index]? with
              | none => simp [GraphQL.Execution.ResponseValue.isNullAt, atPath, found]
              | some item =>
                  simp [GraphQL.Execution.ResponseValue.isNullAt, atPath, found, ih]

/-- A unique typed null entry is an actual null position in the reference response.
Witness: typed-entry lookup identifies its value; the null tag excludes every other
constructor. Position uniqueness rules out an ambiguous repeated alias.
-/
theorem isNullAt_of_null_entry (path : ResponsePath) (data : ResponseValue)
    (member : (path, Atom.null) ∈ value [] data)
    (unique : ((value [] data).map Prod.fst).Nodup)
    : data.isNullAt path = true := by
  obtain ⟨found, lookup, atom⟩ := atPath_of_entry [] path data .null
    (by simpa only [List.nil_append] using member) unique
  apply (isNullAt_iff_atPath_null path data).mpr
  cases found <;> simp only [rootAtom] at atom
  · exact lookup
  all_goals contradiction

/-- Every publicly recognized null has a typed null entry in the response.
Witness: successful lookup contributes its root entry to the whole typed inventory.
This direction does not require unique fields or positions.
-/
theorem null_entry_of_isNullAt (path : ResponsePath) (data : ResponseValue)
    (isNull : data.isNullAt path = true)
    : (path, Atom.null) ∈ value [] data := by
  have lookup := (isNullAt_iff_atPath_null path data).mp isNull
  have subtree := atPath_entries_sublist [] path data .null lookup
  exact subtree.subset (by simp [value])

/-- On unique responses, the public null test and typed null membership agree.
Witness: the two lookup/entry bridges, independent of execution or scheduler assumptions.
-/
theorem isNullAt_iff_null_entry (path : ResponsePath) (data : ResponseValue)
    (unique : ((value [] data).map Prod.fst).Nodup)
    : data.isNullAt path = true ↔ (path, Atom.null) ∈ value [] data :=
  ⟨
    null_entry_of_isNullAt path data,
    fun member => isNullAt_of_null_entry path data member unique
  ⟩

end GraphQL.IncrementalDelivery.Correctness.TypedResponse
