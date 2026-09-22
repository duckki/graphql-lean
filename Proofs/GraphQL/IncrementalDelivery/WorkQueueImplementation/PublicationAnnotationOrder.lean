import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationMatching

/-! Exact object-inventory prefixes become publications under the joint output matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Count object annotations in the strict output prefix
-----------------------------------------------------------------------------------------

/-- An object annotation retains a source occurrence and marks a value event.
Witness: only a present annotation on an object-value event survives this projection. -/
theorem objectAnnotation_some {entry : PublicationAnnotation} {occurrence : Occurrence}
    (selected : objectAnnotation entry = some occurrence)
    : entry.1 = some occurrence ∧ IsValue entry.2 := by
  obtain ⟨source, event⟩ := entry
  cases source with
  | none => cases selected
  | some source => cases event <;> simp_all [objectAnnotation, IsValue]

/-- A matching annotation contributes exactly one object label per object payload.
Witness: successful object descriptors require singleton values; absent annotations mark
control events. Item annotations and control events contribute no object count.
-/
theorem AnnotationMatches.objectCount {work entry} (known : AnnotationMatches work entry)
    : (objectAnnotation entry).toList.length
      = (normalizedObjectValues entry.2).length := by
  obtain ⟨source, event⟩ := entry
  cases event with
  | groupValues group values =>
      cases source with
      | none => exact False.elim (known trivial)
      | some occurrence =>
          cases values with
          | nil => cases known
          | cons value rest =>
              cases rest with
              | nil => rfl
              | cons next tail => cases known
  | streamValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => cases source <;> rfl

/-- Filtered labels in a prefix are exactly the initial labels counted in that prefix.
Witness: induction over the list and cutoff, consuming a label only when it is present.
-/
theorem filterMap_take_count {α β : Type} (project : α → Option β)
    (entries : List α) (index : Nat)
    : (entries.take index).filterMap project
      = (entries.filterMap project).take
          ((entries.take index).filterMap project).length := by
  induction entries generalizing index with
  | nil => simp
  | cons head rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          cases selected : project head with
          | none =>
              simpa only [List.take_succ_cons, List.filterMap_cons, selected] using ih index
          | some value =>
              simpa only [List.take_succ_cons, List.filterMap_cons, selected,
                List.length_cons] using congrArg (value :: ·) (ih index)

/-- Matching annotations contain exactly one object label per object payload.
Witness: add the per-entry object counts through the annotated list.
-/
theorem objectAnnotation_length {work : Execution.Work}
    (entries : List PublicationAnnotation)
    (matching : ∀ entry ∈ entries, AnnotationMatches work entry)
    : (entries.filterMap objectAnnotation).length
      = ((entries.map Prod.snd).flatMap normalizedObjectValues).length := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      have first := (matching head List.mem_cons_self).objectCount
      have later := ih (fun next member => matching next (List.mem_cons_of_mem _ member))
      cases selected : objectAnnotation head with
      | none =>
          simp only [selected, Option.toList_none, List.length_nil] at first
          simp only [List.filterMap_cons, selected, List.map_cons, List.flatMap_cons,
            List.length_append, ← first, Nat.zero_add]
          exact later
      | some occurrence =>
          simp only [selected, Option.toList_some, List.length_cons, List.length_nil] at first
          simp only [List.filterMap_cons, selected, List.length_cons, List.map_cons,
            List.flatMap_cons, List.length_append, ← first, later]
          omega

/-- Object annotation order gives the exact object-inventory prefix before any event.
Witness: annotation counts equal object payload counts, then filtered-prefix counting
selects precisely that many labels from the whole ordered object projection.
-/
theorem objectAnnotation_prefix {work : Execution.Work}
    {annotated : List PublicationAnnotation}
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry) (index : Nat)
    : (annotated.take index).filterMap objectAnnotation
      = (annotated.filterMap objectAnnotation).take
          (((annotated.map Prod.snd).take index).flatMap
            normalizedObjectValues).length := by
  rw [filterMap_take_count]
  have count := objectAnnotation_length (annotated.take index)
    (fun entry member => known entry (List.mem_of_mem_take member))
  simpa only [List.map_take]
    using congrArg (fun size => (annotated.filterMap objectAnnotation).take size) count

/-- A retained filtered label has the rank given by the preceding retained-label count.
Witness: list/index induction skips absent labels and advances on present ones.
-/
theorem filterMap_getElem?_rank {α β : Type} (project : α → Option β)
    (entries : List α) {index : Nat} {entry : α} {value : β}
    (selected : entries[index]? = some entry) (retained : project entry = some value)
    : (entries.filterMap project)[((entries.take index).filterMap project).length]?
      = some value := by
  induction entries generalizing index with
  | nil => cases selected
  | cons head rest ih =>
      cases index with
      | zero => cases selected; simp [retained]
      | succ index =>
          have later := ih selected
          cases kept : project head <;> simpa only [List.take_succ_cons,
            List.filterMap_cons, kept, List.length_cons, List.getElem?_cons_succ] using later

/-- An object's matching occurrence is exactly the next label in the ordered object ledger.
Witness: its present annotation survives at the filtered prefix rank, whose length equals
the number of preceding object values. This is indexed identity, not payload equality.
-/
theorem annotationMatching_object_at {work : Execution.Work}
    {annotated : List PublicationAnnotation}
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry) {index : Nat}
    {group values}
    (selected : (annotated.map Prod.snd)[index]? = some (.groupValues group values))
    : let count :=
        (((annotated.map Prod.snd).take index).flatMap normalizedObjectValues).length
      (annotated.filterMap objectAnnotation)[count]?
      = some (annotationMatching annotated index) := by
  have entry := (annotationMatching_publication known selected trivial).1
  have exactLabel := filterMap_getElem?_rank objectAnnotation annotated entry rfl
  have count := objectAnnotation_length (annotated.take index)
    (fun value member => known value (List.mem_of_mem_take member))
  rw [List.map_take] at count
  rw [count] at exactLabel
  exact exactLabel

-----------------------------------------------------------------------------------------
-- Read a prefix label as an actual publication using the same full-history matching
-----------------------------------------------------------------------------------------

/-- An object label in the strict annotated prefix is already published under its matching.
Witness: recover its earlier annotation index and retain that exact lookup through `take`.
No payload comparison or new matching choice is involved.
-/
theorem annotationMatching_published_object {annotated : List PublicationAnnotation}
    {index occurrence}
    (member : occurrence ∈ (annotated.take index).filterMap objectAnnotation)
    : Published (annotationMatching annotated) ((annotated.map Prod.snd).take index)
        occurrence := by
  obtain ⟨entry, earlier, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨position, atPrefix⟩ := List.mem_iff_getElem?.mp earlier
  have bound : position < index := by
    have size := (List.getElem?_eq_some_iff.mp atPrefix).choose
    simp only [List.length_take] at size
    omega
  have atEntry := (List.getElem?_take_of_lt bound).symm.trans atPrefix
  obtain ⟨source, value⟩ := objectAnnotation_some selected
  refine ⟨position, entry.2, ?_, value, ?_⟩
  · rw [List.getElem?_take_of_lt bound, List.getElem?_map, atEntry]
    rfl
  · have same : entry = (some occurrence, entry.2) := Prod.ext source rfl
    rw [same] at atEntry
    simp only [annotationMatching, atEntry]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
