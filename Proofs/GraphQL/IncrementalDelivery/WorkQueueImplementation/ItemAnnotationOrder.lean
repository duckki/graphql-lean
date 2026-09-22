import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationAnnotationOrder

/-! Ordered item-inventory prefixes identify publications under the joint annotation matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A matching annotation contributes one item label per stream payload and none otherwise.
Witness: stream publication descriptors require singleton values; object/control events
have no item labels or item payloads.
-/
theorem AnnotationMatches.itemCount {work entry} (known : AnnotationMatches work entry)
    : (itemAnnotation entry).toList.length = (normalizedItemValues entry.2).length := by
  obtain ⟨source, event⟩ := entry
  cases event with
  | streamValues stream values groups streams =>
      cases source with
      | none => exact False.elim (known trivial)
      | some occurrence =>
          cases values with
          | nil => cases known
          | cons value rest =>
              cases rest with
              | nil => rfl
              | cons next tail => cases known
  | groupValues | groupSuccess | groupFailure | streamSuccess | streamFailure
    | workQueueTermination => cases source <;> rfl

/-- Item labels before a cutoff are exactly the inventory prefix counted by those payloads.
Witness: singleton item annotations equate filtered-label and payload counts; filtering a
list prefix retains precisely that initial segment of the whole item-label sequence.
-/
theorem itemAnnotation_prefix {work : Execution.Work}
    {annotated : List PublicationAnnotation}
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry) (index : Nat)
    : (annotated.take index).filterMap itemAnnotation
      = (annotated.filterMap itemAnnotation).take
          (((annotated.map Prod.snd).take index).flatMap
            normalizedItemValues).length := by
  have counts (entries : List PublicationAnnotation)
      (matching : ∀ entry ∈ entries, AnnotationMatches work entry)
      : (entries.filterMap itemAnnotation).length
        = ((entries.map Prod.snd).flatMap normalizedItemValues).length := by
    induction entries with
    | nil => rfl
    | cons head rest ih =>
        have first := (matching head List.mem_cons_self).itemCount
        have later := ih (fun next member => matching next (List.mem_cons_of_mem _ member))
        cases selected : itemAnnotation head with
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
  rw [filterMap_take_count]
  have count := counts (annotated.take index)
    (fun entry member => known entry (List.mem_of_mem_take member))
  simpa only [List.map_take]
    using congrArg (fun size => (annotated.filterMap itemAnnotation).take size) count

/-- An item label in an annotated prefix is Published under that exact full-history matching.
Witness: recover its retained annotation index; the selected item event is value-bearing
and its occurrence is the original label, without comparing response payloads.
-/
theorem annotationMatching_published_item {annotated : List PublicationAnnotation}
    {index occurrence}
    (member : occurrence ∈ (annotated.take index).filterMap itemAnnotation)
    : Published (annotationMatching annotated) ((annotated.map Prod.snd).take index)
        occurrence := by
  obtain ⟨entry, earlier, selected⟩ := List.mem_filterMap.mp member
  obtain ⟨position, atPrefix⟩ := List.mem_iff_getElem?.mp earlier
  have bound : position < index := by
    have size := (List.getElem?_eq_some_iff.mp atPrefix).choose
    simp only [List.length_take] at size
    omega
  have atEntry := (List.getElem?_take_of_lt bound).symm.trans atPrefix
  obtain ⟨source, value⟩ := itemAnnotation_some selected
  refine ⟨position, entry.2, ?_, value, ?_⟩
  · rw [List.getElem?_take_of_lt bound, List.getElem?_map, atEntry]
    rfl
  · have same : entry = (some occurrence, entry.2) := Prod.ext source rfl
    rw [same] at atEntry
    simp only [annotationMatching, atEntry]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
