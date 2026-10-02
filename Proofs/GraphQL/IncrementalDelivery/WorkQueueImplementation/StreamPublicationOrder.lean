import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamSourceOrder

/-! The joint output matching publishes earlier stream items before later ordinals. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Recover ordered positions through the item-annotation projection
-----------------------------------------------------------------------------------------

/-- An ordered pair in a filtered projection has two increasing source-list positions.
Witness: list induction skips discarded entries and retains the two selected entries.
-/
private theorem pair_filterMap_positions {α β : Type} (project : α → Option β)
    {entries : List α} {first second : β}
    (ordered : [first, second].Sublist (entries.filterMap project))
    : ∃ (left right : Nat) (before after : α),
        left < right
        ∧ entries[left]? = some before
        ∧ entries[right]? = some after
        ∧ project before = some first
        ∧ project after = some second := by
  induction entries with
  | nil => cases ordered
  | cons head rest ih =>
      cases selected : project head with
      | none =>
          rw [List.filterMap_cons, selected] at ordered
          obtain ⟨left, right, before, after, less, atLeft, atRight, firstAt, secondAt⟩ :=
            ih ordered
          exact ⟨
            left + 1,
            right + 1,
            before,
            after,
            by omega,
            atLeft,
            atRight,
            firstAt,
            secondAt
          ⟩
      | some value =>
          rw [List.filterMap_cons, selected] at ordered
          cases ordered with
          | cons _ skipped =>
              obtain ⟨left, right, before, after, less, atLeft, atRight, firstAt, secondAt⟩ :=
                ih skipped
              exact ⟨
                left + 1,
                right + 1,
                before,
                after,
                by omega,
                atLeft,
                atRight,
                firstAt,
                secondAt
              ⟩
          | cons_cons _ remaining =>
              have member := remaining.subset List.mem_cons_self
              obtain ⟨after, afterMember, secondAt⟩ := List.mem_filterMap.mp member
              obtain ⟨right, atRight⟩ := List.mem_iff_getElem?.mp afterMember
              exact ⟨
                0,
                right + 1,
                head,
                after,
                by omega,
                rfl,
                atRight,
                selected,
                secondAt
              ⟩

/-- An item annotation denotes a value event and retains its exact occurrence.
Witness: only the stream-value constructor can return a present item annotation. -/
theorem itemAnnotation_some {entry : PublicationAnnotation} {occurrence : Occurrence}
    (selected : itemAnnotation entry = some occurrence)
    : entry.1 = some occurrence ∧ IsValue entry.2 := by
  obtain ⟨source, event⟩ := entry
  cases source with
  | none => cases selected
  | some source =>
      cases event <;> simp_all [itemAnnotation, IsValue]

/-- A matched item occurrence cannot annotate an object-value event.
Witness: structural task descriptors separate item payloads from object payloads.
-/
theorem PublicationAt.itemAnnotation {work address ordinal event}
    (source : PublicationAt work (.item address ordinal) event)
    : itemAnnotation (some (.item address ordinal), event)
      = some (.item address ordinal) := by
  cases event with
  | groupValues node values =>
      cases values with
      | nil => cases source
      | cons value rest =>
          cases rest with
          | nil =>
              obtain ⟨owners, producer, known⟩ := source
              simp [TaskAt] at known
          | cons next more => cases source
  | streamValues => rfl
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases source

/-- Every lower ordinal has an earlier value position under the same joint matching.
Witness: the source's ordered item pair, exact item annotation order, and uniqueness of
present annotations identify the pair's second position with the current output index.
-/
theorem annotationMatching_earlier_item {work : Execution.Work} {inputs : List GraphEvent}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs)
    {annotated : List PublicationAnnotation}
    (unique : (annotated.filterMap Prod.fst).Nodup)
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry)
    (itemOrder
      : annotated.filterMap itemAnnotation
        = (inputs.flatMap GraphEvent.itemPublications).map Prod.fst)
    {index event address first second}
    (atEvent : (annotated.map Prod.snd)[index]? = some event) (value : IsValue event)
    (same : annotationMatching annotated index = .item address second)
    (less : first < second)
    : ∃ earlier prior,
        earlier < index
        ∧ (annotated.map Prod.snd)[earlier]? = some prior
        ∧ IsValue prior
        ∧ annotationMatching annotated earlier = .item address first := by
  obtain ⟨current, source⟩ := annotationMatching_publication known atEvent value
  rw [same] at current source
  have currentItem : .item address second ∈ annotated.filterMap itemAnnotation :=
    List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? current, source.itemAnnotation⟩
  have ordered := valid.earlier_item_sublist generated less (itemOrder ▸ currentItem)
  rw [← itemOrder] at ordered
  obtain ⟨left, right, ⟨beforeSource, before⟩, ⟨afterSource, after⟩,
    earlier, atLeft, atRight, firstAt, secondAt⟩ :=
    pair_filterMap_positions itemAnnotation ordered
  obtain ⟨firstSource, firstValue⟩ := itemAnnotation_some firstAt
  obtain ⟨secondSource, _⟩ := itemAnnotation_some secondAt
  dsimp only at firstSource secondSource firstValue
  rw [firstSource] at atLeft
  rw [secondSource] at atRight
  have rightIsCurrent := annotation_occurrence_unique unique atRight current
  subst right
  refine ⟨left, before, earlier, ?_, firstValue, ?_⟩
  · simp only [List.getElem?_map, atLeft, Option.map_some]
  · simp only [annotationMatching, atLeft]

/-- Every lower ordinal is already published in the current value event's strict prefix.
Witness: the earlier annotated position is retained by `take`, with the same matching.
-/
theorem annotationMatching_published_earlier_item {work : Execution.Work}
    {inputs : List GraphEvent} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs) {annotated : List PublicationAnnotation}
    (unique : (annotated.filterMap Prod.fst).Nodup)
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry)
    (itemOrder
      : annotated.filterMap itemAnnotation
        = (inputs.flatMap GraphEvent.itemPublications).map Prod.fst)
    {index event address first second}
    (atEvent : (annotated.map Prod.snd)[index]? = some event) (value : IsValue event)
    (same : annotationMatching annotated index = .item address second)
    (less : first < second)
    : Published (annotationMatching annotated) ((annotated.map Prod.snd).take index)
        (.item address first) := by
  obtain ⟨earlier, prior, earlierIndex, priorAt, priorValue, priorSource⟩ :=
    annotationMatching_earlier_item generated valid unique known itemOrder atEvent value same less
  exact ⟨earlier, prior, (List.getElem?_take_of_lt earlierIndex).trans priorAt,
    priorValue, priorSource⟩

-----------------------------------------------------------------------------------------
-- Actual replay discharges freshness and stream-predecessor publication together
-----------------------------------------------------------------------------------------

/-- One actual-output matching has exact fresh payloads and every earlier stream item.
Witness: the generated source's ordered item prefixes transported through the existing
joint annotation, retaining original output batching. Producer support, cancellation,
owners, and notices are not assumed or proved by this result. -/
theorem createWorkQueue_runNormalized_orderedMatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      ∃ matching : PublicationMatching,
        WorkBatching (outputs.flatten.flatMap publicationAtoms) outputs
        ∧ ∀ index event,
            (outputs.flatten.flatMap publicationAtoms)[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching
                  ((outputs.flatten.flatMap publicationAtoms).take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching
                      ((outputs.flatten.flatMap publicationAtoms).take index)
                      (.item address first) := by
  obtain ⟨annotated, same, unique, itemOrder, known⟩ :=
    createWorkQueue_runNormalized_annotations valid started
  refine ⟨annotationMatching annotated,
    createWorkQueue_runNormalized_atomicBatching valid, ?_⟩
  intro index event atEvent value
  rw [← same] at atEvent ⊢
  obtain ⟨source, fresh⟩ := annotationMatching_fresh unique known atEvent value
  refine ⟨source, fresh, ?_⟩
  intro address first second occurrence less
  exact annotationMatching_published_earlier_item generated valid unique known itemOrder
    atEvent value occurrence less

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
