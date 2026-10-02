import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.OutputShape

/-! One source-occurrence matching covers mixed object/item output atoms. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Attach exact source descriptors to an already emitted atomic history
-----------------------------------------------------------------------------------------

/-- The occurrence has exactly the successful payload of this singleton value event.
Owner admissibility, producer readiness, notices, and cancellation are separate obligations.
-/
def PublicationAt (work : Execution.Work) (occurrence : Occurrence)
    : Execution.WorkQueueEvent → Prop
  | .groupValues _ [value] =>
      ∃ owners producer,
        TaskAt work occurrence owners producer
          (.object value.path (.ok (value.data, value.errors)))
  | .streamValues stream [value] _ _ =>
      ∃ owners producer,
        TaskAt work occurrence owners producer
          (.item stream (.ok (value.item, value.errors)))
  | _ => False

/-- Proof-only event annotation; control events have no source occurrence. -/
abbrev PublicationAnnotation := Option Occurrence × Execution.WorkQueueEvent

/-- Recover item source occurrences in output order, omitting objects and control events.
-/
def itemAnnotation : PublicationAnnotation → Option Occurrence
  | (some occurrence, .streamValues ..) => some occurrence
  | _ => none

/-- Recover object source occurrences in output order, omitting items and control events.
-/
def objectAnnotation : PublicationAnnotation → Option Occurrence
  | (some occurrence, .groupValues ..) => some occurrence
  | _ => none

/-- A present annotation identifies the exact payload; an absent one marks control output.
-/
def AnnotationMatches (work : Execution.Work) (entry : PublicationAnnotation) : Prop :=
  match entry.1 with
  | some occurrence => PublicationAt work occurrence entry.2
  | none => ¬IsValue entry.2

/-- A source paired with an object payload has its exact successful task descriptor. -/
def ObjectSource (work : Execution.Work)
    (entry : Occurrence × Execution.ExecutionGroupValue)
    : Prop :=
  ∃ owners producer,
    TaskAt work entry.1 owners producer
      (.object entry.2.path (.ok (entry.2.data, entry.2.errors)))

/-- A source paired with an item retains the exact stream and successful item descriptor. -/
def ItemSource (work : Execution.Work) (entry : ItemPublication) : Prop :=
  ∃ owners producer,
    TaskAt work entry.1 owners producer
      (.item entry.2.1 (.ok (entry.2.2.item, entry.2.2.errors)))

/-- Ordered object/item inventories can be interleaved along the actual atomic outputs.
Witness: consume the corresponding inventory head at a value event, retain control
events unannotated, and permute only the proof inventory, never the emitted events.
-/
theorem interleavePublicationSources_ordered (work : Execution.Work)
    (events : List Execution.WorkQueueEvent)
    (objects : List (Occurrence × Execution.ExecutionGroupValue))
    (items : List ItemPublication) (atomic : ∀ event ∈ events, AtomicValues event)
    (objectValues : objects.map Prod.snd = events.flatMap normalizedObjectValues)
    (itemValues : items.map Prod.snd = events.flatMap normalizedItemValues)
    (objectSources : ∀ entry ∈ objects, ObjectSource work entry)
    (itemSources : ∀ entry ∈ items, ItemSource work entry)
    : ∃ annotated : List PublicationAnnotation,
        annotated.map Prod.snd = events
        ∧ (annotated.filterMap Prod.fst).Perm (objects.map Prod.fst ++ items.map Prod.fst)
        ∧ annotated.filterMap itemAnnotation = items.map Prod.fst
        ∧ annotated.filterMap objectAnnotation = objects.map Prod.fst
        ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
  induction events generalizing objects items with
  | nil =>
      have noObjects : objects = [] := by simpa using objectValues
      have noItems : items = [] := by simpa using itemValues
      subst objects items
      exact ⟨[], rfl, .refl [], rfl, rfl, by simp⟩
  | cons event rest ih =>
      have restAtomic := fun next member => atomic next (List.mem_cons_of_mem event member)
      have control (noObjects : normalizedObjectValues event = [])
          (noItems : normalizedItemValues event = []) (notValue : ¬IsValue event)
          : ∃ annotated : List PublicationAnnotation,
            annotated.map Prod.snd = event :: rest
            ∧ (annotated.filterMap Prod.fst).Perm
              (objects.map Prod.fst ++ items.map Prod.fst)
            ∧ annotated.filterMap itemAnnotation = items.map Prod.fst
            ∧ annotated.filterMap objectAnnotation = objects.map Prod.fst
            ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
        obtain ⟨tail, same, permuted, itemOrder, objectOrder, sources⟩ :=
          ih objects items restAtomic
          (by simpa only [List.flatMap_cons, noObjects, List.nil_append] using objectValues)
          (by simpa only [List.flatMap_cons, noItems, List.nil_append] using itemValues)
          objectSources itemSources
        refine ⟨(none, event) :: tail, by simp [same], permuted,
          by simpa only [List.filterMap_cons, itemAnnotation] using itemOrder,
          by simpa only [List.filterMap_cons, objectAnnotation] using objectOrder, ?_⟩
        intro entry member
        rcases List.mem_cons.mp member with sameEntry | earlier
        · subst entry
          exact notValue
        · exact sources entry earlier
      cases event with
      | groupValues group values =>
          obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp (atomic _ List.mem_cons_self)
          cases objects with
          | nil => simp [normalizedObjectValues] at objectValues
          | cons first more =>
              have aligned : first.2 = value
                  ∧ more.map Prod.snd = rest.flatMap normalizedObjectValues := by
                simpa [normalizedObjectValues] using objectValues
              obtain ⟨tail, same, permuted, itemOrder, objectOrder, sources⟩ :=
                ih more items restAtomic aligned.2
                (by simpa [normalizedItemValues] using itemValues)
                (fun next member => objectSources next (List.mem_cons_of_mem _ member)) itemSources
              refine ⟨
                (some first.1, .groupValues group [value]) :: tail,
                by simp [same],
                by simpa using permuted.cons first.1,
                by simpa only [List.filterMap_cons, itemAnnotation] using itemOrder,
                by
                  simpa only [List.filterMap_cons, objectAnnotation, List.map_cons]
                    using congrArg (first.1 :: ·) objectOrder,
                ?_
              ⟩
              intro entry member
              rcases List.mem_cons.mp member with sameEntry | later
              · subst entry
                simpa only [AnnotationMatches, PublicationAt, ObjectSource, ← aligned.1]
                  using objectSources first List.mem_cons_self
              · exact sources entry later
      | streamValues stream values groups streams =>
          obtain ⟨value, rfl⟩ := List.length_eq_one_iff.mp (atomic _ List.mem_cons_self)
          cases items with
          | nil => simp [normalizedItemValues] at itemValues
          | cons first more =>
              have aligned : first.2 = (stream, value)
                  ∧ more.map Prod.snd = rest.flatMap normalizedItemValues := by
                simpa [normalizedItemValues] using itemValues
              obtain ⟨tail, same, permuted, itemOrder, objectOrder, sources⟩ :=
                ih objects more restAtomic
                (by simpa [normalizedObjectValues] using objectValues) aligned.2 objectSources
                (fun next member => itemSources next (List.mem_cons_of_mem _ member))
              refine ⟨
                (some first.1, .streamValues stream [value] groups streams) :: tail,
                by simp [same],
                ?_,
                ?_,
                by simpa only [List.filterMap_cons, objectAnnotation] using objectOrder,
                ?_
              ⟩
              · simpa using (permuted.cons first.1).trans List.perm_middle.symm
              · simpa only [List.filterMap_cons, itemAnnotation, List.map_cons]
                  using congrArg (first.1 :: ·) itemOrder
              · intro entry member
                rcases List.mem_cons.mp member with sameEntry | later
                · subst entry
                  have source := itemSources first List.mem_cons_self
                  simpa only [AnnotationMatches, PublicationAt, ItemSource, aligned.1] using source
                · exact sources entry later
      | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination
        =>
          exact control rfl rfl (by simp [IsValue])

/-- The original interleaving interface remains available with its unchanged conclusion.
Witness: project the stronger witness retaining both object and item occurrence orders.
-/
theorem interleavePublicationSources (work : Execution.Work)
    (events : List Execution.WorkQueueEvent)
    (objects : List (Occurrence × Execution.ExecutionGroupValue))
    (items : List ItemPublication) (atomic : ∀ event ∈ events, AtomicValues event)
    (objectValues : objects.map Prod.snd = events.flatMap normalizedObjectValues)
    (itemValues : items.map Prod.snd = events.flatMap normalizedItemValues)
    (objectSources : ∀ entry ∈ objects, ObjectSource work entry)
    (itemSources : ∀ entry ∈ items, ItemSource work entry)
    : ∃ annotated : List PublicationAnnotation,
        annotated.map Prod.snd = events
        ∧ (annotated.filterMap Prod.fst).Perm (objects.map Prod.fst ++ items.map Prod.fst)
        ∧ annotated.filterMap itemAnnotation = items.map Prod.fst
        ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
  obtain ⟨annotated, same, permuted, itemOrder, _, sources⟩ :=
    interleavePublicationSources_ordered work events objects items atomic
      objectValues itemValues objectSources itemSources
  exact ⟨annotated, same, permuted, itemOrder, sources⟩

-----------------------------------------------------------------------------------------
-- Distinct inventories supply a single occurrence-unique annotation
-----------------------------------------------------------------------------------------

/-- Object and item inventories cannot name the same structural occurrence.
Witness: `TaskAt` separates execution-group addresses from indexed stream occurrences.
-/
theorem objectSource_ne_itemSource {work object item}
    (objectSource : ObjectSource work object) (itemSource : ItemSource work item)
    : object.1 ≠ item.1 := by
  intro same
  obtain ⟨objectOwners, objectProducer, objectKnown⟩ := objectSource
  obtain ⟨itemOwners, itemProducer, itemKnown⟩ := itemSource
  rw [← same] at itemKnown
  cases shape : object.1 <;> simp [TaskAt, shape] at objectKnown itemKnown

/-- Valid input replay admits one exact, occurrence-unique annotation of all output atoms.
Witness: independently proved object/item inventories, their structural disjointness,
and order-preserving interleaving along the actual atomized output.
No `EventAllowed`, notice, failure, or terminal property is assumed. -/
theorem createWorkQueue_runNormalized_annotations {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      ∃ annotated : List PublicationAnnotation,
        annotated.map Prod.snd = outputs.flatten.flatMap publicationAtoms
        ∧ (annotated.filterMap Prod.fst).Nodup
        ∧ annotated.filterMap itemAnnotation
          = (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst
        ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
  obtain ⟨objects, objectsUnique, objectValues, objectSources⟩ :=
    createWorkQueue_runNormalized_objectSources valid
  obtain ⟨itemsUnique, itemValues, itemSources⟩ :=
    createWorkQueue_runNormalized_itemSources valid started
  let objectInventory := objects
  let itemInventory := batches.flatten.flatMap GraphEvent.itemPublications
  let outputs := ((State.initialize (Work.fromExecution work)).runNormalized batches).2
  have objectKnown : ∀ entry ∈ objectInventory, ObjectSource work entry := by
    intro entry member
    obtain ⟨result, _, same, owners, producer, known, _, _⟩ :=
      objectSources entry member
    exact ⟨owners, producer, by simpa only [ObjectSource, same] using known⟩
  have itemKnown : ∀ entry ∈ itemInventory, ItemSource work entry := itemSources
  have unique : (objectInventory.map Prod.fst ++ itemInventory.map Prod.fst).Nodup := by
    refine List.nodup_append.mpr ⟨?_, itemsUnique, ?_⟩
    · exact objectsUnique
    · intro first firstMember second secondMember same
      obtain ⟨object, objectMember, rfl⟩ := List.mem_map.mp firstMember
      obtain ⟨item, itemMember, rfl⟩ := List.mem_map.mp secondMember
      exact objectSource_ne_itemSource (objectKnown object objectMember)
        (itemKnown item itemMember) same
  have atomic : ∀ event ∈ outputs.flatten.flatMap publicationAtoms, AtomicValues event := by
    intro event member
    obtain ⟨original, _, inAtoms⟩ := List.mem_flatMap.mp member
    exact publicationAtoms_atomic original event inAtoms
  have objectProjection : (outputs.flatten.flatMap publicationAtoms).flatMap
      normalizedObjectValues = outputs.flatten.flatMap normalizedObjectValues := by
    simp only [List.flatMap_assoc, (publicationAtoms_values _).1]
  have itemProjection : (outputs.flatten.flatMap publicationAtoms).flatMap
      normalizedItemValues = outputs.flatten.flatMap normalizedItemValues := by
    simp only [List.flatMap_assoc, (publicationAtoms_values _).2]
  obtain ⟨annotated, exactEvents, permuted, itemOrder, known⟩ := interleavePublicationSources work
    (outputs.flatten.flatMap publicationAtoms) objectInventory itemInventory atomic
    (objectValues.trans objectProjection.symm)
    (itemValues.trans itemProjection.symm) objectKnown itemKnown
  exact ⟨annotated, exactEvents, permuted.nodup_iff.mpr unique, itemOrder, known⟩

-----------------------------------------------------------------------------------------
-- Use unbatched event indices, as required by the scheduler contract
-----------------------------------------------------------------------------------------

/-- Read the source occurrence at an output index; control/out-of-range entries are unused.
The arbitrary default is never consulted by a value publication. -/
def annotationMatching (annotated : List PublicationAnnotation) : PublicationMatching :=
  fun index =>
    match annotated[index]? with
    | some (some occurrence, _) => occurrence
    | _ => .executionGroup []

/-- A value event's source annotation is present and yields its exact task descriptor.
Witness: indexed lookup in the event-preserving annotation list; an absent annotation
would classify this output as control instead. -/
theorem annotationMatching_publication {work : Execution.Work}
    {annotated : List PublicationAnnotation}
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry)
    {index event} (atEvent : (annotated.map Prod.snd)[index]? = some event)
    (value : IsValue event)
    : annotated[index]? = some (some (annotationMatching annotated index), event)
      ∧ PublicationAt work (annotationMatching annotated index) event := by
  rw [List.getElem?_map] at atEvent
  cases found : annotated[index]? with
  | none => simp [found] at atEvent
  | some entry =>
      have same : entry.2 = event := by
        simpa only [found, Option.map_some, Option.some.injEq] using atEvent
      have source := known entry (List.mem_of_getElem? found)
      obtain ⟨occurrence, emitted⟩ := entry
      dsimp only at same
      subst emitted
      cases occurrence with
      | none => exact False.elim (source value)
      | some occurrence =>
          simpa only [annotationMatching, found, AnnotationMatches] using And.intro found source

/-- Distinct annotated positions cannot share a present source occurrence.
Witness: duplicate-free filtered annotations imply pairwise separation of all present
occurrences, even with any number of unannotated control events between them. -/
theorem annotation_occurrence_unique {annotated : List PublicationAnnotation}
    (unique : (annotated.filterMap Prod.fst).Nodup)
    {left right : Nat} {occurrence : Occurrence} {first second : Execution.WorkQueueEvent}
    (atLeft : annotated[left]? = some (some occurrence, first))
    (atRight : annotated[right]? = some (some occurrence, second))
    : left = right := by
  have separated : annotated.Pairwise
      (fun first second =>
        ∀ occurrence, first.1 = some occurrence → second.1 ≠ some occurrence) := by
    clear atLeft atRight
    induction annotated with
    | nil => exact .nil
    | cons entry rest ih =>
        have tailUnique : (rest.filterMap Prod.fst).Nodup := by
          cases source : entry.1 with
          | none => simpa only [List.filterMap_cons, source] using unique
          | some occurrence =>
              exact (List.nodup_cons.mp
                      (by simpa only [List.filterMap_cons, source] using unique)).2
        refine .cons ?_ (ih tailUnique)
        intro next member occurrence first same
        have fresh : occurrence ∉ rest.filterMap Prod.fst :=
          (List.nodup_cons.mp (by simpa only [List.filterMap_cons, first] using unique)).1
        exact fresh (List.mem_filterMap.mpr ⟨next, member, same⟩)
  have earlier {i j : Nat} {a b : Execution.WorkQueueEvent}
      (atI : annotated[i]? = some (some occurrence, a))
      (atJ : annotated[j]? = some (some occurrence, b)) (less : i < j) : False := by
    obtain ⟨boundI, exactI⟩ := List.getElem?_eq_some_iff.mp atI
    obtain ⟨boundJ, exactJ⟩ := List.getElem?_eq_some_iff.mp atJ
    have different := List.pairwise_iff_getElem.mp separated i j boundI boundJ less
    rw [exactI, exactJ] at different
    exact different occurrence rfl rfl
  by_cases less : left < right
  · exact False.elim (earlier atLeft atRight less)
  · by_cases greater : right < left
    · exact False.elim (earlier atRight atLeft greater)
    · omega

/-- The constructed matching names a fresh, exact source task at every value position.
Witness: annotation lookup and occurrence uniqueness exclude any earlier publication.
This is the provenance/freshness part of `EventAllowed`, not its other admission clauses.
-/
theorem annotationMatching_fresh {work : Execution.Work}
    {annotated : List PublicationAnnotation}
    (unique : (annotated.filterMap Prod.fst).Nodup)
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry)
    {index event} (atEvent : (annotated.map Prod.snd)[index]? = some event)
    (value : IsValue event)
    : PublicationAt work (annotationMatching annotated index) event
      ∧ ¬Published (annotationMatching annotated) ((annotated.map Prod.snd).take index)
          (annotationMatching annotated index) := by
  obtain ⟨current, source⟩ := annotationMatching_publication known atEvent value
  refine ⟨source, ?_⟩
  rintro ⟨earlier, prior, atPrior, priorValue, same⟩
  have less : earlier < index := by
    have bound := (List.getElem?_eq_some_iff.mp atPrior).choose
    simp only [List.length_take] at bound
    omega
  have priorAt : (annotated.map Prod.snd)[earlier]? = some prior :=
    (List.getElem?_take_of_lt less).symm.trans atPrior
  have previous := (annotationMatching_publication known priorAt priorValue).1
  rw [same] at previous
  have equal := annotation_occurrence_unique unique previous current
  omega

/-- Actual normalized output has a single exact, fresh publication matching and retains
its original batching. Witness: derived output shape, object/item inventory interleaving,
and occurrence-unique annotation lookup. This is not yet an `Explains` witness. -/
theorem createWorkQueue_runNormalized_publicationMatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
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
                  ((outputs.flatten.flatMap publicationAtoms).take index)
                  (matching index) := by
  obtain ⟨annotated, same, unique, _, known⟩ :=
    createWorkQueue_runNormalized_annotations valid started
  refine ⟨annotationMatching annotated,
    createWorkQueue_runNormalized_atomicBatching valid, ?_⟩
  intro index event atEvent value
  rw [← same] at atEvent ⊢
  exact annotationMatching_fresh unique known atEvent value

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
