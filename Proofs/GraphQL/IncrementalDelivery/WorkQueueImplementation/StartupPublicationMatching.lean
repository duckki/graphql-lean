import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupPublicationLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemPublications
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseMatching
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupStreamNoticeMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupItemStreamRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectLedgerMatching

/-! Startup replay has one exact occurrence matching and the same source-handler ledger. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Interleave the supplied object ledger and exact source-item ledger on actual startup output.
Both source orders and all occurrence identities are retained, even for equal payloads.
-/
theorem State.startup_runNormalized_annotations_of_inventory {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    (objects : List ObjectPublication) (objectsUnique : (objects.map Prod.fst).Nodup)
    (objectValues
      : let initial := State.initialize (Work.fromExecution work) startup
        objects.map Prod.snd
        = (initial.runNormalized batches).2.flatten.flatMap normalizedObjectValues)
    (objectSources : ∀ entry ∈ objects, ObjectValueFrom batches.flatten entry.1 entry.2)
    : let initial := State.initialize (Work.fromExecution work) startup
      let atoms := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ annotated : List PublicationAnnotation,
        annotated.map Prod.snd = atoms
        ∧ (annotated.filterMap Prod.fst).Nodup
        ∧ annotated.filterMap itemAnnotation
          = (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst
        ∧ annotated.filterMap objectAnnotation = objects.map Prod.fst
        ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
  obtain ⟨itemsUnique, itemValues, itemSources⟩ :=
    State.startup_runNormalized_itemSources startup valid started
  let initial := State.initialize (Work.fromExecution work) startup
  let outputs := (initial.runNormalized batches).2
  let items := batches.flatten.flatMap GraphEvent.itemPublications
  have objectKnown : ∀ entry ∈ objects, ObjectSource work entry := by
    intro entry member
    obtain ⟨result, supplied, same⟩ := objectSources entry member
    obtain ⟨owners, producer, known, _, _⟩ := valid.event_matches supplied
    exact ⟨owners, producer, by simpa only [same] using known⟩
  have unique : (objects.map Prod.fst ++ items.map Prod.fst).Nodup := by
    refine List.nodup_append.mpr ⟨objectsUnique, itemsUnique, ?_⟩
    intro first firstMember second secondMember same
    obtain ⟨object, objectMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨item, itemMember, rfl⟩ := List.mem_map.mp secondMember
    exact objectSource_ne_itemSource (objectKnown object objectMember)
      (itemSources item itemMember) same
  have atomic : ∀ event ∈ outputs.flatten.flatMap publicationAtoms, AtomicValues event := by
    intro event member
    obtain ⟨original, _, inAtoms⟩ := List.mem_flatMap.mp member
    exact publicationAtoms_atomic original event inAtoms
  have objectProjection : (outputs.flatten.flatMap publicationAtoms).flatMap normalizedObjectValues
      = outputs.flatten.flatMap normalizedObjectValues := by
    simp only [List.flatMap_assoc, (publicationAtoms_values _).1]
  have itemProjection : (outputs.flatten.flatMap publicationAtoms).flatMap normalizedItemValues
      = outputs.flatten.flatMap normalizedItemValues := by
    simp only [List.flatMap_assoc, (publicationAtoms_values _).2]
  obtain ⟨annotated, exactEvents, permuted, itemOrder, objectOrder, known⟩ :=
    interleavePublicationSources_ordered work (outputs.flatten.flatMap publicationAtoms)
      objects items atomic (objectValues.trans objectProjection.symm)
      (itemValues.trans itemProjection.symm) objectKnown itemSources
  exact ⟨
    annotated,
    exactEvents,
    permuted.nodup_iff.mpr unique,
    itemOrder,
    objectOrder,
    known
  ⟩

/-- Every actual startup publication has its exact fixed payload and a fresh occurrence.
The same matching retains earlier-item order and the common buffered/prepared closure
ledger. This establishes publication provenance, not full owner/notice admission.
-/
theorem ExecutedWork.startup_runNormalized_matchingWithLedger {work : Execution.Work}
    (generated : ExecutedWork work) (startup : InitialStartup)
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true)
    : let initial := State.initialize (Work.fromExecution work) startup
      let events := (initial.runNormalized batches).2.flatten.flatMap publicationAtoms
      ∃ published : List ObjectPublication,
      ∃ matching : PublicationMatching,
        initial.BatchClosuresCovered batches published
        ∧ NormalizedStreamReleasePublications work published
            (initial.runNormalized batches).2.flatten
        ∧ published.map Prod.snd = initial.batchedObjectValues batches
        ∧ (∀ index event,
            events[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (events.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (events.take index) (.item address first))
        ∧ (∀ index occurrence,
            occurrence
              ∈ (published.map Prod.fst).take
                  ((events.take index).flatMap normalizedObjectValues).length
            → Published matching (events.take index) occurrence)
        ∧ (∀ index occurrence,
            occurrence
              ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                  ((events.take index).flatMap normalizedItemValues).length
            → Published matching (events.take index) occurrence)
        ∧ (∀ occurrence ∈
            (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
            Published matching events occurrence)
        ∧ (∀ index group groups streams,
            events[index]? = some (.groupSuccess group groups streams)
            → ∀ child ∈ streams,
                ∃ dependencies occurrence,
                  NodeAt work child .stream dependencies (some occurrence)
                  ∧ Published matching (events.take index) occurrence)
        ∧ (∀ index owner values groups streams,
            events[index]? = some (.streamValues owner values groups streams)
            → ∀ child ∈ streams,
                ∃ occurrence,
                  NodeAt work child .stream [] (some occurrence)
                  ∧ Published matching (events.take (index + 1)) occurrence)
        ∧ ObjectLedgerMatching work batches events matching published initial := by
  obtain ⟨published, values, inventory, coverage, streams, raw⟩ :=
    generated.startup_runNormalized_bufferedCoverage startup batches valid started
  obtain ⟨annotated, same, unique, itemOrder, objectOrder, known⟩ :=
    State.startup_runNormalized_annotations_of_inventory startup valid started published
      inventory.unique values inventory.provenance
  refine ⟨
    published,
    annotationMatching annotated,
    coverage,
    streams,
    raw,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_,
    ?_
  ⟩
  · intro index event atEvent value
    rw [← same] at atEvent ⊢
    obtain ⟨source, fresh⟩ := annotationMatching_fresh unique known atEvent value
    refine ⟨source, fresh, ?_⟩
    intro address first second occurrence less
    exact annotationMatching_published_earlier_item generated valid unique known itemOrder
      atEvent value occurrence less
  · intro index occurrence member
    rw [← same] at member ⊢
    apply annotationMatching_published_object
    rw [objectAnnotation_prefix known, objectOrder]
    exact member
  · intro index occurrence member
    rw [← same] at member ⊢
    apply annotationMatching_published_item
    rw [itemAnnotation_prefix known, itemOrder]
    exact member
  · intro occurrence member
    rw [← same]
    have retained : occurrence ∈
        (annotated.take (annotated.map Prod.snd).length).filterMap itemAnnotation := by
      simpa only [List.length_map, List.take_length, itemOrder] using member
    simpa only [List.take_length] using annotationMatching_published_item retained
  · intro index group groups children selected child noticed
    have metadata := State.startup_runNormalized_atomicStreamNoticesLocated startup valid
      (.groupSuccess group groups children) (List.mem_of_getElem? selected)
    obtain ⟨dependencies, producer, located⟩ := metadata child noticed
    have supported := streams.publicationAtoms
    rw [← same] at selected supported ⊢
    obtain ⟨occurrence, source, published⟩ :=
      annotationMatching_streamRelease known objectOrder supported selected noticed located
    exact ⟨dependencies, occurrence, source ▸ located, published⟩
  · intro index owner items groups children selected child noticed
    have support := (State.startup_runNormalized_itemStreamReleasePublications
      startup valid started).publicationAtoms
    rw [← same] at selected support ⊢
    obtain ⟨occurrence, located, source⟩ := support index owner items groups children
      selected child noticed
    refine ⟨occurrence, located, annotationMatching_published_item ?_⟩
    rw [itemAnnotation_prefix known, itemOrder, ← List.map_take]
    exact source
  · refine ⟨raw.trans (State.batchedObjectValues_rawBatches _ batches), ?_, ?_⟩
    · intro publication member
      obtain ⟨result, supplied, valueEq⟩ := inventory.provenance publication member
      exact ⟨result, supplied, valueEq, valid.event_matches supplied⟩
    · intro index group values selected
      rw [← same] at selected ⊢
      rw [← objectOrder]
      exact annotationMatching_object_at known selected

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
