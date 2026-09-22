import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamReleaseAtoms
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemAnnotationOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedClosureLedger
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ObjectLedgerMatching

/-! One joint matching publishes every announced stream's producer by its notice carrier. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An item-carried stream's producer is published in the annotation's inclusive prefix.
Witness: exact item-label order converts the release inventory prefix to a retained item
annotation, which is a publication under the same full-history matching.
-/
theorem annotationMatching_itemStreamRelease {work : Execution.Work}
    {annotated : List PublicationAnnotation} {published : List ItemPublication}
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry)
    (itemOrder : annotated.filterMap itemAnnotation = published.map Prod.fst)
    (supported
      : NormalizedItemStreamReleasePublications work published (annotated.map Prod.snd))
    {index owner values groups streams child}
    (atEvent
      : (annotated.map Prod.snd)[index]?
        = some (.streamValues owner values groups streams))
    (noticed : child ∈ streams)
    : ∃ occurrence,
        NodeAt work child .stream [] (some occurrence)
        ∧ Published (annotationMatching annotated)
            ((annotated.map Prod.snd).take (index + 1)) occurrence := by
  obtain ⟨occurrence, located, source⟩ :=
    supported index owner values groups streams atEvent child noticed
  refine ⟨occurrence, located, annotationMatching_published_item ?_⟩
  rw [itemAnnotation_prefix known, itemOrder, ← List.map_take]
  exact source

/-- Extending a cutoff preserves publication under an unchanged full-history matching.
Witness: the original value index stays below the larger cutoff and retains the same lookup.
-/
theorem published_take_mono {events : List Execution.WorkQueueEvent}
    {matching occurrence first last}
    (published : Published matching (events.take first) occurrence) (bound : first ≤ last)
    : Published matching (events.take last) occurrence := by
  obtain ⟨index, event, atEvent, value, same⟩ := published
  have smaller : index < first := by
    have size := (List.getElem?_eq_some_iff.mp atEvent).choose
    simp only [List.length_take] at size
    omega
  refine ⟨index, event, ?_, value, same⟩
  rw [List.getElem?_take_of_lt (by omega : index < last)]
  exact (List.getElem?_take_of_lt smaller).symm.trans atEvent

-----------------------------------------------------------------------------------------
-- Object and item release share the matching used for value freshness and item ordering
-----------------------------------------------------------------------------------------

/-- One actual-output matching publishes every announced stream's producer by its carrier.
Witness: use the object-release inventory in the joint annotation, retain its exact object
and source-item orders, and transport both release arguments through atomization. A group
carrier's producer is strictly earlier; an item carrier may publish its own producer.
This proves publication support, not cancellation safety, dependency satisfaction, notice
freshness/openness, owner eligibility, terminal accounting, or full admission.
Every source-item and object inventory prefix is published once the output contains that
many corresponding values, retaining occurrence labels even when values coincide. The
same object ledger retains every batch/handler's buffered and prepared closure coverage.
-/
theorem createWorkQueue_runNormalized_streamProducerMatching_withClosureLedger
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ published : List ObjectPublication,
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index event,
            atoms[index]? = some event
            → StreamNoticesSatisfy
                (fun child =>
                  ∃ dependencies occurrence,
                    NodeAt work child .stream dependencies (some occurrence)
                    ∧ Published matching (atoms.take (index + 1)) occurrence) event)
        ∧ (∀ occurrence ∈
            (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
            Published matching atoms occurrence)
        ∧ (∀ index occurrence,
            occurrence
              ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                  ((atoms.take index).flatMap normalizedItemValues).length
            → Published matching (atoms.take index) occurrence)
        ∧ (State.initialize (Work.fromExecution work)).BatchClosuresCovered batches
            published
        ∧ (∀ index occurrence,
            occurrence
              ∈ (published.map Prod.fst).take
                  ((atoms.take index).flatMap normalizedObjectValues).length
            → Published matching (atoms.take index) occurrence)
        ∧ ObjectLedgerMatching work batches atoms matching published := by
  obtain ⟨published, values, inventory, closureCoverage, objectSupport, rawValues⟩ :=
    generated.runNormalized_bufferedCoverage batches valid started
  obtain ⟨annotated, same, unique, itemOrder, objectOrder, known⟩ :=
    createWorkQueue_runNormalized_annotations_of_inventory valid started published
      inventory.unique values inventory.provenance
  have itemSupport :=
    (createWorkQueue_runNormalized_itemStreamReleasePublications valid started).publicationAtoms
  have objectAtoms := objectSupport.publicationAtoms
  rw [← same] at itemSupport objectAtoms
  refine ⟨
    published,
    annotationMatching annotated,
    createWorkQueue_runNormalized_atomicBatching valid,
    ?_,
    ?_,
    ?_,
    ?_,
    closureCoverage,
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
  · intro index event atEvent
    have metadata := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid event
      (List.mem_of_getElem? atEvent)
    rw [← same] at atEvent ⊢
    cases event with
    | groupSuccess group groups streams =>
        intro child noticed
        obtain ⟨dependencies, producer, located⟩ := metadata child noticed
        obtain ⟨occurrence, source, earlier⟩ :=
          annotationMatching_streamRelease known objectOrder objectAtoms atEvent noticed located
        exact ⟨
          dependencies,
          occurrence,
          source ▸ located,
          published_take_mono earlier (by omega)
        ⟩
    | streamValues stream items groups streams =>
        intro child noticed
        obtain ⟨occurrence, located, throughCarrier⟩ :=
          annotationMatching_itemStreamRelease known itemOrder itemSupport atEvent noticed
        exact ⟨[], occurrence, located, throughCarrier⟩
    | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
        trivial
  · intro occurrence member
    have retained : occurrence ∈ annotated.filterMap itemAnnotation := itemOrder ▸ member
    have published := annotationMatching_published_item (annotated := annotated)
      (occurrence := occurrence) (index := annotated.length) (by simpa using retained)
    rw [← List.map_take, List.take_length, same] at published
    exact published
  · intro index occurrence member
    rw [← same] at member ⊢
    apply annotationMatching_published_item
    rw [itemAnnotation_prefix known, itemOrder]
    exact member
  · intro index occurrence member
    rw [← same] at member ⊢
    apply annotationMatching_published_object
    rw [objectAnnotation_prefix known, objectOrder]
    exact member
  · refine ⟨?_, ?_, ?_⟩
    · exact rawValues.trans ((State.initialize (Work.fromExecution work)).batchedObjectValues_flattened
        batches (by rwa [← inputsStarted_eq_batchesStarted]))
    · intro publication member
      obtain ⟨result, supplied, valueEq⟩ := inventory.provenance publication member
      exact ⟨result, supplied, valueEq, valid.event_matches supplied⟩
    · intro index group payload selected
      rw [← same] at selected ⊢
      rw [← objectOrder]
      exact annotationMatching_object_at known selected

/-- The item-prefix interface projects the matching with the stronger closure ledger.
Witness: discard only its proof-side object ledger and object-prefix certificate; batching,
fresh values, item order, stream notices, and item-prefix coverage retain the same matching.
-/
theorem createWorkQueue_runNormalized_streamProducerMatching_withItemPrefixes
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index event,
            atoms[index]? = some event
            → StreamNoticesSatisfy
                (fun child =>
                  ∃ dependencies occurrence,
                    NodeAt work child .stream dependencies (some occurrence)
                    ∧ Published matching (atoms.take (index + 1)) occurrence) event)
        ∧ (∀ occurrence ∈
            (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
            Published matching atoms occurrence)
        ∧ (∀ index occurrence,
            occurrence
              ∈ ((batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst).take
                  ((atoms.take index).flatMap normalizedItemValues).length
            → Published matching (atoms.take index) occurrence) := by
  obtain ⟨_, matching, batching, values, notices, items, itemPrefixes, _, _⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withClosureLedger generated valid started
  exact ⟨matching, batching, values, notices, items, itemPrefixes⟩

/-- The existing full-item-coverage interface projects the stronger prefix matching.
Witness: retain the same actual matching, batching, values, and notice support; discard
only the additional prefix certificate. No source occurrences are reconstructed by value.
-/
theorem createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage
    {work : Execution.Work} {batches : List (List GraphEvent)}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index event,
            atoms[index]? = some event
            → StreamNoticesSatisfy
                (fun child =>
                  ∃ dependencies occurrence,
                    NodeAt work child .stream dependencies (some occurrence)
                    ∧ Published matching (atoms.take (index + 1)) occurrence) event)
        ∧ (∀ occurrence ∈
            (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst,
            Published matching atoms occurrence) := by
  obtain ⟨matching, batching, values, notices, covered, _⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemPrefixes generated valid started
  exact ⟨matching, batching, values, notices, covered⟩

/-- The producer-support interface retains its original conclusion.
Witness: project the stronger joint matching that also retains every source item.
-/
theorem createWorkQueue_runNormalized_streamProducerMatching {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ (∀ index event,
            atoms[index]? = some event
            → StreamNoticesSatisfy
                (fun child =>
                  ∃ dependencies occurrence,
                    NodeAt work child .stream dependencies (some occurrence)
                    ∧ Published matching (atoms.take (index + 1)) occurrence) event) := by
  obtain ⟨matching, batching, values, support, _⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  exact ⟨matching, batching, values, support⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
