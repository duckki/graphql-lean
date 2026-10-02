import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedStreamRelease
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationAnnotationOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamPublicationOrder

/-! Stream release uses the same mixed matching as fresh and ordered value publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Atomic expansion keeps stream carriers and their preceding object inventory
-----------------------------------------------------------------------------------------

/-- Splitting stream values cannot create a group-success carrier.
Witness: the recursive expansion emits only stream-value events. -/
private theorem streamPublicationAtoms_noGroupSuccess (stream groups streams values)
    (group newGroups newStreams)
    : Execution.WorkQueueEvent.groupSuccess group newGroups newStreams
      ∉ streamPublicationAtoms stream groups streams values := by
  induction values using streamPublicationAtoms.induct with
  | case1 => simp [streamPublicationAtoms]
  | case2 => simp [streamPublicationAtoms]
  | case3 value next rest ih => simpa [streamPublicationAtoms] using ih

/-- A group-success atom is precisely its unchanged singleton source event.
Witness: value splitting retains only value constructors; each control event keeps its tag.
-/
theorem publicationAtoms_groupSuccess (event : Execution.WorkQueueEvent)
    {index group groups streams}
    (atEvent
      : (publicationAtoms event)[index]? = some (.groupSuccess group groups streams))
    : event = .groupSuccess group groups streams ∧ index = 0 := by
  have member := List.mem_of_getElem? atEvent
  cases event with
  | groupValues owner values =>
      obtain ⟨value, _, impossible⟩ := List.mem_map.mp member
      cases impossible
  | streamValues stream values newGroups newStreams =>
      exact False.elim (streamPublicationAtoms_noGroupSuccess stream newGroups newStreams
        values group groups streams member)
  | groupSuccess owner newGroups newStreams =>
      have same : owner = group ∧ newGroups = groups ∧ newStreams = streams := by
        simpa using (List.mem_singleton.mp member).symm
      obtain ⟨rfl, rfl, rfl⟩ := same
      refine ⟨rfl, ?_⟩
      by_cases zero : index = 0
      · exact zero
      · simp [publicationAtoms, zero] at atEvent
  | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms] at member

/-- A carrier in the atomic history has the same preceding object count as its source.
Witness: locate the source event through flat-map concatenation; each earlier event's
atomic expansion preserves its exact object values, including empty value lists.
-/
theorem publicationAtoms_groupSuccess_prefix (events : List Execution.WorkQueueEvent)
    {index group groups streams}
    (atEvent
      : (events.flatMap publicationAtoms)[index]?
        = some (.groupSuccess group groups streams))
    : ∃ sourceIndex,
        events[sourceIndex]? = some (.groupSuccess group groups streams)
        ∧ (((events.flatMap publicationAtoms).take index).flatMap
            normalizedObjectValues).length
          = ((events.take sourceIndex).flatMap normalizedObjectValues).length := by
  induction events generalizing index with
  | nil => simp at atEvent
  | cons event rest ih =>
      rw [List.flatMap_cons] at atEvent ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans atEvent
        obtain ⟨rfl, rfl⟩ := publicationAtoms_groupSuccess event atHead
        exact ⟨0, rfl, rfl⟩
      · have later : (publicationAtoms event).length ≤ index := by omega
        have atTail := (List.getElem?_append_right later).symm.trans atEvent
        obtain ⟨sourceIndex, sourceEvent, count⟩ := ih atTail
        refine ⟨sourceIndex + 1, sourceEvent, ?_⟩
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
          List.length_append, count, (publicationAtoms_values event).1]
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]

/-- Stream-release support retains its exact object labels through atomic expansion.
Witness: carriers and the number of preceding object payloads are unchanged by splitting.
-/
theorem NormalizedStreamReleasePublications.publicationAtoms {work published events}
    (supported : NormalizedStreamReleasePublications work published events)
    : NormalizedStreamReleasePublications work published
        (events.flatMap publicationAtoms) := by
  intro index group groups streams atEvent stream member dependencies producer known
  obtain ⟨sourceIndex, sourceEvent, count⟩ := publicationAtoms_groupSuccess_prefix events atEvent
  rw [count]
  exact supported sourceIndex group groups streams sourceEvent stream member dependencies
    producer known

-----------------------------------------------------------------------------------------
-- Supply the release inventory to the joint annotation instead of choosing another one
-----------------------------------------------------------------------------------------

/-- An explicitly supplied object inventory can label the actual mixed output atoms.
Witness: pair that inventory with the exact item inventory and interleave both in order;
structural task kinds make their occurrence sets disjoint. This preserves both projected
orders and makes no independent choice of object identities from equal-valued payloads.
-/
theorem createWorkQueue_runNormalized_annotations_of_inventory {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) (objects : List ObjectPublication)
    (objectsUnique : (objects.map Prod.fst).Nodup)
    (objectValues
      : objects.map (fun entry => entry.2)
        = ((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
            normalizedObjectValues)
    (objectSources : ∀ entry ∈ objects, ObjectValueFrom batches.flatten entry.1 entry.2)
    : let outputs :=
        ((State.initialize (Work.fromExecution work)).runNormalized batches).2
      ∃ annotated : List PublicationAnnotation,
        annotated.map Prod.snd = outputs.flatten.flatMap publicationAtoms
        ∧ (annotated.filterMap Prod.fst).Nodup
        ∧ annotated.filterMap itemAnnotation
          = (batches.flatten.flatMap GraphEvent.itemPublications).map Prod.fst
        ∧ annotated.filterMap objectAnnotation = objects.map Prod.fst
        ∧ ∀ entry ∈ annotated, AnnotationMatches work entry := by
  obtain ⟨itemsUnique, itemValues, itemSources⟩ :=
    createWorkQueue_runNormalized_itemSources valid started
  let objectInventory := objects
  let itemInventory := batches.flatten.flatMap GraphEvent.itemPublications
  let outputs := ((State.initialize (Work.fromExecution work)).runNormalized batches).2
  have objectKnown : ∀ entry ∈ objectInventory, ObjectSource work entry := by
    intro entry member
    obtain ⟨result, supplied, same⟩ := objectSources entry member
    obtain ⟨owners, producer, known, _, _⟩ := valid.event_matches supplied
    exact ⟨owners, producer, by simpa only [same] using known⟩
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
  obtain ⟨annotated, exactEvents, permuted, itemOrder, objectOrder, known⟩ :=
    interleavePublicationSources_ordered work (outputs.flatten.flatMap publicationAtoms)
      objectInventory itemInventory atomic
      (objectValues.trans objectProjection.symm)
      (itemValues.trans itemProjection.symm) objectKnown itemKnown
  exact ⟨
    annotated,
    exactEvents,
    permuted.nodup_iff.mpr unique,
    itemOrder,
    objectOrder,
    known
  ⟩

/-- A stream carrier's producer is already published under the joint annotation matching.
Witness: exact object order turns the supported inventory prefix into earlier annotation
membership, which yields an actual value position with that same source occurrence.
-/
theorem annotationMatching_streamRelease {work : Execution.Work}
    {annotated : List PublicationAnnotation} {published : List ObjectPublication}
    (known : ∀ entry ∈ annotated, AnnotationMatches work entry)
    (objectOrder : annotated.filterMap objectAnnotation = published.map Prod.fst)
    (supported
      : NormalizedStreamReleasePublications work published (annotated.map Prod.snd))
    {index group groups streams}
    (atEvent
      : (annotated.map Prod.snd)[index]? = some (.groupSuccess group groups streams))
    {stream dependencies producer} (member : stream ∈ streams)
    (structural : NodeAt work stream .stream dependencies producer)
    : ∃ occurrence,
        producer = some occurrence
        ∧ Published (annotationMatching annotated) ((annotated.map Prod.snd).take index)
            occurrence := by
  obtain ⟨occurrence, source, earlier⟩ :=
    supported index group groups streams atEvent stream member dependencies producer structural
  refine ⟨occurrence, source, annotationMatching_published_object ?_⟩
  rw [objectAnnotation_prefix known index, objectOrder, ← List.map_take]
  exact earlier

-----------------------------------------------------------------------------------------
-- One actual-output matching jointly satisfies all three established publication clauses
-----------------------------------------------------------------------------------------

/-- Actual output has one matching with fresh exact payloads, all earlier stream ordinals,
and earlier producer publication at every task-produced stream notice.
Witness: use the replay's release inventory in the ordered object/item annotation, retain
its strict prefixes through atomic expansion, and reuse the source item-order theorem.
This does not yet prove producer readiness at later stream events, cancellation, notice
licensing, owner admission, termination accounting, or a complete `Explains` witness.
-/
theorem createWorkQueue_runNormalized_streamReleaseMatching {work : Execution.Work}
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
        ∧ (∀ index group groups streams,
            atoms[index]? = some (.groupSuccess group groups streams)
            → ∀ stream ∈ streams,
                ∀ dependencies producer,
                  NodeAt work stream .stream dependencies producer
                  → ∃ occurrence,
                      producer = some occurrence
                      ∧ Published matching (atoms.take index) occurrence) := by
  obtain ⟨published, values, inventory, supported⟩ :=
    createWorkQueue_runNormalized_streamReleasePublications generated valid
  obtain ⟨annotated, same, unique, itemOrder, objectOrder, known⟩ :=
    createWorkQueue_runNormalized_annotations_of_inventory valid started published
      inventory.unique values inventory.provenance
  refine ⟨annotationMatching annotated, createWorkQueue_runNormalized_atomicBatching valid, ?_, ?_⟩
  · intro index event atEvent value
    rw [← same] at atEvent ⊢
    obtain ⟨source, fresh⟩ := annotationMatching_fresh unique known atEvent value
    refine ⟨source, fresh, ?_⟩
    intro address first second occurrence less
    exact annotationMatching_published_earlier_item generated valid unique known itemOrder
      atEvent value occurrence less
  · intro index group groups streams atEvent stream member dependencies producer structural
    rw [← same] at atEvent ⊢
    have atomSupport := supported.publicationAtoms
    rw [← same] at atomSupport
    exact annotationMatching_streamRelease known objectOrder atomSupport atEvent member structural

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
