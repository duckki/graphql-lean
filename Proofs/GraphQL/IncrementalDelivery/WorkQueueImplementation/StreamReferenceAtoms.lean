import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferences

/-! Prior stream notices persist in the atomic history used by scheduler admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Value splitting keeps stream notices and creates no new stream references
-----------------------------------------------------------------------------------------

/-- Splitting nonempty stream values keeps exactly the final atom's stream notices.
Witness: earlier item atoms carry no child notices; the last atom keeps the original list.
-/
theorem streamPublicationAtoms_streamNotices (stream groups streams values)
    (nonempty : values ≠ [])
    : (streamPublicationAtoms stream groups streams values).flatMap streamNoticeRefs
      = streams.map Execution.DeliveryNode.ref := by
  induction values using streamPublicationAtoms.induct with
  | case1 => exact False.elim (nonempty rfl)
  | case2 => simp [streamPublicationAtoms, streamNoticeRefs]
  | case3 value next rest ih =>
      simpa [streamPublicationAtoms, streamNoticeRefs] using ih (by simp)

/-- Atomizing an event with nonempty values retains its complete stream-notice projection.
Witness: object atoms have no notices, stream notices stay last, and control events stay put.
-/
theorem publicationAtoms_streamNotices (event : Execution.WorkQueueEvent)
    (nonempty : NonemptyValues event)
    : (publicationAtoms event).flatMap streamNoticeRefs = streamNoticeRefs event := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, List.flatMap_map, streamNoticeRefs]
  | streamValues stream values groups streams =>
      exact streamPublicationAtoms_streamNotices _ _ _ _ nonempty
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms]

/-- Every atom references only a stream referenced by its original event.
Witness: splitting items repeats their unchanged stream ref; no other split adds a reference.
-/
theorem publicationAtoms_streamReferences (event : Execution.WorkQueueEvent)
    : ((publicationAtoms event).flatMap streamReferenceRefs).Subset
        (streamReferenceRefs event) := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, List.flatMap_map, streamReferenceRefs, List.Subset]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms, List.Subset]
      | case2 => intro ref member; exact member
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, streamReferenceRefs,
            List.Subset]
            using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      intro ref member; exact member

/-- Atomic expansion retains strictly prior notice support for every stream reference.
Witness: each atom uses only its source event's already-known refs; nonempty value lists
retain every source notice before the next source event is expanded.
-/
theorem ReferencesAnnounced.publicationAtoms {initial events}
    (announced : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial events)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ReferencesAnnounced streamNoticeRefs streamReferenceRefs initial
        (events.flatMap publicationAtoms) := by
  induction events generalizing initial with
  | nil => trivial
  | cons event rest ih =>
      rw [List.flatMap_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        intro ref member
        exact announced.1 (publicationAtoms_streamReferences event member)
      · rw [publicationAtoms_streamNotices event (nonempty event List.mem_cons_self)]
        exact ih announced.2 (fun event member => nonempty event (List.mem_cons_of_mem _ member))

-----------------------------------------------------------------------------------------
-- Actual scheduler observations have prior stream notices at every atomic reference
-----------------------------------------------------------------------------------------

/-- Every actual stream value or closure has a prior notice in the same atomic output history.
Witness: raw guard/activation accounting, normalization, and nonempty atomic expansion.
Only valid source payloads are needed to exclude empty item batches; generated-work and
start premises are unnecessary here. This proves announcement, not the full Open predicate.
-/
theorem createWorkQueue_runNormalized_atomicStreamReferences {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    : ReferencesAnnounced streamNoticeRefs streamReferenceRefs
        ((State.initialize (Work.fromExecution work)).initialStreams.map
          Execution.DeliveryNode.ref)
        (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms) := by
  exact (createWorkQueue_runNormalized_streamReferencesAnnounced (Work.fromExecution work)
    batches).publicationAtoms (createWorkQueue_runNormalized_nonemptyValues valid).2

/-- Stream-only notice accounting implies the contract's broader announced-ref condition.
Witness: a stream notice is one of the pending refs; initial stream refs are also initial
queue refs. This does not infer that a previously announced ref is still open.
-/
theorem ReferencesAnnounced.announcedRefs
    {groups streams : List Execution.DeliveryNode} {events}
    (announced
      : ReferencesAnnounced streamNoticeRefs streamReferenceRefs
          (streams.map Execution.DeliveryNode.ref) events)
    {index event} (atEvent : events[index]? = some event)
    {ref} (reference : ref ∈ streamReferenceRefs event)
    : ref
      ∈ announcedRefs ((groups ++ streams).map Execution.DeliveryNode.ref)
          (events.take index) := by
  have known := announced.atEvent atEvent reference
  rcases List.mem_append.mp known with initial | prior
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_right _ initial
  · apply List.mem_append_right
    obtain ⟨carrier, member, noticed⟩ := List.mem_flatMap.mp prior
    apply List.mem_flatMap.mpr ⟨carrier, member, ?_⟩
    cases carrier <;> simp_all [streamNoticeRefs, eventPending, List.map_append]

/-- A stream reference in actual atomic replay satisfies the contract's announcement clause.
Witness: the ordered stream-only invariant embeds into all initial and pending queue refs.
The witness is independent of any publication matching or failure-cut choice.
-/
theorem createWorkQueue_runNormalized_streamAnnouncedAt {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    {index event}
    (atEvent
      : (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms)[index]?
        = some event)
    {ref} (reference : ref ∈ streamReferenceRefs event)
    : let queue := State.initialize (Work.fromExecution work)
      ref
      ∈ announcedRefs
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref)
          ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms
            |>.take index) := by
  exact (createWorkQueue_runNormalized_atomicStreamReferences valid).announcedRefs
    atEvent reference

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
