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
    : (streamPublicationAtoms stream groups streams values).flatMap streamNoticeKeys
      = streams.map Execution.DeliveryNode.key := by
  induction values using streamPublicationAtoms.induct with
  | case1 => exact False.elim (nonempty rfl)
  | case2 => simp [streamPublicationAtoms, streamNoticeKeys]
  | case3 value next rest ih =>
      simpa [streamPublicationAtoms, streamNoticeKeys] using ih (by simp)

/-- Atomizing an event with nonempty values retains its complete stream-notice projection.
Witness: object atoms have no notices, stream notices stay last, and control events stay put.
-/
theorem publicationAtoms_streamNotices (event : Execution.WorkQueueEvent)
    (nonempty : NonemptyValues event)
    : (publicationAtoms event).flatMap streamNoticeKeys = streamNoticeKeys event := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, List.flatMap_map, streamNoticeKeys]
  | streamValues stream values groups streams =>
      exact streamPublicationAtoms_streamNotices _ _ _ _ nonempty
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms]

/-- Every atom references only a stream referenced by its original event.
Witness: splitting items repeats their unchanged stream key; no other split adds a reference.
-/
theorem publicationAtoms_streamReferences (event : Execution.WorkQueueEvent)
    : ((publicationAtoms event).flatMap streamReferenceKeys).Subset
        (streamReferenceKeys event) := by
  cases event with
  | groupValues group values =>
      simp [publicationAtoms, List.flatMap_map, streamReferenceKeys, List.Subset]
  | streamValues stream values groups streams =>
      induction values using streamPublicationAtoms.induct with
      | case1 => simp [publicationAtoms, streamPublicationAtoms, List.Subset]
      | case2 => intro key member; exact member
      | case3 value next rest ih =>
          simpa [publicationAtoms, streamPublicationAtoms, streamReferenceKeys,
            List.Subset]
            using ih
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      intro key member; exact member

/-- Atomic expansion retains strictly prior notice support for every stream reference.
Witness: each atom uses only its source event's already-known keys; nonempty value lists
retain every source notice before the next source event is expanded.
-/
theorem ReferencesAnnounced.publicationAtoms {initial events}
    (announced : ReferencesAnnounced streamNoticeKeys streamReferenceKeys initial events)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : ReferencesAnnounced streamNoticeKeys streamReferenceKeys initial
        (events.flatMap publicationAtoms) := by
  induction events generalizing initial with
  | nil => trivial
  | cons event rest ih =>
      rw [List.flatMap_cons]
      apply ReferencesAnnounced.append
      · apply ReferencesAnnounced.of_references
        intro key member
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
    : ReferencesAnnounced streamNoticeKeys streamReferenceKeys
        ((State.initialize (Work.fromExecution work)).initialStreams.map
          Execution.DeliveryNode.key)
        (((State.initialize (Work.fromExecution work)).runNormalized
            batches).2.flatten.flatMap
          publicationAtoms) := by
  exact (createWorkQueue_runNormalized_streamReferencesAnnounced (Work.fromExecution work)
    batches).publicationAtoms (createWorkQueue_runNormalized_nonemptyValues valid).2

/-- Stream-only notice accounting implies the contract's broader announced-key condition.
Witness: a stream notice is one of the pending keys; initial stream keys are also initial
queue keys. This does not infer that a previously announced key is still open.
-/
theorem ReferencesAnnounced.announcedKeys
    {groups streams : List Execution.DeliveryNode} {events}
    (announced
      : ReferencesAnnounced streamNoticeKeys streamReferenceKeys
          (streams.map Execution.DeliveryNode.key) events)
    {index event} (atEvent : events[index]? = some event)
    {key} (reference : key ∈ streamReferenceKeys event)
    : key
      ∈ announcedKeys ((groups ++ streams).map Execution.DeliveryNode.key)
          (events.take index) := by
  have known := announced.atEvent atEvent reference
  rcases List.mem_append.mp known with initial | prior
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_right _ initial
  · apply List.mem_append_right
    obtain ⟨carrier, member, noticed⟩ := List.mem_flatMap.mp prior
    apply List.mem_flatMap.mpr ⟨carrier, member, ?_⟩
    cases carrier <;> simp_all [streamNoticeKeys, eventPending, List.map_append]

/-- A stream reference in actual atomic replay satisfies the contract's announcement clause.
Witness: the ordered stream-only invariant embeds into all initial and pending queue keys.
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
    {key} (reference : key ∈ streamReferenceKeys event)
    : let queue := State.initialize (Work.fromExecution work)
      key
      ∈ announcedKeys
          ((queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key)
          ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms
            |>.take index) := by
  exact (createWorkQueue_runNormalized_atomicStreamReferences valid).announcedKeys
    atEvent reference

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
