import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReferenceAtoms

/-! Item-carried stream notices retain their exact strict notice prefix. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Earlier atoms of one item batch carry no stream notices.
Witness: only its final item retains either child list; preceding singleton atoms are empty.
-/
theorem streamPublicationAtoms_before_streamNotices (stream groups streams values)
    {index : Nat} (last : index + 1 = values.length)
    : ((streamPublicationAtoms stream groups streams values).take index).flatMap
        streamNoticeRefs
      = [] := by
  induction values using streamPublicationAtoms.induct generalizing index with
  | case1 => simp at last
  | case2 value =>
      have zero : index = 0 := by simp only [List.length_singleton] at last; omega
      subst index
      rfl
  | case3 value next rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          simp only [streamPublicationAtoms, List.take_succ_cons, List.flatMap_cons,
            streamNoticeRefs, List.map_nil, List.nil_append]
          exact ih (by simp only [List.length_cons] at last ⊢; omega)

/-- A notice-bearing item atom has exactly its source event's strict stream-notice prefix.
Witness: its child notice identifies the last atom; earlier complete expansions retain
their stream notices, while the selected expansion contributes none before that atom.
-/
theorem publicationAtoms_itemNotice_streamPrefix (events : List Execution.WorkQueueEvent)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    {index owner values groups streams child}
    (selected
      : (events.flatMap publicationAtoms)[index]?
        = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ sourceIndex sourceValues,
        events[sourceIndex]? = some (.streamValues owner sourceValues groups streams)
        ∧ ((events.flatMap publicationAtoms).take index).flatMap streamNoticeRefs
          = (events.take sourceIndex).flatMap streamNoticeRefs := by
  induction events generalizing index with
  | nil => simp at selected
  | cons event rest ih =>
      rw [List.flatMap_cons] at selected ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans selected
        obtain ⟨sourceValues, same, last⟩ := publicationAtoms_noticeCarrier event atHead noticed
        subst event
        refine ⟨0, sourceValues, rfl, ?_⟩
        rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
        apply streamPublicationAtoms_before_streamNotices
        exact last.trans (streamPublicationAtoms_length ..)
      · have later : (publicationAtoms event).length ≤ index := by omega
        obtain ⟨sourceIndex, sourceValues, atSource, notices⟩ := ih
          (fun entry member => nonempty entry (List.mem_cons_of_mem _ member))
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨sourceIndex + 1, sourceValues, atSource, ?_⟩
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
          notices, publicationAtoms_streamNotices event (nonempty event List.mem_cons_self)]
        rfl

/-- A normalized item carrier retains the exact raw strict stream-notice prefix.
Witness: its raw event remains a singleton, and every earlier publisher step preserves
its notice list, independently of owner remapping or changes in event count.
-/
theorem IncrementalPublisher.normalizeBatch_itemNotice_streamPrefix
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index owner values groups streams}
    (selected
      : (publisher.normalizeBatch events).2[index]?
        = some (.streamValues owner values groups streams))
    : ∃ sourceIndex sourceValues,
        events[sourceIndex]? = some (.streamValues owner sourceValues groups streams)
        ∧ ((publisher.normalizeBatch events).2.take index).flatMap streamNoticeRefs
          = (events.take sourceIndex).flatMap rawStreamNoticeRefs := by
  induction events generalizing publisher index with
  | nil => simp [IncrementalPublisher.normalizeBatch] at selected
  | cons event rest ih =>
      rw [IncrementalPublisher.normalizeBatch_cons] at selected ⊢
      dsimp only at selected ⊢
      let head := publisher.handleWorkQueueEvent event
      let tail := head.1.normalizeBatch rest
      change (head.2 ++ tail.2)[index]? = _ at selected
      by_cases earlier : index < head.2.length
      · have atHead := (List.getElem?_append_left earlier).symm.trans selected
        obtain ⟨sourceValues, rfl, rfl⟩ := publisher.handleWorkQueueEvent_streamValues event atHead
        exact ⟨0, sourceValues, rfl, rfl⟩
      · have later : head.2.length ≤ index := by omega
        obtain ⟨sourceIndex, sourceValues, atSource, notices⟩ := ih head.1
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨sourceIndex + 1, sourceValues, atSource, ?_⟩
        change ((head.2 ++ tail.2).take index).flatMap streamNoticeRefs = _
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append, notices,
          publisher.handleWorkQueueEvent_streamNotices event]
        rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
