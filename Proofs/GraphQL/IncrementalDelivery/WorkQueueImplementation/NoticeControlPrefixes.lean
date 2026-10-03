import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupClosureAccounting

/-! Group notices and closures retain one common carrier cut through output expansion. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Group-success carriers stay singleton events through both expansion stages
-----------------------------------------------------------------------------------------

/-- An atomic group-success carrier retains both earlier group-control projections.
Witness: recurse by the selected position, using exact full projections for preceding
events. Its source carrier is unchanged, so neither projection includes the new notices.
-/
theorem publicationAtoms_groupSuccess_controls (events : List Execution.WorkQueueEvent)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    {index group groups streams}
    (selected
      : (events.flatMap publicationAtoms)[index]?
        = some (.groupSuccess group groups streams))
    : ∃ sourceIndex,
        events[sourceIndex]? = some (.groupSuccess group groups streams)
        ∧ ((events.flatMap publicationAtoms).take index).flatMap groupNoticeRefs
          = (events.take sourceIndex).flatMap groupNoticeRefs
        ∧ ((events.flatMap publicationAtoms).take index).flatMap groupClosureRefs
          = (events.take sourceIndex).flatMap groupClosureRefs := by
  induction events generalizing index with
  | nil => simp at selected
  | cons event rest ih =>
      rw [List.flatMap_cons] at selected ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans selected
        obtain ⟨rfl, rfl⟩ := publicationAtoms_groupSuccess event atHead
        exact ⟨0, rfl, rfl, rfl⟩
      · have later : (publicationAtoms event).length ≤ index := by omega
        obtain ⟨sourceIndex, atSource, notices, closures⟩ := ih
          (fun entry member => nonempty entry (List.mem_cons_of_mem _ member))
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨sourceIndex + 1, atSource, ?_, ?_⟩
        · rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
            notices, publicationAtoms_groupNotices event (nonempty event List.mem_cons_self)]
          rfl
        · rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
            closures, publicationAtoms_groupClosureRefs]
          rfl

/-- Normalizing a group-success carrier retains its exact earlier notices and closures.
Witness: the publisher changes only value owners, and both control projections commute
with its stateful output concatenation. The source index is shared by both equalities.
-/
theorem IncrementalPublisher.normalizeBatch_groupSuccess_controls
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index group groups streams}
    (selected
      : (publisher.normalizeBatch events).2[index]?
        = some (.groupSuccess group groups streams))
    : ∃ sourceIndex,
        events[sourceIndex]? = some (.groupSuccess group groups streams)
        ∧ ((publisher.normalizeBatch events).2.take index).flatMap groupNoticeRefs
          = (events.take sourceIndex).flatMap rawGroupNoticeRefs
        ∧ ((publisher.normalizeBatch events).2.take index).flatMap groupClosureRefs
          = (events.take sourceIndex).flatMap rawGroupClosureRefs := by
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
        obtain ⟨rfl, rfl⟩ := publisher.handleWorkQueueEvent_groupSuccess event atHead
        exact ⟨0, rfl, rfl, rfl⟩
      · have later : head.2.length ≤ index := by omega
        obtain ⟨sourceIndex, atSource, notices, closures⟩ := ih head.1
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨sourceIndex + 1, atSource, ?_, ?_⟩
        · change ((head.2 ++ tail.2).take index).flatMap groupNoticeRefs = _
          rw [List.take_append, List.take_of_length_le later, List.flatMap_append, notices]
          rw [publisher.handleWorkQueueEvent_groupNotices event]
          rfl
        · change ((head.2 ++ tail.2).take index).flatMap groupClosureRefs = _
          rw [List.take_append, List.take_of_length_le later, List.flatMap_append, closures]
          rw [publisher.handleWorkQueueEvent_groupClosureRefs event]
          rfl

-----------------------------------------------------------------------------------------
-- The final item atom carries notices; all earlier atoms carry no group controls
-----------------------------------------------------------------------------------------

/-- No group notice occurs before the final atom of a single stream-value batch.
Witness: every nonfinal item has empty child lists, and a singleton's strict prefix is empty.
-/
theorem streamPublicationAtoms_before_groupNotices (stream groups streams values)
    {index : Nat} (last : index + 1 = values.length)
    : ((streamPublicationAtoms stream groups streams values).take index).flatMap
        groupNoticeRefs
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
            groupNoticeRefs, List.map_nil, List.nil_append]
          exact ih (by simp only [List.length_cons] at last ⊢; omega)

/-- An item-notice atom retains both earlier group-control projections at one source index.
Witness: its notice identifies the final atom of the original item batch. Earlier items
of that batch have no group controls, while preceding complete events preserve both lists.
-/
theorem publicationAtoms_itemNotice_controls (events : List Execution.WorkQueueEvent)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    {index owner values groups streams child}
    (selected
      : (events.flatMap publicationAtoms)[index]?
        = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ sourceIndex sourceValues,
        events[sourceIndex]? = some (.streamValues owner sourceValues groups streams)
        ∧ ((events.flatMap publicationAtoms).take index).flatMap groupNoticeRefs
          = (events.take sourceIndex).flatMap groupNoticeRefs
        ∧ ((events.flatMap publicationAtoms).take index).flatMap groupClosureRefs
          = (events.take sourceIndex).flatMap groupClosureRefs := by
  induction events generalizing index with
  | nil => simp at selected
  | cons event rest ih =>
      rw [List.flatMap_cons] at selected ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans selected
        obtain ⟨sourceValues, same, last⟩ := publicationAtoms_noticeCarrier event atHead noticed
        subst event
        refine ⟨0, sourceValues, rfl, ?_, ?_⟩
        · rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
          apply streamPublicationAtoms_before_groupNotices
          exact last.trans (streamPublicationAtoms_length ..)
        · rw [List.take_append_of_le_length (Nat.le_of_lt earlier)]
          apply List.flatMap_eq_nil_iff.mpr
          intro entry member
          exact List.flatMap_eq_nil_iff.mp
            (publicationAtoms_groupClosureRefs (.streamValues owner sourceValues groups streams))
            entry (List.mem_of_mem_take member)
      · have later : (publicationAtoms event).length ≤ index := by omega
        obtain ⟨sourceIndex, sourceValues, atSource, notices, closures⟩ := ih
          (fun entry member => nonempty entry (List.mem_cons_of_mem _ member))
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨sourceIndex + 1, sourceValues, atSource, ?_, ?_⟩
        · rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
            notices, publicationAtoms_groupNotices event (nonempty event List.mem_cons_self)]
          rfl
        · rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
            closures, publicationAtoms_groupClosureRefs]
          rfl

/-- A normalized item carrier retains the raw strict notice and closure prefix together.
Witness: normalization leaves the item carrier as one event; the stateful traversal
preserves earlier group controls regardless of intervening object-owner remapping.
-/
theorem IncrementalPublisher.normalizeBatch_itemNotice_controls
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index owner values groups streams}
    (selected
      : (publisher.normalizeBatch events).2[index]?
        = some (.streamValues owner values groups streams))
    : ∃ sourceIndex sourceValues,
        events[sourceIndex]? = some (.streamValues owner sourceValues groups streams)
        ∧ ((publisher.normalizeBatch events).2.take index).flatMap groupNoticeRefs
          = (events.take sourceIndex).flatMap rawGroupNoticeRefs
        ∧ ((publisher.normalizeBatch events).2.take index).flatMap groupClosureRefs
          = (events.take sourceIndex).flatMap rawGroupClosureRefs := by
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
        exact ⟨0, sourceValues, rfl, rfl, rfl⟩
      · have later : head.2.length ≤ index := by omega
        obtain ⟨sourceIndex, sourceValues, atSource, notices, closures⟩ := ih head.1
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨sourceIndex + 1, sourceValues, atSource, ?_, ?_⟩
        · change ((head.2 ++ tail.2).take index).flatMap groupNoticeRefs = _
          rw [List.take_append, List.take_of_length_le later, List.flatMap_append, notices]
          rw [publisher.handleWorkQueueEvent_groupNotices event]
          rfl
        · change ((head.2 ++ tail.2).take index).flatMap groupClosureRefs = _
          rw [List.take_append, List.take_of_length_le later, List.flatMap_append, closures]
          rw [publisher.handleWorkQueueEvent_groupClosureRefs event]
          rfl

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
