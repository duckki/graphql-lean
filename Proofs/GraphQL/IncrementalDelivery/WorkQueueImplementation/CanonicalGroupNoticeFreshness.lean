import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeSeparation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalNoticeCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BatchedNoticeHistory

/-! Actual canonical group notices are fresh without assuming output admission. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Group and stream roles exclude announcements of the wrong kind
-----------------------------------------------------------------------------------------

/-- An announced generated group ref came from an initial or carried group notice.
Witness: generated node roles exclude every initial and carried stream descriptor.
This uses source provenance rather than already-admitted notices or unique wire IDs.
-/
theorem groupNode_announced_group {work inputs index child dependencies producer}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (known : NodeAt work child .group dependencies producer)
    (announced : child.ref ∈ announcedRefs (initialRefs work) (w.events.take index))
    : child.ref
      ∈ (initialQueue work).rootGroups
        ++ (w.events.take index).flatMap groupNoticeRefs := by
  rcases List.mem_append.mp announced with initial | pending
  · rw [initialRefs, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · apply List.mem_append_left
      rwa [createWorkQueue_rootGroups]
    · obtain ⟨stream, member, same⟩ := List.mem_map.mp stream
      exact False.elim (generated.groupStreamRefsDisjoint known
        ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm)
  · obtain ⟨event, prior, notice⟩ := List.mem_flatMap.mp pending
    obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take prior)
    have streamKnown := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid event
      (List.mem_of_getElem? (Witness.canonical_event history selected).1)
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨event, prior, ?_⟩
    cases event <;> simp only [eventPending] at notice
    case groupSuccess group groups streams | streamValues group values groups streams =>
      rw [List.map_append] at notice
      rcases List.mem_append.mp notice with groupNotice | streamNotice
      · exact groupNotice
      · obtain ⟨stream, member, same⟩ := List.mem_map.mp streamNotice
        obtain ⟨enclosing, birth, located⟩ := streamKnown stream member
        exact False.elim (generated.groupStreamRefsDisjoint known located same.symm)
    all_goals cases notice

/-- Initial and canonical carried group refs are globally duplicate-free.
Witness: legal source payloads make normalization and atomic expansion retain the exact
raw group-notice inventory, whose uniqueness is derived from actual queue replay.
-/
theorem groupNoticeRefs_nodup {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : ((initialQueue work).rootGroups ++ w.events.flatMap groupNoticeRefs).Nodup := by
  let publisher : IncrementalPublisher :=
    { active := (initialQueue work).initialGroups ++ (initialQueue work).initialStreams }
  have controls := atomicGroupNotices publisher ((initialQueue work).rawBatches inputs).2
    ((initialQueue work).rawBatches_nonemptyValues inputs valid.nonemptyItems)
  rw [Witness.rawBatches_shape history] at controls
  have same : w.events.flatMap groupNoticeRefs =
      ((initialQueue work).rawBatches inputs).2.flatMap rawGroupNoticeRefs := by
    split at controls <;> simpa [List.flatMap_append, groupNoticeRefs] using controls
  rw [same]
  exact generated.rawBatches_groupRefs_nodup valid started

-----------------------------------------------------------------------------------------
-- Canonical carrier origins retain the exact strict raw notice prefix
-----------------------------------------------------------------------------------------

/-- Every actual canonical group notice is fresh against all previous announcements.
Witness: the unique actual batch notice inventory separates the selected carrier from
its strict prefix. Generated roles exclude announcements from unrelated stream refs.
-/
theorem groupNotice_fresh {work inputs index event child dependencies producer}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    (noticed : child.ref ∈ groupNoticeRefs event)
    (known : NodeAt work child .group dependencies producer)
    : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index) := by
  intro announced
  have repeated := groupNode_announced_group generated valid history known announced
  have unique := groupNoticeRefs_nodup generated valid started history
  have split : w.events = w.events.take index ++ w.events.drop index :=
    (List.take_append_drop index w.events).symm
  conv at unique => arg 1; arg 2; rw [split]
  rw [List.flatMap_append, ← List.append_assoc] at unique
  have suffix : event ∈ w.events.drop index := List.mem_of_getElem?
    (show (w.events.drop index)[0]? = some event by simpa using selected)
  exact (List.nodup_append.mp unique).2.2 child.ref repeated child.ref
    (List.mem_flatMap.mpr ⟨event, suffix, noticed⟩) rfl

-----------------------------------------------------------------------------------------
-- Normalization and atomization preserve the entire ordered group-notice inventory
-----------------------------------------------------------------------------------------

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
