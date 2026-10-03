import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamAnnouncementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalItemStreamFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalStreamCompletion

/-! Group-released stream notices are fresh on the common conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Replay uniqueness survives normalization and atomic expansion
-----------------------------------------------------------------------------------------

/-- Initial and canonical carried stream refs form one globally distinct history.
Witness: actual replay consumes registered links once, while normalization and legal
atomic expansion preserve exactly the ordered notice inventory.
-/
theorem streamNoticeRefs_nodup {work inputs} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    : ((initialQueue work).initialStreams.map Execution.DeliveryNode.ref
        ++ w.events.flatMap streamNoticeRefs).Nodup := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [exactHistory, atomicStreamNotices _ _
    ((initialQueue work).rawEventReplay_nonemptyValues inputs.flatten valid.nonemptyItems)]
  exact ((createWorkQueue_streamAnnouncementInventory (Work.fromExecution work)).rawEventReplay
    (createWorkQueue_childStreamsMatchWork _ _) generated inputs.flatten
    (fun _ member => valid.event_matches member)).unique

/-- Any canonical stream notice excludes all strictly earlier stream notices.
Witness: the selected prefix is a sublist of the globally unique inventory; splitting it
at the carrier separates old refs from every ref announced by that carrier.
-/
theorem streamNotice_ref_fresh {work inputs index event ref} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event) (noticed : ref ∈ streamNoticeRefs event)
    : ref
      ∉ (initialQueue work).initialStreams.map Execution.DeliveryNode.ref
        ++ (w.events.take index).flatMap streamNoticeRefs := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp selected
  have split : w.events = w.events.take index ++ event :: w.events.drop (index + 1) := by
    rw [← value, ← List.drop_eq_getElem_cons bound]
    exact (List.take_append_drop index w.events).symm
  have unique := streamNoticeRefs_nodup generated valid started history
  conv at unique => arg 1; arg 2; arg 2; rw [split]
  simp only [List.flatMap_append, List.flatMap_cons, ← List.append_assoc] at unique
  intro repeated
  exact (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
    ref repeated ref noticed rfl

-----------------------------------------------------------------------------------------
-- Successful group controls have fresh, eligible, and distinct child streams
-----------------------------------------------------------------------------------------

/-- A group-released stream is fresh against all earlier group and stream announcements.
Witness: generated role separation converts a repeated notice to a stream-only notice,
which contradicts the derived global stream inventory.
-/
theorem groupStreamNotice_fresh {work inputs index group groups streams child}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ streams)
    : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index) := by
  obtain ⟨dependencies, producer, known⟩ :=
    createWorkQueue_runNormalized_atomicStreamNoticesLocated valid _
      (List.mem_of_getElem? (Witness.canonical_event history selected).1) child noticed
  intro repeated
  exact streamNotice_ref_fresh generated valid started history selected
    (List.mem_map_of_mem noticed)
    (streamNode_announced_stream generated valid history known repeated)

/-- Actual group-produced stream notices satisfy complete eligibility without extra laws.
Witness: derive freshness from consumed links and reuse the existing shared producer,
healthy dependency, and historical failure-support certificates.
-/
theorem groupStreamNotice_canAnnounce_of_replay
    {work inputs w index group groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (healthy : GroupSuccessesHealthy work w) (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ streams)
    : ∃ dependencies producer,
        NodeAt work child .stream dependencies producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [.groupSuccess group [] []])
            (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
            child .stream dependencies producer :=
  groupStreamNotice_canAnnounce generated valid history announced support healthy
    producers selected noticed
    (groupStreamNotice_fresh generated valid started history selected noticed)

/-- A successful group's combined child-notice list has no repeated ref.
Witness: both global notice inventories supply internal uniqueness; generated roles
exclude collisions between group and stream lists on the same carrier.
-/
theorem groupCarrierNoticeRefs_nodup {work inputs group groups streams} {index : Nat}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : ((groups ++ streams).map Execution.DeliveryNode.ref).Nodup := by
  have groupUnique := (List.nodup_append.mp
    (groupNoticeRefs_nodup generated valid started history)).2.1
  have streamUnique := (List.nodup_append.mp
    (streamNoticeRefs_nodup generated valid started history)).2.1
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp (List.mem_of_getElem? selected)
  rw [split, List.flatMap_append, List.flatMap_cons] at groupUnique streamUnique
  have atFull := List.mem_of_getElem? (Witness.canonical_event history selected).1
  have groupKnown :=
    createWorkQueue_runNormalized_atomicGroupNoticesLocated generated valid _ atFull
  have streamKnown := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid _ atFull
  rw [List.map_append]
  refine List.nodup_append.mpr
    ⟨(List.nodup_append.mp (List.nodup_append.mp groupUnique).2.1).1,
      (List.nodup_append.mp (List.nodup_append.mp streamUnique).2.1).1, ?_⟩
  intro first groupMember second streamMember same
  obtain ⟨group, included, groupRef⟩ := List.mem_map.mp groupMember
  obtain ⟨stream, noticed, streamRef⟩ := List.mem_map.mp streamMember
  obtain ⟨parents, birth, descriptor⟩ := groupKnown group included
  obtain ⟨enclosing, producer, known⟩ := streamKnown stream noticed
  exact generated.groupStreamRefsDisjoint descriptor known
    (groupRef.trans (same.trans streamRef.symm))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
