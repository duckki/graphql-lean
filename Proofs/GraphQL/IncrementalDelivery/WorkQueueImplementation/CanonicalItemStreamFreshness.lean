import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeRegistry
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamNoticePrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CanonicalGroupNoticeFreshness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamNoticeAdmission

/-! Item-produced stream notices satisfy freshness on the canonical shared witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Registration remembers old notices even after their streams have completed
-----------------------------------------------------------------------------------------

/-- A raw item-carried stream ref repeats neither an old registration nor an earlier notice.
Witness: its carrier leads its source handler, whose fresh-selection theorem excludes the
entry registry; every earlier notice remains in that registry after arbitrary replay.
-/
theorem State.rawEventReplay_itemStreamNoticeFresh (queue : State)
    (events : List GraphEvent) {index owner values groups streams child}
    (selected
      : (queue.rawEventReplay events).2[index]?
        = some (.streamValues owner values groups streams))
    (noticed : child ∈ streams)
    : child.ref
      ∉ queue.streams.map (fun stream => stream.node.ref)
        ++ ((queue.rawEventReplay events).2.take index).flatMap rawStreamNoticeRefs := by
  obtain ⟨before, event, after, position, _, emitted, prior⟩ :=
    queue.rawEventReplay_output_prefix_at events selected
  obtain ⟨stream, items, rfl⟩ :=
    (queue.replayGraphEvents before).handleGraphEvent_streamValues_source event emitted
  have zero := (queue.replayGraphEvents before).streamItems_carrier_index stream items emitted
  have fresh := (queue.replayGraphEvents before).streamItems_notices_fresh stream items emitted
  rw [prior, zero, List.take_zero, List.append_nil]
  intro repeated
  apply fresh.2 child noticed
  have registered := queue.rawEventReplay_streamRegistry before repeated
  rwa [State.rawEventReplay_state] at registered

namespace ConformancePlan

/-- An announced structural stream ref came from an initial or carried stream notice.
Witness: generated node roles exclude initial supported group refs and actual group
notices. This does not assume either notice freshness or output admission.
-/
theorem streamNode_announced_stream {work inputs index child dependencies producer}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (known : NodeAt work child .stream dependencies producer)
    (announced : child.ref ∈ announcedRefs (initialRefs work) (w.events.take index))
    : child.ref
      ∈ (initialQueue work).initialStreams.map Execution.DeliveryNode.ref
        ++ (w.events.take index).flatMap streamNoticeRefs := by
  rcases List.mem_append.mp announced with initial | pending
  · rw [initialRefs, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · have active : child.ref ∈ (initialQueue work).rootGroups := by
        rwa [createWorkQueue_rootGroups]
      obtain ⟨parents, group, birth, descriptor, same⟩ :=
        (createWorkQueue_fromSpec_groupRefSupport work).roots child.ref active
      exact False.elim (generated.groupStreamRefsDisjoint descriptor known same)
    · exact List.mem_append_left _ stream
  · obtain ⟨event, prior, notice⟩ := List.mem_flatMap.mp pending
    obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take prior)
    have groupsKnown := createWorkQueue_runNormalized_atomicGroupNoticesLocated generated
      valid event
      (List.mem_of_getElem? (Witness.canonical_event history selected).1)
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨event, prior, ?_⟩
    cases event <;> simp only [eventPending] at notice
    case groupSuccess group groups streams | streamValues group values groups streams =>
      rw [List.map_append] at notice
      rcases List.mem_append.mp notice with groupNotice | streamNotice
      · obtain ⟨group, member, same⟩ := List.mem_map.mp groupNotice
        obtain ⟨parents, birth, descriptor⟩ := groupsKnown group member
        exact False.elim (generated.groupStreamRefsDisjoint descriptor known same)
      · exact streamNotice
    all_goals cases notice

/-- A canonical item notice retains its exact raw strict stream-notice prefix.
Witness: started replay supplies the actual publisher history; final-item atomization
and normalization preserve one common indexed carrier and all preceding stream notices.
-/
theorem Witness.itemNotice_rawStreamPrefix {work inputs} {w : Witness}
    {index owner values groups streams child}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ position rawValues,
        ((initialQueue work).rawEventReplay inputs.flatten).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ (w.events.take index).flatMap streamNoticeRefs
          = (((initialQueue work).rawEventReplay inputs.flatten).2.take position).flatMap
              rawStreamNoticeRefs := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [exactHistory] at selected ⊢
  have rawShape := (initialQueue work).rawEventReplay_nonemptyValues inputs.flatten
    valid.nonemptyItems
  obtain ⟨sourceIndex, sourceValues, sourceAt, notices⟩ :=
    publicationAtoms_itemNotice_streamPrefix _
      (IncrementalPublisher.normalizeBatch_nonemptyValues _ _ rawShape).2 selected noticed
  obtain ⟨position, rawValues, rawAt, rawNotices⟩ :=
    IncrementalPublisher.normalizeBatch_itemNotice_streamPrefix _ _ sourceAt
  exact ⟨position, rawValues, rawAt, notices.trans rawNotices⟩

/-- An actual item-carried stream notice is fresh against every earlier announcement.
Witness: role separation discards group notices, and the exact raw prefix uses permanent
stream registration to exclude both initial notices and previously closed streams.
-/
theorem itemStreamNotice_fresh {work inputs index owner values groups streams child}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ streams)
    : child.ref ∉ announcedRefs (initialRefs work) (w.events.take index) := by
  have known := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid _
    (List.mem_of_getElem? (Witness.canonical_event history selected).1) child noticed
  obtain ⟨dependencies, producer, descriptor⟩ := known
  obtain ⟨position, rawValues, rawAt, notices⟩ := Witness.itemNotice_rawStreamPrefix
    valid started history selected (List.mem_append_right groups noticed)
  intro announced
  have repeated := streamNode_announced_stream generated valid history descriptor announced
  rw [notices] at repeated
  apply (initialQueue work).rawEventReplay_itemStreamNoticeFresh inputs.flatten rawAt
    noticed
  rcases List.mem_append.mp repeated with initial | prior
  · apply List.mem_append_left
    obtain ⟨node, member, same⟩ := List.mem_map.mp initial
    have registered := (State.maybeIntegrateWork_streams_registered ({} : State)
      (Work.fromExecution work)).2 member
    obtain ⟨stream, stored, equal⟩ := List.mem_map.mp registered
    have registry : (initialQueue work).streams
        = (({} : State).maybeIntegrateWork (Work.fromExecution work)).1.streams := by
      let integrated := ({} : State).maybeIntegrateWork (Work.fromExecution work)
      let pruned := integrated.1.pruneEmptyGroups integrated.2.newGroups
      change (pruned.1.startNewWork { integrated.2 with newGroups := pruned.2 }).streams
        = integrated.1.streams
      rw [State.startNewWork_streams, State.pruneEmptyGroups_streams]
    rw [registry]
    exact List.mem_map.mpr ⟨stream, stored,
      (congrArg Execution.DeliveryNode.ref equal).trans same⟩
  · exact List.mem_append_right _ prior

/-- Item-produced stream notices satisfy full eligibility without an extra freshness law.
Witness: derive freshness from actual registration and combine it with the existing joint
producer, dependency, and failure-support certificates on the unchanged witness.
-/
theorem itemStreamNotice_canAnnounce_of_replay
    {work inputs w index stream values groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (announced : AnnouncedFailures work w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (producers : StreamNoticeProducers work w)
    (selected : w.events[index]? = some (.streamValues stream values groups streams))
    (noticed : child ∈ streams)
    : ∃ producer,
        NodeAt work child .stream [] producer
        ∧ CanAnnounce work (initialRefs work) w.matching
            (w.events.take index ++ [.streamValues stream values [] []])
            (w.failures.filter (fun entry => decide (entry.1 ≤ index)))
            child .stream [] producer :=
  itemStreamNotice_canAnnounce generated valid started history announced support producers
    selected noticed
    (itemStreamNotice_fresh generated valid started history selected noticed)

-----------------------------------------------------------------------------------------
-- Both child lists on one item carrier have distinct refs
-----------------------------------------------------------------------------------------

/-- A canonical item carrier's stream-notice refs are internally unique.
Witness: recover its exact raw handler and reuse the concrete multi-item fresh inventory;
an empty notice list is immediate and requires no carrier-position inversion.
-/
theorem itemStreamNoticeRefs_nodup {work inputs owner values groups streams} {index : Nat}
    {w : Witness} (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    : (streams.map Execution.DeliveryNode.ref).Nodup := by
  cases streams with
  | nil => simp
  | cons child rest =>
      obtain ⟨position, rawValues, rawAt, _⟩ := Witness.itemNotice_rawStreamPrefix
        valid started history selected (List.mem_append_right groups List.mem_cons_self)
      obtain ⟨before, event, after, localIndex, _, emitted, _⟩ :=
        (initialQueue work).rawEventReplay_output_prefix_at inputs.flatten rawAt
      obtain ⟨stream, items, rfl⟩ :=
        ((initialQueue work).replayGraphEvents before).handleGraphEvent_streamValues_source
          event emitted
      exact (((initialQueue work).replayGraphEvents before).streamItems_notices_fresh
        stream items emitted).1

/-- The combined group/stream notice list on an item carrier has no repeated ref.
Witness: global group uniqueness gives its group sublist; fresh registration gives stream
uniqueness; generated group/stream roles exclude collisions between the two lists.
-/
theorem itemNoticeRefs_nodup {work inputs owner values groups streams} {index : Nat}
    {w : Witness} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    : ((groups ++ streams).map Execution.DeliveryNode.ref).Nodup := by
  have unique := (List.nodup_append.mp
    (groupNoticeRefs_nodup generated valid started history)).2.1
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp (List.mem_of_getElem? selected)
  rw [split, List.flatMap_append, List.flatMap_cons] at unique
  have groupsUnique := (List.nodup_append.mp (List.nodup_append.mp unique).2.1).1
  have atFull := List.mem_of_getElem? (Witness.canonical_event history selected).1
  have groupKnown := createWorkQueue_runNormalized_atomicGroupNoticesLocated generated valid
    _ atFull
  have streamKnown := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid _ atFull
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨groupsUnique,
    itemStreamNoticeRefs_nodup valid started history selected, ?_⟩
  intro first groupMember second streamMember same
  obtain ⟨group, included, groupRef⟩ := List.mem_map.mp groupMember
  obtain ⟨stream, noticed, streamRef⟩ := List.mem_map.mp streamMember
  obtain ⟨parents, birth, descriptor⟩ := groupKnown group included
  obtain ⟨enclosing, producer, known⟩ := streamKnown stream noticed
  exact generated.groupStreamRefsDisjoint descriptor known
    (groupRef.trans (same.trans streamRef.symm))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
