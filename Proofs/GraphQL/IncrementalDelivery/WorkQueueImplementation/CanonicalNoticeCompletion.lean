import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeControlPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawNoticeHistoryCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeAncestorSemantics

/-! Actual notice-ancestor completions on the unchanged canonical explanation witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Keep the same selected raw carrier for both control projections
-----------------------------------------------------------------------------------------

/-- A canonical group carrier retains exact raw strict notice and closure prefixes.
Witness: accepted batches flatten to publisher replay; legal source payloads make atomic
splitting preserve notices. Both projections use the same indexed raw carrier.
-/
theorem Witness.groupNotice_rawControls {work inputs} {w : Witness}
    {index group groups streams}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    : ∃ position,
        ((initialQueue work).rawEventReplay inputs.flatten).2[position]?
          = some (.groupSuccess group groups streams)
        ∧ (w.events.take index).flatMap groupNoticeKeys
          = (((initialQueue work).rawEventReplay inputs.flatten).2.take position).flatMap
              rawGroupNoticeKeys
        ∧ (w.events.take index).flatMap groupClosureKeys
          = (((initialQueue work).rawEventReplay inputs.flatten).2.take position).flatMap
              rawGroupClosureKeys := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [exactHistory] at selected ⊢
  have rawShape := (initialQueue work).rawEventReplay_nonemptyValues inputs.flatten
    valid.nonemptyItems
  obtain ⟨sourceIndex, sourceAt, notices, closures⟩ := publicationAtoms_groupSuccess_controls _
    (IncrementalPublisher.normalizeBatch_nonemptyValues _ _ rawShape).2 selected
  obtain ⟨position, rawAt, rawNotices, rawClosures⟩ :=
    IncrementalPublisher.normalizeBatch_groupSuccess_controls _ _ sourceAt
  exact ⟨position, rawAt, notices.trans rawNotices, closures.trans rawClosures⟩

/-- A canonical item notice retains exact raw strict notice and closure prefixes.
Witness: the selected notice is on its batch's last item atom; all earlier atoms of that
batch have no group controls. Normalization then recovers one common raw carrier index.
-/
theorem Witness.itemNotice_rawControls {work inputs} {w : Witness}
    {index owner values groups streams child}
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ position rawValues,
        ((initialQueue work).rawEventReplay inputs.flatten).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ (w.events.take index).flatMap groupNoticeKeys
          = (((initialQueue work).rawEventReplay inputs.flatten).2.take position).flatMap
              rawGroupNoticeKeys
        ∧ (w.events.take index).flatMap groupClosureKeys
          = (((initialQueue work).rawEventReplay inputs.flatten).2.take position).flatMap
              rawGroupClosureKeys := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [exactHistory] at selected ⊢
  have rawShape := (initialQueue work).rawEventReplay_nonemptyValues inputs.flatten
    valid.nonemptyItems
  obtain ⟨sourceIndex, sourceValues, sourceAt, notices, closures⟩ :=
    publicationAtoms_itemNotice_controls _
      (IncrementalPublisher.normalizeBatch_nonemptyValues _ _ rawShape).2 selected noticed
  obtain ⟨position, rawValues, rawAt, rawNotices, rawClosures⟩ :=
    IncrementalPublisher.normalizeBatch_itemNotice_controls _ _ sourceAt
  exact ⟨position, rawValues, rawAt, notices.trans rawNotices, closures.trans rawClosures⟩

-----------------------------------------------------------------------------------------
-- An ancestor key cannot be supplied by an unrelated stream's announcement
-----------------------------------------------------------------------------------------

/-- An announced defer ancestor comes from initial groups or prior group notices.
Witness: generated key roles exclude every initial or carried stream descriptor, including
taskless ancestor records. Only actual output provenance is used, not notice admission.
-/
theorem groupNoticeAncestor_announced_group
    {work inputs index child dependencies key} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (known : GroupRecordAt work child dependencies) (ancestor : key ∈ dependencies)
    (announced : key ∈ announcedKeys (initialKeys work) (w.events.take index))
    : key
      ∈ (initialQueue work).rootGroups
        ++ (w.events.take index).flatMap groupNoticeKeys := by
  rcases List.mem_append.mp announced with initial | pending
  · rw [initialKeys, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · apply List.mem_append_left
      rwa [createWorkQueue_rootGroups]
    · obtain ⟨stream, member, same⟩ := List.mem_map.mp stream
      exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor
        ((createWorkQueue_initialStreams_nodeAt work).2 stream member) same.symm)
  · obtain ⟨event, prior, notice⟩ := List.mem_flatMap.mp pending
    have inWitness := List.mem_of_mem_take prior
    obtain ⟨position, selected⟩ := List.mem_iff_getElem?.mp inWitness
    have atFull := (Witness.canonical_event history selected).1
    have streamKnown := createWorkQueue_runNormalized_atomicStreamNoticesLocated valid event
      (List.mem_of_getElem? atFull)
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨event, prior, ?_⟩
    cases event <;> simp only [eventPending] at notice
    case groupSuccess group groups streams | streamValues group values groups streams =>
      rw [List.map_append] at notice
      rcases List.mem_append.mp notice with groupNotice | streamNotice
      · exact groupNotice
      · obtain ⟨stream, member, same⟩ := List.mem_map.mp streamNotice
        obtain ⟨enclosing, producer, located⟩ := streamKnown stream member
        exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor located
          same.symm)
    all_goals cases notice

/-- Every group-only closure is also a scheduler completion.
Witness: group success and failure are completion constructors; other group projections
are empty. Stream completion keys may additionally occur in the target list.
-/
theorem groupClosureKeys_subset_completed (events : List Execution.WorkQueueEvent)
    : (events.flatMap groupClosureKeys).Subset (completedKeys events) := by
  intro key member
  obtain ⟨event, emitted, closed⟩ := List.mem_flatMap.mp member
  refine List.mem_flatMap.mpr ⟨event, emitted, ?_⟩
  cases event <;> simp_all [groupClosureKeys, eventCompleted]

-----------------------------------------------------------------------------------------
-- Discharge the concrete announced-or-completed status alternative
-----------------------------------------------------------------------------------------

/-- An announced ancestor completes by the actual canonical group-success notice carrier.
Witness: role separation identifies its group announcement; the joint raw-prefix bridge
and source-history completion theorem transport its closure through the same carrier.
-/
theorem groupNoticeAncestor_completed
    {work inputs index group groups streams child dependencies key} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (announced : key ∈ announcedKeys (initialKeys work) (w.events.take index))
    : key ∈ completedKeys (w.events.take index ++ [.groupSuccess group [] []]) := by
  have groupNotice := groupNoticeAncestor_announced_group generated valid history known
    ancestor announced
  obtain ⟨position, atRaw, notices, closures⟩ :=
    Witness.groupNotice_rawControls valid started history selected
  rw [notices] at groupNotice
  have accepted := (initialQueue work).batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have closed := generated.rawEventReplay_groupNoticeAncestor_completed valid accepted atRaw
    noticed known ancestor groupNotice
  rw [List.take_add_one, atRaw] at closed
  simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
    rawGroupClosureKeys, ← closures] at closed
  apply groupClosureKeys_subset_completed
  simpa only [List.flatMap_append, List.flatMap_singleton, groupClosureKeys] using closed

/-- An announced ancestor of an item-carried group notice completes strictly before it.
Witness: the item carrier's joint raw boundary retains group controls, and its source
completion theorem rules out using any closure from the current handler's later drain.
-/
theorem itemGroupNoticeAncestor_completed
    {work inputs index owner values groups streams child dependencies key} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (announced : key ∈ announcedKeys (initialKeys work) (w.events.take index))
    : key ∈ completedKeys (w.events.take index) := by
  have groupNotice := groupNoticeAncestor_announced_group generated valid history known
    ancestor announced
  obtain ⟨position, rawValues, atRaw, notices, closures⟩ :=
    Witness.itemNotice_rawControls valid started history selected (List.mem_append_left _ noticed)
  rw [notices] at groupNotice
  have accepted := (initialQueue work).batchesStarted_acceptsBatch inputs
    (by rwa [← inputsStarted_eq_batchesStarted])
  have closed := generated.rawEventReplay_itemNoticeAncestor_completed valid accepted atRaw
    noticed known ancestor groupNotice
  apply groupClosureKeys_subset_completed
  rwa [closures]

-----------------------------------------------------------------------------------------
-- The scheduler's dependency clause now follows from the unchanged source laws
-----------------------------------------------------------------------------------------

/-- Every ancestor of an actual group-success notice is ready at its frozen carrier cut.
Witness: canonical publication accounting supplies all ancestor tasks, supported
publication supplies health, and the exact completion bridge closes any announced key.
Unannounced ancestors use silent accounting, including taskless registration shells.
-/
theorem groupNoticeAncestor_dependencySatisfied
    {work inputs index group groups streams child dependencies} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (failures : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ key ∈ dependencies,
        DependencySatisfied work (initialKeys work) w.matching
          (w.events.take index ++ [.groupSuccess group [] []])
          (w.failures.filter (fun entry => entry.1 ≤ index)) key := by
  classical
  intro key ancestor
  apply dependencySatisfied_noticeCarrier_of_status selected
    (groupNoticeAncestor_healthy generated valid started history ledger support failures
      selected noticed known key ancestor)
    (groupNoticeAncestor_nodeAccounted generated valid started history ledger selected
      noticed known ancestor _)
  by_cases announced : key ∈ announcedKeys (initialKeys work) (w.events.take index)
  · exact .inl (groupNoticeAncestor_completed generated valid started history selected
      noticed known ancestor announced)
  · exact .inr announced

/-- Every ancestor of an item-carried group notice is ready at its frozen carrier cut.
Witness: its tasks and any announced closure precede the source item's leading carrier.
The shared semantic health theorem remains valid through the final item atom with frozen
failure cuts. No completion from the handler's later recursive drain is used.
-/
theorem itemGroupNoticeAncestor_dependencySatisfied
    {work inputs index owner values groups streams child dependencies} {w : Witness}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (support : PublicationSupport work w.matching w.events w.failures)
    (failures : AnnouncedFailures work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    : ∀ key ∈ dependencies,
        DependencySatisfied work (initialKeys work) w.matching
          (w.events.take index ++ [.streamValues owner values [] []])
          (w.failures.filter (fun entry => entry.1 ≤ index)) key := by
  classical
  intro key ancestor
  apply dependencySatisfied_noticeCarrier_of_status selected
    (itemGroupNoticeAncestor_healthy generated valid started history ledger support failures
      selected noticed known key ancestor)
    (itemGroupNoticeAncestor_nodeAccounted generated valid started history ledger selected
      noticed known ancestor _)
  by_cases announced : key ∈ announcedKeys (initialKeys work) (w.events.take index)
  · left
    have closed := itemGroupNoticeAncestor_completed generated valid started history selected
      noticed known ancestor announced
    simpa only [completedKeys, List.flatMap_append, List.flatMap_singleton,
      withoutChildNotices, eventCompleted, List.append_nil] using closed
  · exact .inr announced

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
