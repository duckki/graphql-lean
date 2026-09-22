import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemStreamReleaseAtoms
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationSupport
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ItemNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RawCarrierCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamActions

/-! Carried group and stream notices retain one joint raw/atomic publication boundary. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Either kind of item-carried notice identifies the final atom of the same source event
-----------------------------------------------------------------------------------------

/-- An atom carrying either kind of child notice is the final item of its original batch.
Witness: earlier item atoms carry neither group nor stream notices; the final atom copies
both lists unchanged. The witness does not identify a carrier by payload equality.
-/
theorem streamPublicationAtoms_noticeCarrier (stream groups streams values)
    {index owner items newGroups newStreams child}
    (selected
      : (streamPublicationAtoms stream groups streams values)[index]?
        = some (.streamValues owner items newGroups newStreams))
    (noticed : child ∈ newGroups ++ newStreams)
    : owner = stream
      ∧ newGroups = groups
      ∧ newStreams = streams
      ∧ index + 1 = values.length := by
  induction values using streamPublicationAtoms.induct generalizing index with
  | case1 => simp [streamPublicationAtoms] at selected
  | case2 value =>
      cases index with
      | zero =>
          have same := Execution.WorkQueueEvent.streamValues.inj (Option.some.inj selected)
          exact ⟨same.1.symm, same.2.2.1.symm, same.2.2.2.symm, rfl⟩
      | succ index => simp [streamPublicationAtoms] at selected
  | case3 value next rest ih =>
      cases index with
      | zero =>
          have same := Execution.WorkQueueEvent.streamValues.inj (Option.some.inj selected)
          rw [← same.2.2.1, ← same.2.2.2] at noticed
          cases noticed
      | succ index =>
          obtain ⟨ownerSame, groupsSame, streamsSame, size⟩ := ih selected
          exact ⟨
            ownerSame,
            groupsSame,
            streamsSame,
            by simp only [List.length_cons] at *; omega
          ⟩

/-- A notice-bearing item atom ends the expansion of its exact original event.
Witness: other event constructors cannot produce an item carrier; either child-notice
list identifies the final item atom, retaining both original notice lists together.
-/
theorem publicationAtoms_noticeCarrier (event : Execution.WorkQueueEvent)
    {index owner items groups streams child}
    (selected
      : (publicationAtoms event)[index]?
        = some (.streamValues owner items groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ values,
        event = .streamValues owner values groups streams
        ∧ index + 1 = (publicationAtoms event).length := by
  have member := List.mem_of_getElem? selected
  cases event with
  | groupValues group values =>
      obtain ⟨value, _, impossible⟩ := List.mem_map.mp member
      cases impossible
  | streamValues stream values newGroups newStreams =>
      obtain ⟨rfl, rfl, rfl, size⟩ :=
        streamPublicationAtoms_noticeCarrier stream newGroups newStreams values selected noticed
      exact ⟨values, rfl, size.trans (streamPublicationAtoms_length ..).symm⟩
  | groupSuccess | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      simp [publicationAtoms] at member

/-- A notice carrier preserves its strict object count and inclusive item count together.
Witness: locate the final item atom inside the concatenated expansion. Its preceding item
atoms add no object values, while its inclusive prefix contains the whole original batch.
Both equalities refer to the same source index, even when event payloads repeat.
-/
theorem publicationAtoms_noticeCarrier_prefix (events : List Execution.WorkQueueEvent)
    {index owner items groups streams child}
    (selected
      : (events.flatMap publicationAtoms)[index]?
        = some (.streamValues owner items groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ sourceIndex values,
        events[sourceIndex]? = some (.streamValues owner values groups streams)
        ∧ (((events.flatMap publicationAtoms).take index).flatMap
            normalizedObjectValues).length
          = ((events.take sourceIndex).flatMap normalizedObjectValues).length
        ∧ (((events.flatMap publicationAtoms).take (index + 1)).flatMap
            normalizedItemValues).length
          = ((events.take (sourceIndex + 1)).flatMap normalizedItemValues).length := by
  induction events generalizing index with
  | nil => simp at selected
  | cons event rest ih =>
      rw [List.flatMap_cons] at selected ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans selected
        obtain ⟨values, same, endAt⟩ := publicationAtoms_noticeCarrier event atHead noticed
        refine ⟨0, values, same ▸ rfl, ?_, ?_⟩
        · have empty : (publicationAtoms event).flatMap normalizedObjectValues = [] := by
            rw [(publicationAtoms_values event).1, same]
          have initialEmpty : ((publicationAtoms event).take index).flatMap
              normalizedObjectValues = [] :=
            List.flatMap_eq_nil_iff.mpr (fun entry member =>
              List.flatMap_eq_nil_iff.mp empty entry (List.mem_of_mem_take member))
          rw [List.take_append_of_le_length (Nat.le_of_lt earlier), initialEmpty]
          rfl
        · rw [endAt, List.take_left, (publicationAtoms_values event).2]
          simp
      · have later : (publicationAtoms event).length ≤ index := by omega
        have atTail := (List.getElem?_append_right later).symm.trans selected
        obtain ⟨sourceIndex, values, sourceAt, objectCount, itemCount⟩ := ih atTail
        refine ⟨sourceIndex + 1, values, sourceAt, ?_, ?_⟩
        · rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
            List.length_append, objectCount, (publicationAtoms_values event).1]
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
        · rw [List.take_append,
            List.take_of_length_le (by omega : (publicationAtoms event).length ≤ index + 1),
            show index + 1 - (publicationAtoms event).length
              = index - (publicationAtoms event).length + 1 by omega,
            List.flatMap_append, List.length_append, itemCount, (publicationAtoms_values event).2]
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]

-----------------------------------------------------------------------------------------
-- Publisher normalization retains both counts at that same raw carrier
-----------------------------------------------------------------------------------------

/-- A normalized item carrier keeps strict object and inclusive item counts jointly.
Witness: invert its singleton raw event and recurse through the stateful publisher fold.
Earlier object owner remapping changes event indices but neither projected value count.
-/
theorem IncrementalPublisher.normalizeBatch_streamCarrier_prefix
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index owner values groups streams}
    (selected
      : (publisher.normalizeBatch events).2[index]?
        = some (.streamValues owner values groups streams))
    : ∃ rawIndex rawValues,
        events[rawIndex]? = some (.streamValues owner rawValues groups streams)
        ∧ (((publisher.normalizeBatch events).2.take index).flatMap
            normalizedObjectValues).length
          = ((events.take rawIndex).flatMap WorkQueueEvent.objectValues).length
        ∧ (((publisher.normalizeBatch events).2.take (index + 1)).flatMap
            normalizedItemValues).length
          = ((events.take (rawIndex + 1)).flatMap WorkQueueEvent.itemValues).length := by
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
        obtain ⟨rawValues, rfl, rfl⟩ := publisher.handleWorkQueueEvent_streamValues event atHead
        refine ⟨0, rawValues, rfl, rfl, ?_⟩
        simp [IncrementalPublisher.handleWorkQueueEvent, normalizedItemValues,
          WorkQueueEvent.itemValues]
      · have later : head.2.length ≤ index := by omega
        have atTail := (List.getElem?_append_right later).symm.trans selected
        obtain ⟨rawIndex, rawValues, rawAt, objectCount, itemCount⟩ := ih head.1 atTail
        refine ⟨rawIndex + 1, rawValues, rawAt, ?_, ?_⟩
        · change (((head.2 ++ tail.2).take index).flatMap normalizedObjectValues).length = _
          rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
            List.length_append, objectCount]
          have count := congrArg List.length (publisher.handleWorkQueueEvent_objectValues event)
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          exact congrArg (· + _) count
        · change (((head.2 ++ tail.2).take (index + 1)).flatMap normalizedItemValues).length = _
          rw [List.take_append, List.take_of_length_le (by omega : head.2.length ≤ index + 1),
            show index + 1 - head.2.length = index - head.2.length + 1 by omega,
            List.flatMap_append, List.length_append, itemCount]
          simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          exact congrArg (· + _) (congrArg List.length
            (publisher.handleWorkQueueEvent_itemValues event))

-----------------------------------------------------------------------------------------
-- Canonical atomic carriers identify their real source-handler boundaries
-----------------------------------------------------------------------------------------

/-- A raw item-value carrier can only have come from a stream-items source event.
Witness: output stream actions are a subsequence of the source's action; task events have
none, and stream completions have a distinct closing flag.
-/
theorem State.handleGraphEvent_streamValues_source (queue : State) (event : GraphEvent)
    {index : Nat} {owner values groups streams}
    (selected
      : (queue.handleGraphEvent event).2[index]?
        = some (.streamValues owner values groups streams))
    : ∃ stream items, event = .streamItems stream items := by
  have action := (queue.handleGraphEvent_streamActions event).subset
    (List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? selected, rfl⟩)
  have source : event.streamAction = some (owner.key, false) := by
    simpa only [Option.mem_toList] using action
  cases event with
  | streamItems stream items => exact ⟨stream, items, rfl⟩
  | taskSuccess | taskFailure | streamSuccess | streamFailure =>
      simp [GraphEvent.streamAction] at source

namespace ConformancePlan

/-- A canonical item notice retains both prefix counts at one raw carrier position.
Witness: started batches flatten to the same publisher replay; invert atomization and
normalization without choosing a different publication matching or carrier occurrence.
-/
theorem Witness.itemNotice_rawPrefix {work inputs} {w : Witness}
    {index owner values groups streams child}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ position rawValues,
        ((initialQueue work).rawEventReplay inputs.flatten).2[position]?
          = some (.streamValues owner rawValues groups streams)
        ∧ ((w.events.take index).flatMap normalizedObjectValues).length
          = ((((initialQueue work).rawEventReplay inputs.flatten).2.take position).flatMap
              WorkQueueEvent.objectValues).length
        ∧ ((w.events.take (index + 1)).flatMap normalizedItemValues).length
          = ((((initialQueue work).rawEventReplay inputs.flatten).2.take
                (position + 1)).flatMap
              WorkQueueEvent.itemValues).length := by
  have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [exactHistory] at selected ⊢
  obtain ⟨sourceIndex, sourceValues, sourceAt, objectCount, itemCount⟩ :=
    publicationAtoms_noticeCarrier_prefix _ selected noticed
  obtain ⟨position, rawValues, rawAt, rawObjects, rawItems⟩ :=
    IncrementalPublisher.normalizeBatch_streamCarrier_prefix _ _ sourceAt
  exact ⟨position, rawValues, rawAt, objectCount.trans rawObjects, itemCount.trans rawItems⟩

/-- An item-carried notice has exactly the object prefix preceding its source handler.
Witness: recover its raw carrier and actual source input, then invert the accepted item's
leading-event position. The entire item-preparation phase emits no object publications.
-/
theorem Witness.itemNotice_sourceBoundary
    {work inputs} {w : Witness} {index owner values groups streams child}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups ++ streams)
    : ∃ before stream items after,
        inputs.flatten = before ++ .streamItems stream items :: after
        ∧ let current := (initialQueue work).replayGraphEvents before
          current.rootStreams.contains stream.key = true
          ∧ groups = (items.foldl streamItemStep (current, [], [], [])).2.1
          ∧ ((w.events.take index).flatMap normalizedObjectValues).length
            = (((initialQueue work).rawEventReplay before).2.flatMap
                WorkQueueEvent.objectValues).length := by
  obtain ⟨rawIndex, rawValues, rawAt, atomicCount, _⟩ :=
    Witness.itemNotice_rawPrefix started history selected noticed
  obtain ⟨before, event, after, position, shape, emitted, sourceCount⟩ :=
    (initialQueue work).rawEventReplay_output_at inputs.flatten rawAt
  obtain ⟨stream, items, rfl⟩ :=
    ((initialQueue work).replayGraphEvents before).handleGraphEvent_streamValues_source
      event emitted
  obtain ⟨active, zero, groupsEq⟩ :=
    ((initialQueue work).replayGraphEvents before).streamItems_noticeGroups stream items emitted
  refine ⟨before, stream, items, after, shape, active, groupsEq, ?_⟩
  exact atomicCount.trans
    (by simpa only [zero, List.take_zero, List.flatMap_nil,
      List.length_nil, Nat.add_zero] using sourceCount)

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
