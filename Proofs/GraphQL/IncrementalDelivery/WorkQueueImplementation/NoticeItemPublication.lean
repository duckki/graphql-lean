import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeItemBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes

/-! Group notices retain their item-producer publications on the canonical atomic witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Successful group carriers preserve the same strict item rank through both mappings
-----------------------------------------------------------------------------------------

/-- Splitting normalized values preserves the item rank before a group-success carrier.
Witness: that carrier expands to itself, while every earlier expansion retains its exact
item sequence. Locate by index rather than equal payloads or matching notice lists.
-/
theorem publicationAtoms_groupSuccess_itemPrefix (events : List Execution.WorkQueueEvent)
    {index group groups streams}
    (selected
      : (events.flatMap publicationAtoms)[index]?
        = some (.groupSuccess group groups streams))
    : ∃ position,
        events[position]? = some (.groupSuccess group groups streams)
        ∧ (((events.flatMap publicationAtoms).take index).flatMap
            normalizedItemValues).length
          = ((events.take position).flatMap normalizedItemValues).length := by
  induction events generalizing index with
  | nil => simp at selected
  | cons event rest ih =>
      rw [List.flatMap_cons] at selected ⊢
      by_cases earlier : index < (publicationAtoms event).length
      · have atHead := (List.getElem?_append_left earlier).symm.trans selected
        obtain ⟨rfl, rfl⟩ := publicationAtoms_groupSuccess event atHead
        exact ⟨0, rfl, rfl⟩
      · have later : (publicationAtoms event).length ≤ index := by omega
        obtain ⟨position, atSource, count⟩ :=
          ih ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨position + 1, atSource, ?_⟩
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
          List.length_append, count, (publicationAtoms_values event).2]
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]

/-- Publisher remapping preserves the item rank before the exact raw group-success carrier.
Witness: a group completion maps unchanged; earlier raw events preserve item projection
even when object ownership remapping changes the number of intervening output events.
-/
theorem IncrementalPublisher.normalizeBatch_groupSuccess_itemPrefix
    (publisher : IncrementalPublisher) (events : List WorkQueueEvent)
    {index group groups streams}
    (selected
      : (publisher.normalizeBatch events).2[index]?
        = some (.groupSuccess group groups streams))
    : ∃ position,
        events[position]? = some (.groupSuccess group groups streams)
        ∧ (((publisher.normalizeBatch events).2.take index).flatMap
            normalizedItemValues).length
          = ((events.take position).flatMap WorkQueueEvent.itemValues).length := by
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
        exact ⟨0, rfl, rfl⟩
      · have later : head.2.length ≤ index := by omega
        obtain ⟨position, atRaw, count⟩ := ih head.1
          ((List.getElem?_append_right later).symm.trans selected)
        refine ⟨position + 1, atRaw, ?_⟩
        change (((head.2 ++ tail.2).take index).flatMap normalizedItemValues).length = _
        rw [List.take_append, List.take_of_length_le later, List.flatMap_append,
          List.length_append, count]
        simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
        exact congrArg (· + _) (congrArg List.length
          (publisher.handleWorkQueueEvent_itemValues event))

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Either notice carrier supplies the same inclusive raw item prefix
-----------------------------------------------------------------------------------------

/-- A canonical group notice retains its raw carrier and inclusive item-prefix count.
Witness: group carriers preserve their strict rank and carry no items; item notices occur
only on the final atom of their raw batch. Both retain the same noticed key and index.
-/
theorem Witness.groupNotice_itemRawPrefix {work inputs} {w : Witness} {index event key}
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (selected : w.events[index]? = some event)
    (noticed : key ∈ groupNoticeKeys event)
    : ∃ position output,
        ((initialQueue work).rawEventReplay inputs.flatten).2[position]? = some output
        ∧ key ∈ rawGroupNoticeKeys output
        ∧ ((w.events.take (index + 1)).flatMap normalizedItemValues).length
          = ((((initialQueue work).rawEventReplay inputs.flatten).2.take
                (position + 1)).flatMap
              WorkQueueEvent.itemValues).length := by
  cases event with
  | groupSuccess group groups streams =>
      have exactHistory := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
      have atFull := selected
      rw [exactHistory] at atFull
      obtain ⟨sourceIndex, atSource, sourceCount⟩ :=
        publicationAtoms_groupSuccess_itemPrefix _ atFull
      obtain ⟨position, atRaw, rawCount⟩ :=
        IncrementalPublisher.normalizeBatch_groupSuccess_itemPrefix _ _ atSource
      refine ⟨position, _, atRaw, noticed, ?_⟩
      simp only [List.take_add_one, selected, atRaw, Option.toList_some,
        List.flatMap_append, List.flatMap_singleton, normalizedItemValues,
        WorkQueueEvent.itemValues, List.append_nil]
      rw [exactHistory]
      exact sourceCount.trans rawCount
  | streamValues owner values groups streams =>
      obtain ⟨child, member, same⟩ := List.mem_map.mp noticed
      obtain ⟨position, rawValues, atRaw, _, itemCount⟩ :=
        w.itemNotice_rawPrefix started history selected (List.mem_append_left streams member)
      refine ⟨position, _, atRaw, ?_, itemCount⟩
      exact List.mem_map.mpr ⟨child, member, same⟩
  | groupValues | groupFailure | streamSuccess | streamFailure | workQueueTermination =>
      cases noticed

/-- Every item-produced group notice has its producer published by the carrier's end.
Witness: its actual raw handler registers the group only after the producer input. The
same inclusive item rank survives normalization and atomic splitting; the shared ledger
interprets that source occurrence with the original matching, not a separately chosen one.
-/
theorem Witness.groupNotice_itemProducerPublished
    {work inputs} {w : Witness} {index event node dependencies source ordinal}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some event)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (noticed : node.key ∈ groupNoticeKeys event)
    : Published w.matching (w.events.take (index + 1)) (.item source ordinal) := by
  obtain ⟨_, _, _, _, interpret⟩ := ledger
  have batches : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  obtain ⟨position, output, atRaw, rawNotice, itemCount⟩ :=
    w.groupNotice_itemRawPrefix started history selected noticed
  have delivered := generated.rawEventReplay_groupNotice_itemProducer_prefix valid
    ((initialQueue work).batchesStarted_acceptsBatch inputs batches) atRaw known rawNotice
  apply interpret (index + 1)
  rwa [itemCount]

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
