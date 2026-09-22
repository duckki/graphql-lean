import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationOwnership
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationItemBoundary

/-! Item-produced objects retain strict producer publication on the common witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Normalization preserves the exact item boundary before each object atom
-----------------------------------------------------------------------------------------

/-- The item rank before an object atom is exactly the rank before its raw object block.
Witness: normalize the actual raw prefix; preceding values in this object block add no
items, while publisher remapping and atomic stream splitting preserve item projection.
-/
theorem GroupPublicationOrigin.itemRank {publisher raw index owner payload}
    (origin : GroupPublicationOrigin publisher raw index owner payload)
    : ((((publisher.normalizeBatch raw).2.flatMap publicationAtoms).take index).flatMap
        normalizedItemValues).length
      = (origin.before.flatMap WorkQueueEvent.itemValues).length := by
  rw [origin.valuePrefix, List.flatMap_append]
  have noItems : (((publisher.normalizeBatch origin.before).1.handleWorkQueueEvent
      (.groupValues origin.group origin.values)).2.take origin.offset).flatMap
      normalizedItemValues = [] := by
    simp [IncrementalPublisher.handleWorkQueueEvent, ← List.map_take, List.flatMap_map,
      normalizedItemValues]
  rw [noItems, List.append_nil, publicationAtoms_list_itemValues,
    publisher.normalizeBatch_itemValues]

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- One retained item interpretation is shared with object and failure evidence
-----------------------------------------------------------------------------------------

/-- An item-produced raw releasing group places that item before this exact object atom.
Witness: raw source-boundary registration and item-first handling supply the prefix label;
unchanged item rank and the common ledger interpretation turn it into `Published`.
-/
theorem Witness.groupPublication_groupItemProducerPublished
    {work inputs w index owner payload node dependencies source ordinal}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    (known : NodeAt work node .group dependencies (some (.item source ordinal)))
    (sameKey : node.key = origin.group.key)
    : Published w.matching (w.events.take index) (.item source ordinal) := by
  obtain ⟨_, _, _, _, interpret⟩ := ledger
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  have atRaw : ((initialQueue work).rawEventReplay inputs.flatten).2[origin.before.length]?
      = some (.groupValues origin.group origin.values) := by
    have same := congrArg (fun raw : List WorkQueueEvent => raw[origin.before.length]?)
      origin.rawEq
    simpa using same
  have delivered := generated.rawEventReplay_groupValues_itemProducer_prefix valid
    ((initialQueue work).batchesStarted_acceptsBatch inputs accepted) atRaw known sameKey
  have beforeEq : ((initialQueue work).rawEventReplay inputs.flatten).2.take
      origin.before.length = origin.before := by
    have same := congrArg (List.take origin.before.length) origin.rawEq
    simpa using same
  rw [beforeEq] at delivered
  have rank := origin.itemRank
  have historyEq := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [← historyEq] at rank
  apply interpret index
  rwa [rank]

/-- Every item-produced object publishes strictly after its producer under the same matching.
Witness: exact object provenance identifies the producer of its available raw releasing
owner. The raw group's item-origin theorem then proves the required strict publication;
no extra source order or independently supplied producer-publication premise is assumed.
-/
theorem GroupPublicationReleases.itemProducerPublished
    {work inputs w index owner payload source ordinal}
    (releases : GroupPublicationReleases work inputs w) (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupValues owner payload))
    (produced : TaskHasProducer work (w.matching index) (some (.item source ordinal)))
    : Published w.matching (w.events.take index) (.item source ordinal) := by
  obtain ⟨origin, ⟨producer, known⟩, available⟩ :=
    releases.matched_available valid started history ledger selected
  obtain ⟨owners, taskPayload, descriptor⟩ := produced
  have sameProducer := (known.unique descriptor).2.1
  rw [sameProducer] at known
  cases matched : w.matching index with
  | item address itemIndex =>
      rw [matched] at known
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible
  | executionGroup address =>
      rw [matched] at known
      obtain ⟨node, dependencies, groupKnown, sameKey⟩ :=
        TaskAt.executionGroup_owner known available.1.2.1
      exact Witness.groupPublication_groupItemProducerPublished generated valid started
        history ledger origin groupKnown sameKey

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
