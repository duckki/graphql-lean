import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupAncestorProducer
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.HandlerProducerPublication
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationItemProducer

/-! General object producer readiness on the unchanged common conformance witness. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every object producer precedes its child object atom in actual normalized output.
Witness: generated defer continuity gives reused or ancestor support. Reused support uses
registration order within a shared block. Ancestor support now covers both prior activation
and activation inside either successful handler; exact raw offsets transport its strict
prefix to the same normalized matching and ledger. No handler-shape premise remains.
-/
theorem Witness.groupPublication_objectProducerPublished
    {work inputs w index owner payload source}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupValues owner payload))
    (origin
      : GroupPublicationOrigin
          {
            active :=
              (initialQueue work).initialGroups ++ (initialQueue work).initialStreams
          }
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    (boundary
      : GroupPublicationHandlerBoundary (initialQueue work) inputs.flatten origin.group
          origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length)
    (rawKnown
      : ∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
    (contributes
      : origin.group.key ∈ origin.value.deliveryGroups.map Execution.DeliveryNode.key)
    (produced : TaskHasProducer work (w.matching index) (some (.executionGroup source)))
    : Published w.matching (w.events.take index) (.executionGroup source) := by
  obtain ⟨producer, known⟩ := Witness.groupPublication_taskAt started history ledger selected origin
  obtain ⟨owners, taskPayload, descriptor⟩ := produced
  have sameProducer := (known.unique descriptor).2.1
  rw [sameProducer] at known
  cases matched : w.matching index with
  | item address ordinal =>
      rw [matched] at known
      obtain ⟨_, _, _, _, _, _, _, _, impossible⟩ := known
      cases impossible
  | executionGroup address =>
      rw [matched] at known
      obtain ⟨node, dependencies, childKnown, sameKey⟩ :=
        TaskAt.executionGroup_owner known contributes
      obtain ⟨rawDependencies, rawProducer, rawKnown⟩ := rawKnown
      have sameNode := generated.nodeKeyCoherent _ _ _ _ _ _ _ _ childKnown rawKnown sameKey
      rw [sameNode] at childKnown
      obtain ⟨parentOwners, ancestor, parentPayload, key, parentKnown, parentContributes,
        support⟩ := generated.group_objectProducer_support childKnown
      rcases support with reused | dependency
      · apply Witness.groupPublication_reusedProducerPublished generated valid started history
          ledger selected origin ⟨owners, taskPayload, descriptor⟩ parentKnown
        exact reused ▸ parentContributes
      · obtain ⟨published, batched, _, interpret, _⟩ := ledger
        have accepted : (initialQueue work).batchesStarted inputs = true := by
          rwa [← inputsStarted_eq_batchesStarted]
        have received := (initialQueue work).batchesStarted_acceptsBatch inputs accepted
        have prior : (boundary.before ++ [boundary.event]).IsPrefix inputs.flatten :=
          ⟨boundary.after, by simp [boundary.sourceEq, List.append_assoc]⟩
        have priorAccepted : (initialQueue work).acceptsBatch
            (boundary.before ++ [boundary.event]) = true := by
          apply State.acceptsBatch_prefix (after := boundary.after)
          simpa only [boundary.sourceEq, List.append_assoc, List.singleton_append] using received
        have earlierLedger : (initialQueue work).ReplayClosuresCovered
            (boundary.before ++ [boundary.event]) published := by
          apply State.ReplayClosuresCovered.prefix (after := boundary.after)
          simpa only [boundary.sourceEq, List.append_assoc, List.singleton_append]
            using batched.flatten accepted
        obtain ⟨value, delivered⟩ := generated.handleGraphEvent_ancestorProducer_beforeValue
          (valid.prefix prior) priorAccepted earlierLedger boundary.atHandler known contributes
          (groupRecordAt_of_nodeAt childKnown) dependency parentKnown parentContributes
        have rank := origin.objectRank
        have historyEq := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
        rw [← historyEq] at rank
        apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
        rw [← List.map_take]
        refine List.mem_map.mpr ⟨(_, value), ?_, rfl⟩
        have count := boundary.count
        apply List.take_subset_take_left _
          (show (((initialQueue work).rawEventReplay boundary.before).2.flatMap
                    WorkQueueEvent.objectValues).length
                  + (((((initialQueue work).replayGraphEvents
                          boundary.before).handleGraphEvent
                        boundary.event).2.take
                        boundary.position).flatMap
                      WorkQueueEvent.objectValues).length
                ≤ ((w.events.take index).flatMap normalizedObjectValues).length from ?_)
          delivered
        change (origin.before.flatMap WorkQueueEvent.objectValues).length = _ at count
        omega

/-- Every actual object value has its structural producer in the strict output prefix.
Witness: the actual release origin supplies raw group provenance and contributor identity.
Object producers use the complete handler argument; item producers use item-first output
order. Both cases retain the same publication matching and exact replay ledger.
-/
theorem GroupPublicationReleases.producerPublished
    {work inputs w index owner payload parent}
    (releases : GroupPublicationReleases work inputs w) (generated : ExecutedWork work)
    (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.groupValues owner payload))
    (produced : TaskHasProducer work (w.matching index) (some parent))
    : Published w.matching (w.events.take index) parent := by
  cases parent with
  | item source ordinal =>
      exact releases.itemProducerPublished generated valid started history ledger selected produced
  | executionGroup source =>
      obtain ⟨origin, rawKnown, _, _⟩ := releases index owner payload selected
      obtain ⟨boundary⟩ := origin.handlerBoundary
      have contributes := createWorkQueue_rawEventReplay_publicationContributors valid
        origin.group origin.values origin.members.1 origin.value origin.members.2
      exact Witness.groupPublication_objectProducerPublished generated valid started history
        ledger selected origin boundary rawKnown contributes produced

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
