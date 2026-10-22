import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SuccessfulOwnerReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationProducerOrder

/-! Already-active releasing groups give strict ancestor-producer publication at actual cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An actual raw object block retains its host batch, FIFO handler and exact object offset. -/
structure GroupPublicationHandlerBoundary (queue : State)
    (batches : List (List GraphEvent)) (group : Execution.DeliveryNode)
    (values : List ExecutionGroupValue) (offset : Nat) where
  earlier : List (List GraphEvent)
  batch : List GraphEvent
  later : List (List GraphEvent)
  fifo : List GraphEvent
  event : GraphEvent
  tail : List GraphEvent
  position : Nat
  partition : batches = earlier ++ batch :: later
  batchEq : batch = fifo ++ event :: tail
  atHandler
    : (((queue.replayBatches earlier).replayGraphEvents fifo
          (GraphEvent.availableFailures batch)).handleGraphEvent
        event (GraphEvent.availableFailures batch)).2.1[position]?
      = some (.groupValues group values)
  count
    : offset
      = ((queue.rawBatches earlier).2.flatMap WorkQueueEvent.objectValues).length
        + (((queue.replayBatches earlier).rawEventReplay fifo
              (GraphEvent.availableFailures batch)).2.flatMap
            WorkQueueEvent.objectValues).length
        + (((((queue.replayBatches earlier).replayGraphEvents fifo
                (GraphEvent.availableFailures batch)).handleGraphEvent
              event (GraphEvent.availableFailures batch)).2.1.take
              position).flatMap
            WorkQueueEvent.objectValues).length

/-- The queue at this actual source input, before exposing that handler's rejection snapshot. -/
def GroupPublicationHandlerBoundary.current {queue batches group values offset}
    (boundary : GroupPublicationHandlerBoundary queue batches group values offset)
    : State :=
  (queue.replayBatches boundary.earlier).replayGraphEvents boundary.fifo
    (GraphEvent.availableFailures boundary.batch)

/-- One raw publication origin determines an actual batch/FIFO source boundary. -/
theorem GroupPublicationOrigin.handlerBoundary
    {publisher queue batches index owner payload}
    (origin
      : GroupPublicationOrigin publisher (queue.rawBatches batches).2 index owner payload)
    : Nonempty
        (GroupPublicationHandlerBoundary queue batches origin.group origin.values
          (origin.before.flatMap WorkQueueEvent.objectValues).length) := by
  have selected : (queue.rawBatches batches).2[origin.before.length]?
      = some (.groupValues origin.group origin.values) := by
    have same := congrArg (fun raw : List WorkQueueEvent => raw[origin.before.length]?) origin.rawEq
    simpa using same
  obtain ⟨earlier, batch, later, fifo, event, tail, position, split, batchEq, atHandler, count⟩ :=
    queue.rawBatches_immediate_handlerCut batches selected
      (by intro _ _ impossible; cases impossible) (by intro impossible; cases impossible)
  have beforeEq : (queue.rawBatches batches).2.take origin.before.length = origin.before := by
    have same := congrArg (List.take origin.before.length) origin.rawEq
    simpa using same
  rw [beforeEq] at count
  exact ⟨⟨
          earlier,
          batch,
          later,
          fifo,
          event,
          tail,
          position,
          split,
          batchEq,
          atHandler,
          count
        ⟩⟩

namespace ConformancePlan

/-- An already-active releasing group has every ancestor producer in the earlier ledger.
Root ancestry supplies retirement at the actual FIFO cut. The live record's uncancelled
ancestor certificate and the same-cut publication frame then give the strict prefix. -/
theorem Witness.groupPublication_activeAncestorProducerPublished
    {work inputs w index owner payload source owners producer parentPayload dependencies
      ref}
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
          ((initialQueue work).rawBatches inputs).2 index owner payload)
    (boundary
      : GroupPublicationHandlerBoundary (initialQueue work) inputs origin.group
          origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length)
    (active : origin.group.ref ∈ boundary.current.rootGroups)
    (record : GroupRecordAt work origin.group dependencies)
    (ancestor : ref ∈ dependencies)
    (known : TaskAt work (.executionGroup source) owners producer parentPayload)
    (contributes : ref ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup source) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.ownerPublicationFrame_atBatchPrefix canonical valid started batched
    boundary.earlier boundary.batch boundary.later boundary.fifo boundary.partition
    ⟨boundary.event :: boundary.tail, boundary.batchEq.symm⟩
  have sourceValid := valid.prefix (show (boundary.earlier.flatten ++ boundary.fifo).IsPrefix
    inputs.flatten from ⟨boundary.event :: boundary.tail ++ boundary.later.flatten,
      by simp [boundary.partition, boundary.batchEq, List.append_assoc]⟩)
  have retired := frame.source.roots.live.roots origin.group.ref active origin.group dependencies
    record rfl ref ancestor (.executionGroup source) owners
      ⟨producer, parentPayload, known⟩ contributes
  obtain ⟨node, member, sameRef⟩ := List.mem_map.mp (frame.source.roots.live.present _ active)
  have uncancelled := frame.source.markers.live_record_ancestors frame.source.parent.safe
    frame.source.parent.fields frame.source.parent.closed frame.source.parent.live canonical
    record ⟨node, member, sameRef⟩ ref ancestor (.executionGroup source) owners
    ⟨producer, parentPayload, known⟩ contributes
  obtain ⟨value, delivered⟩ := frame.retired_structuralContributor_published generated sourceValid
    known contributes retired uncancelled
  have rank := origin.objectRank
  rw [(Witness.rawBatches_canonical history selected).2] at rank
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  rw [← List.map_take]
  apply List.mem_map.mpr
  refine ⟨(_, value), ?_, rfl⟩
  apply List.take_subset_take_left _ (show _ ≤ ((w.events.take index).flatMap
      normalizedObjectValues).length from ?_) delivered
  rw [rank]
  have offset := boundary.count
  dsimp only [initialQueue] at offset
  omega

/-- Every object producer precedes publication when its raw releasing group was already active.
Witness: exact task provenance and generated local defer continuity give a supporting
producer owner. Reused support uses same-block registration order; strict ancestor support
uses prior healthy retirement. Only activation within the current handler is excluded.
-/
theorem Witness.groupPublication_activeObjectProducerPublished
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
          ((initialQueue work).rawBatches inputs).2 index owner payload)
    (boundary
      : GroupPublicationHandlerBoundary (initialQueue work) inputs origin.group
          origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length)
    (active : origin.group.ref ∈ boundary.current.rootGroups)
    (rawKnown
      : ∃ dependencies producer, NodeAt work origin.group .group dependencies producer)
    (contributes
      : origin.group.ref ∈ origin.value.deliveryGroups.map Execution.DeliveryNode.ref)
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
      obtain ⟨node, dependencies, childKnown, sameRef⟩ :=
        TaskAt.executionGroup_owner known contributes
      obtain ⟨rawDependencies, rawProducer, rawKnown⟩ := rawKnown
      have sameNode := generated.nodeRefCoherent _ _ _ _ _ _ _ _ childKnown rawKnown sameRef
      rw [sameNode] at childKnown
      obtain ⟨parentOwners, ancestor, parentPayload, ref, parentKnown, parentContributes,
        support⟩ := generated.group_objectProducer_support childKnown
      rcases support with reused | dependency
      · apply Witness.groupPublication_reusedProducerPublished generated valid started history
          ledger selected origin ⟨owners, taskPayload, descriptor⟩ parentKnown
        exact reused ▸ parentContributes
      · exact Witness.groupPublication_activeAncestorProducerPublished generated valid started
          history ledger selected origin boundary active (groupRecordAt_of_nodeAt childKnown)
          dependency parentKnown parentContributes

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
