import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AncestorPublicationBoundary
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupPublicationProducerOrder

/-! Already-active releasing groups give strict ancestor-producer publication. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Keep the actual source boundary and exact object offset of a raw releasing block
-----------------------------------------------------------------------------------------

/-- Source-handler evidence for one raw object block, with the exact prior object count.
`queue` and `received` fix executable replay; `group`, `values`, and `offset` identify the
block already selected by the atomic publication origin. This is proof-only evidence.
-/
structure GroupPublicationHandlerBoundary (queue : State) (received : List GraphEvent)
    (group : Execution.DeliveryNode) (values : List ExecutionGroupValue)
    (offset : Nat) where
  before : List GraphEvent
  event : GraphEvent
  after : List GraphEvent
  position : Nat
  sourceEq : received = before ++ event :: after
  atHandler
    : ((queue.replayGraphEvents before).handleGraphEvent event).2[position]?
      = some (.groupValues group values)
  count
    : offset
      = ((queue.rawEventReplay before).2.flatMap WorkQueueEvent.objectValues).length
        + ((((queue.replayGraphEvents before).handleGraphEvent event).2.take
              position).flatMap
            WorkQueueEvent.objectValues).length

/-- Each actual raw object origin recovers its own handler boundary and ledger offset.
Witness: indexed source-handler decomposition and the origin's exact raw prefix; silent
handlers and earlier blocks of the same handler remain part of the counted prefix.
-/
theorem GroupPublicationOrigin.handlerBoundary
    {publisher queue received index owner payload}
    (origin
      : GroupPublicationOrigin publisher (queue.rawEventReplay received).2
          index owner payload)
    : Nonempty
        (GroupPublicationHandlerBoundary queue received origin.group origin.values
          (origin.before.flatMap WorkQueueEvent.objectValues).length) := by
  have selected : (queue.rawEventReplay received).2[origin.before.length]?
      = some (.groupValues origin.group origin.values) := by
    have same := congrArg (fun raw : List WorkQueueEvent => raw[origin.before.length]?)
      origin.rawEq
    simpa using same
  obtain ⟨before, event, after, position, same, atHandler, count⟩ :=
    queue.rawEventReplay_output_at received selected
  have beforeEq : (queue.rawEventReplay received).2.take origin.before.length
      = origin.before := by
    have same := congrArg (List.take origin.before.length) origin.rawEq
    simpa using same
  rw [beforeEq] at count
  exact ⟨⟨before, event, after, position, same, atHandler, count⟩⟩

namespace ConformancePlan

-----------------------------------------------------------------------------------------
-- Ancestors already retired before the input are strictly before its object outputs
-----------------------------------------------------------------------------------------

/-- An already-active releasing group has its ancestor producer before this object atom.
Witness: exact handler origin supplies a source boundary. Structural root ancestry and
healthy retirement publish the ancestor contributor before that input; the retained
ledger offset puts it strictly before the selected atom under the same matching.
The active-root premise isolates this branch; same-handler activation is separate.
-/
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
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    (boundary
      : GroupPublicationHandlerBoundary (initialQueue work) inputs.flatten origin.group
          origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length)
    (active
      : origin.group.ref
        ∈ ((initialQueue work).replayGraphEvents boundary.before).rootGroups)
    (record : GroupRecordAt work origin.group dependencies)
    (ancestor : ref ∈ dependencies)
    (known : TaskAt work (.executionGroup source) owners producer parentPayload)
    (contributes : ref ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup source) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
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
  obtain ⟨groups, streams, carrier⟩ :=
    (((initialQueue work).replayGraphEvents boundary.before).handleGraphEvent_publicationPairs
      boundary.event).next boundary.atHandler
  obtain ⟨value, delivered⟩ := generated.activeAncestorContributor_published_before_handler
    (valid.prefix prior) priorAccepted earlierLedger (List.mem_of_getElem? carrier)
    active record ancestor known contributes
  have rank := origin.objectRank
  have historyEq := history.trans (createWorkQueue_nonterminalAtoms_flattened inputs started)
  rw [← historyEq] at rank
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
  rw [← List.map_take]
  refine List.mem_map.mpr ⟨(_, value), ?_, rfl⟩
  apply List.take_subset_take_left _ (show
    (((initialQueue work).rawEventReplay boundary.before).2.flatMap
      WorkQueueEvent.objectValues).length
      ≤ ((w.events.take index).flatMap normalizedObjectValues).length from ?_) delivered
  have count := boundary.count
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
          ((initialQueue work).rawEventReplay inputs.flatten).2 index owner payload)
    (boundary
      : GroupPublicationHandlerBoundary (initialQueue work) inputs.flatten origin.group
          origin.values (origin.before.flatMap WorkQueueEvent.objectValues).length)
    (active
      : origin.group.ref
        ∈ ((initialQueue work).replayGraphEvents boundary.before).rootGroups)
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
