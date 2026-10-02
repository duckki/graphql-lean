import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAncestorAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes

/-! Leading item notices account for their defer ancestry before the recursive drain. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Preparing items emits no object values and already retires the noticed ancestry
-----------------------------------------------------------------------------------------

/-- A leading item notice's ancestor contributions precede the entire item handler.
Witness: source accounting supplies prior publication or an entry buffer. Preparation
already retires the ancestor, and the common ledger's zero-step conservation excludes
such a buffer without appealing to a later drain publication or closure.
-/
theorem ExecutedWork.streamItems_leadingAncestor_contributor_before
    {work before stream items published owner values groups streams child
      dependencies key address owners producer payload}
    {position : Nat}
    (generated : ExecutedWork work)
    (valid : ValidGraphEvents work (before ++ [.streamItems stream items]))
    (started
      : (State.initialize (Work.fromExecution work)).acceptsBatch
          (before ++ [.streamItems stream items])
        = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
          (before ++ [.streamItems stream items]) published)
    (selected
      : (((State.initialize (Work.fromExecution work)).replayGraphEvents
            before).streamItems
          stream items).2[position]?
        = some (Execution.WorkQueueEvent.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            (((State.initialize (Work.fromExecution work)).rawEventReplay
                before).2.flatMap
              WorkQueueEvent.objectValues).length := by
  let initial := State.initialize (Work.fromExecution work)
  let queue := initial.replayGraphEvents before
  have keyNoticed : child.key ∈ rawGroupNoticeKeys (.streamValues owner values groups streams) :=
    List.mem_map_of_mem noticed
  have emitted := List.mem_of_getElem? selected
  obtain ⟨result, impossible | ⟨_, prior | buffered⟩⟩ :=
    generated.noticeAncestor_contributor_published_buffered_or_current valid started covered
      emitted keyNoticed known ancestor task contributes
  · cases impossible
  · exact ⟨result.value, prior⟩
  · obtain ⟨node, lookup, stored, taskOwners, nodeContributes, present⟩ := buffered
    obtain ⟨active, _, notices⟩ := queue.streamItems_noticeGroups stream items selected
    have matched := valid.eachMatches (List.mem_append_right before List.mem_cons_self)
    have retired := generated.streamItems_prepared_noticeAncestorsRetired
      (fun _ member => (valid.prefix (List.prefix_append before [_])).eachMatches member)
      matched child (notices ▸ noticed)
      child dependencies known rfl key ancestor _ _ taskOwners nodeContributes
    have notCancelled := (generated.noticeAncestor_healthy_uncancelled valid
      (State.acceptsBatch_prefix started) emitted keyNoticed known ancestor).2
    have endpoint : initial.replayGraphEvents (before ++ [.streamItems stream items])
        = (queue.preparedStreamItems items).drainReadyGroups.1 := by
      rw [State.replayGraphEvents_append, State.handleGraphEvent,
        State.streamItems_eq, active]
      rfl
    rw [endpoint] at notCancelled
    have healthy : key ∉ (queue.preparedStreamItems items).cancelledGroups :=
      fun member => notCancelled (State.drainReadyGroups_go_cancelledGroups_subset _ _ member)
    have prefixes := covered.atPrefixDrainOwners before (.streamItems stream items) []
    have conserved := prefixes active 0 (Nat.zero_le _) _ node result.value lookup stored
      key nodeContributes present healthy
    rcases conserved with published | retained
    · simp [State.drainReadyGroups.go] at published
    · exact False.elim (retired.2 retained.2)

-----------------------------------------------------------------------------------------
-- The exact raw and atomic carrier retain that earlier object-publication prefix
-----------------------------------------------------------------------------------------

/-- Raw replay publishes all contributors of an item notice's ancestor before its carrier.
Witness: locate the actual source input, which must be a stream-items event. Its notice
occupies the object-free leading output, so the handler-entry ledger is the strict prefix.
-/
theorem ExecutedWork.rawEventReplay_itemNoticeAncestor_covered
    {work events published index owner values groups streams child dependencies key
      address owners producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work events)
    (started : (State.initialize (Work.fromExecution work)).acceptsBatch events = true)
    (covered
      : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered events
          published)
    (selected
      : ((State.initialize (Work.fromExecution work)).rawEventReplay events).2[index]?
        = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : ∃ value,
        (Occurrence.executionGroup address, value)
        ∈ published.take
            ((((State.initialize (Work.fromExecution work)).rawEventReplay events).2.take
                index).flatMap
              WorkQueueEvent.objectValues).length := by
  obtain ⟨before, event, after, position, same, carrier, count⟩ :=
    (State.initialize (Work.fromExecution work)).rawEventReplay_output_at events selected
  obtain ⟨stream, items, rfl⟩ :=
    ((State.initialize (Work.fromExecution work)).replayGraphEvents
      before).handleGraphEvent_streamValues_source event carrier
  have prior : (before ++ [GraphEvent.streamItems stream items]).IsPrefix events :=
    ⟨after, by simp [same, List.append_assoc]⟩
  have accepted : (State.initialize (Work.fromExecution work)).acceptsBatch
      (before ++ [.streamItems stream items]) = true := by
    apply State.acceptsBatch_prefix (after := after)
    simpa only [same, List.append_assoc, List.singleton_append] using started
  have ledger : (State.initialize (Work.fromExecution work)).ReplayClosuresCovered
      (before ++ [.streamItems stream items]) published := by
    apply State.ReplayClosuresCovered.prefix (after := after)
    simpa only [same, List.append_assoc, List.singleton_append] using covered
  obtain ⟨_, zero, _⟩ :=
    ((State.initialize (Work.fromExecution work)).replayGraphEvents before).streamItems_noticeGroups
      stream items carrier
  rw [count, zero]
  simp only [List.take_zero, List.flatMap_nil, List.length_nil, Nat.add_zero]
  exact generated.streamItems_leadingAncestor_contributor_before (valid.prefix prior)
    accepted ledger carrier noticed known ancestor task contributes

namespace ConformancePlan

/-- An item-carried group notice's ancestor contributors are published on the same matching.
Witness: the joint raw/atomic carrier bridge preserves the strict object count. Interpret
that prefix with the original buffered closure ledger, without choosing new labels.
-/
theorem itemGroupNoticeAncestor_objectContributor_published
    {work inputs w index owner values groups streams child dependencies key address owners
      producer payload}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies)
    (task : TaskAt work (.executionGroup address) owners producer payload)
    (contributes : key ∈ owners)
    : Published w.matching (w.events.take index) (.executionGroup address) := by
  obtain ⟨published, batched, _, interpret, _⟩ := ledger
  have accepted : (initialQueue work).batchesStarted inputs = true := by
    rwa [← inputsStarted_eq_batchesStarted]
  obtain ⟨position, rawValues, atRaw, count, _⟩ :=
    Witness.itemNotice_rawPrefix started history selected (List.mem_append_left _ noticed)
  obtain ⟨value, delivered⟩ := generated.rawEventReplay_itemNoticeAncestor_covered valid
    ((initialQueue work).batchesStarted_acceptsBatch inputs accepted) (batched.flatten accepted)
    atRaw noticed known ancestor task contributes
  apply interpret index (Nat.le_of_lt (List.getElem?_eq_some_iff.mp selected).1)
    (.executionGroup address)
  rw [count, ← List.map_take]
  exact List.mem_map.mpr ⟨(_, value), delivered, rfl⟩

/-- An item-carried group notice accounts for all tasks belonging to each defer ancestor.
Witness: object contributors precede the item handler, and execution-generated roles
exclude stream contributors. This holds for arbitrary failure cuts, without cancellation.
-/
theorem itemGroupNoticeAncestor_nodeAccounted
    {work inputs w index owner values groups streams child dependencies key}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups) (known : GroupRecordAt work child dependencies)
    (ancestor : key ∈ dependencies) (failures : FailureCuts)
    : NodeAccounted work w.matching (w.events.take index) failures key := by
  intro occurrence owners ⟨producer, payload, task⟩ contributes
  cases occurrence with
  | executionGroup address =>
      exact Or.inr (itemGroupNoticeAncestor_objectContributor_published generated valid started
        history ledger selected noticed known ancestor task contributes)
  | item address ordinal =>
      obtain ⟨stream, items, enclosing, result, children, located, _, sameOwners, _⟩ := task
      rw [sameOwners] at contributes
      exact False.elim (generated.groupRecord_ancestor_ne_stream known ancestor (.stream located)
        (List.mem_singleton.mp contributes))

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
