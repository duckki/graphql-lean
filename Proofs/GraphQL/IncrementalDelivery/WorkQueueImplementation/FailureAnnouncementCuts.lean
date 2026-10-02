import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskAnnouncementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureSettlementPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureInventory

/-! Previously announced contributing owners at the actual ordered settlement cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Exact group-notice transport through handler annotations and atomic expansion
-----------------------------------------------------------------------------------------

/-- Each annotated block preserves its source handler's group notices from queue `queue`.
Optional terminal labels have no handler and no group notices. This is derived proof
evidence about actual output, not a restriction on the scheduler or event source.
-/
private def SourceBlockNotices : State → List SourceOutputBlock → Prop
  | _, [] => True
  | queue, block :: rest =>
      (queue.rawEventReplay block.1.toList).2.flatMap rawGroupNoticeKeys
        = block.2.flatMap groupNoticeKeys
      ∧ SourceBlockNotices (queue.replayGraphEvents block.1.toList) rest

/-- Notice preservation composes at the exact received source prefix.
Witness: recurse through the original labels, including silent and terminal blocks.
-/
private theorem SourceBlockNotices.append {queue left right}
    (first : SourceBlockNotices queue left)
    (last : SourceBlockNotices (queue.replayGraphEvents (left.filterMap Prod.fst)) right)
    : SourceBlockNotices queue (left ++ right) := by
  induction left generalizing queue with
  | nil => exact last
  | cons block rest ih =>
      refine ⟨first.1, ih first.2 ?_⟩
      cases source : block.1 <;>
        simpa [source, State.replayGraphEvents] using last

/-- Every annotation prefix inherits its blocks' notice-preservation certificate.
Witness: take the head equation and recurse through the same pre-handler states.
-/
private theorem SourceBlockNotices.prefix {queue before after}
    (known : SourceBlockNotices queue (before ++ after))
    : SourceBlockNotices queue before := by
  induction before generalizing queue with
  | nil => trivial
  | cons block rest ih => exact ⟨known.1, ih known.2⟩

/-- Blockwise agreement identifies the entire raw and atomic group-notice histories.
Witness: source replay and output concatenation follow the same original block order.
-/
private theorem SourceBlockNotices.notices {queue blocks}
    (known : SourceBlockNotices queue blocks)
    : (queue.rawEventReplay (blocks.filterMap Prod.fst)).2.flatMap rawGroupNoticeKeys
      = (blocks.flatMap Prod.snd).flatMap groupNoticeKeys := by
  induction blocks generalizing queue with
  | nil => rfl
  | cons block rest ih =>
      cases source : block.1 with
      | none =>
          have empty : block.2.flatMap groupNoticeKeys = [] := by
            simpa [source, State.rawEventReplay] using known.1.symm
          simpa [source, List.flatMap_append, empty, State.replayGraphEvents]
            using ih known.2
      | some event =>
          have head : (queue.handleGraphEvent event).2.flatMap rawGroupNoticeKeys
              = block.2.flatMap groupNoticeKeys := by
            simpa [source, State.rawEventReplay, rawEventStep] using known.1
          simpa [source, State.rawEventReplay_cons, List.flatMap_append, head,
            State.replayGraphEvents]
            using congrArg ((block.2.flatMap groupNoticeKeys) ++ ·) (ih known.2)

/-- Normalizing and atomizing legal raw output preserves its exact group notices.
Witness: publisher notice copying and the nonempty payload atomization equations.
-/
theorem atomicGroupNotices (publisher : IncrementalPublisher)
    (events : List WorkQueueEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyValues)
    : ((publisher.normalizeBatch events).2.flatMap publicationAtoms).flatMap
        groupNoticeKeys
      = events.flatMap rawGroupNoticeKeys := by
  have expand (outputs : List Execution.WorkQueueEvent)
      (shape : ∀ event ∈ outputs, NonemptyValues event)
      : (outputs.flatMap publicationAtoms).flatMap groupNoticeKeys
        = outputs.flatMap groupNoticeKeys := by
    induction outputs with
    | nil => rfl
    | cons event rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append,
          publicationAtoms_groupNotices event (shape event (by simp)),
          ih (fun next member => shape next (List.mem_cons_of_mem _ member))]
  calc
    _ = (publisher.normalizeBatch events).2.flatMap groupNoticeKeys := by
      exact expand _ (publisher.normalizeBatch_nonemptyValues events nonempty).2
    _ = _ := publisher.normalizeBatch_groupNotices events

/-- Actual handler annotations preserve notices even across silent source inputs.
Witness: legal item shapes give nonempty payloads; each publisher segment copies notices.
-/
private theorem State.sourceOutputBlocks_groupNotices (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyItems)
    : SourceBlockNotices queue (queue.sourceOutputBlocks publisher events).2.2 := by
  induction events generalizing queue publisher with
  | nil => trivial
  | cons event rest ih =>
      refine ⟨
        ?_,
        ih _ _ (fun next member => nonempty next (List.mem_cons_of_mem _ member))
      ⟩
      simpa [State.rawEventReplay, rawEventStep]
        using (atomicGroupNotices publisher (queue.handleGraphEvent event).2
                (queue.handleGraphEvent_nonemptyValues event
                  (nonempty event (by simp)))).symm

/-- Batch termination contributes no group notice and no source settlement label.
Witness: append an empty-notice certificate to the unchanged handler annotations.
-/
private theorem State.sourceBatchBlocks_groupNotices (queue : State)
    (publisher : IncrementalPublisher) (events : List GraphEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyItems)
    : SourceBlockNotices queue (queue.sourceBatchBlocks publisher events).2.2 := by
  have handlers := queue.sourceOutputBlocks_groupNotices publisher events nonempty
  unfold State.sourceBatchBlocks
  split
  · trivial
  · dsimp only
    split
    · exact handlers.append ⟨rfl, trivial⟩
    · exact handlers

/-- Started multi-batch replay preserves notices at every original handler boundary.
Witness: batch agreement and start checks keep pre-handler queue states identical;
the final optional termination block is notice-free.
-/
private theorem State.sourceRunBlocks_groupNotices (queue : State)
    (publisher : IncrementalPublisher) (batches : List (List GraphEvent))
    (nonempty : ∀ event ∈ batches.flatten, event.NonemptyItems)
    (started : queue.batchesStarted batches = true)
    : SourceBlockNotices queue (queue.sourceRunBlocks publisher batches).2.2 := by
  induction batches generalizing queue publisher with
  | nil => trivial
  | cons batch rest ih =>
      obtain ⟨running, _, restStarted⟩ := queue.batchesStarted_cons batch rest started
      have first := queue.sourceBatchBlocks_groupNotices publisher batch
        (fun event member => nonempty event (by simp [member]))
      cases rest with
      | nil => simpa [State.sourceRunBlocks] using first
      | cons next rest =>
          have stillOpen := ((queue.handleGraphEvents batch).1.batchesStarted_cons next rest
            restStarted).1
          have unchanged := queue.handleGraphEvents_nonterminalState batch running stillOpen
          have agreement := (queue.sourceBatchBlocks_agrees publisher batch).1
          rw [← agreement] at restStarted
          have later := ih _ (queue.sourceBatchBlocks publisher batch).2.1
            (fun event member => nonempty event
              (List.mem_append_right batch member)) restStarted
          rw [State.sourceRunBlocks]
          apply first.append
          rw [queue.sourceBatchBlocks_inputs_of_open publisher batch running,
            ← unchanged, ← agreement]
          exact later

-----------------------------------------------------------------------------------------
-- An accepted object settlement has a previously announced structural contributor
-----------------------------------------------------------------------------------------

/-- Group-only notice keys occur in the scheduler's combined group/stream notice list.
Witness: each carrier appends its stream keys after its group keys.
-/
private theorem groupNotices_subset_pending (events : List Execution.WorkQueueEvent)
    : (events.flatMap groupNoticeKeys).Subset (pendingKeys events) := by
  intro key member
  obtain ⟨event, emitted, announced⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨event, emitted, ?_⟩
  cases event <;> simp_all [groupNoticeKeys, eventPending, List.map_append]

/-- Every actual eligible object-failure cut has a previously announced contributing owner.
Witness: recover the exact source prefix, use historical task-start ownership, and transport
raw notices through actual normalization and atomization at that same output boundary.
This proves the announcement clause only; earlier cancellation remains a separate obligation.
-/
theorem createWorkQueue_eligibleObjectFailureCuts_announcedOwner {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {before after : FailureCuts}
    {cut : Nat} {occurrence : Occurrence}
    (split
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        sourceObjectFailureCuts 0
          (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
        = before ++ (cut, occurrence) :: after)
    : let queue := State.initialize (Work.fromExecution work)
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedKeys
              ((queue.initialGroups ++ queue.initialStreams).map
                Execution.DeliveryNode.key)
              (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                cut) := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  obtain ⟨earlier, outputs, errors, later, node, blocksEq, _, outputEq, _,
    priorValid, _, _, _, found, _⟩ :=
    createWorkQueue_eligibleObjectFailureCuts_split valid started split
  obtain ⟨owners, owner, structural, contributes, announced⟩ :=
    createWorkQueue_replayGraphEvents_announcedOwner priorValid found
  have certificate := queue.sourceRunBlocks_groupNotices publisher batches valid.nonemptyItems
    (by rwa [← inputsStarted_eq_batchesStarted])
  rw [blocksEq] at certificate
  have notices := certificate.prefix.notices
  rw [notices, outputEq] at announced
  refine ⟨owners, owner, structural, contributes, ?_⟩
  rcases List.mem_append.mp announced with initial | later
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_left _ initial
  · exact List.mem_append_right _ (groupNotices_subset_pending _ later)

/-- Actual replay has one complete mixed inventory whose every failure owner was announced.
Witness: merge the unchanged source-ordered object cuts with actual stream-failure cuts;
historical task starts justify object owners and stream openness supplies stream owners.
The same inventory retains all previously proved exact group and stream error totals.
-/
theorem createWorkQueue_announcedFailureInventory_exists {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      let initial :=
        (queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.key
      ∃ failures : FailureCuts,
        CompleteFailureInventory work atoms failures
        ∧ ∀ entry ∈ failures,
            ∃ owners,
              TaskHasOwners work entry.2 owners
              ∧ ∃ key ∈ owners, key ∈ announcedKeys initial (atoms.take entry.1) := by
  dsimp only
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := sourceObjectFailureCuts 0
    (queue.eligibleFailureBlocks (queue.sourceRunBlocks publisher batches).2.2)
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  obtain ⟨streams, cuts, _, supported⟩ := createWorkQueue_runNormalized_streamFailureCuts
    generated valid matching (fun index event atEvent value =>
      (values index event atEvent value).1) covered
  refine ⟨mergeFailureCuts objects streams,
    createWorkQueue_completeFailureInventory generated valid started cuts
      (fun entry member => (supported entry member).1), ?_⟩
  intro entry member
  rcases List.mem_append.mp ((mergeFailureCuts_partition objects streams).mem_iff.mp member)
      with fromStream | fromObject
  · obtain ⟨key, owners, opened⟩ := (supported entry fromStream).2.2
    exact ⟨[key], owners, key, List.mem_cons_self, opened.1⟩
  · obtain ⟨before, after, split⟩ := List.mem_iff_append.mp fromObject
    obtain ⟨owners, key, structural, contributes, announced⟩ :=
      createWorkQueue_eligibleObjectFailureCuts_announcedOwner valid started split
    exact ⟨owners, structural, key, contributes, announced⟩

/-- A complete, announced mixed inventory needs only earlier-cancellation exclusion.
Witness: project the general complete-inventory equivalence after discharging notices;
the remaining clause still uses the exact ordered earlier-cut list and one matching.
-/
theorem CompleteFailureInventory.failureWitness_iff_uncancelled
    {work events failures initial matching}
    (inventory : CompleteFailureInventory work events failures)
    (announced
      : ∀ entry ∈ failures,
          ∃ owners,
            TaskHasOwners work entry.2 owners
            ∧ ∃ key ∈ owners, key ∈ announcedKeys initial (events.take entry.1))
    : FailureWitness work initial matching events failures
      ↔ ∀ before cut occurrence after,
          failures = before ++ (cut, occurrence) :: after
          → ¬TaskCancelled work matching (events.take cut) before occurrence := by
  rw [inventory.failureWitness_iff]
  exact ⟨And.right, fun uncancelled => ⟨announced, uncancelled⟩⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
