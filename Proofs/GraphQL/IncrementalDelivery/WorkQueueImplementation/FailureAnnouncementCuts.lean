import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ReportCutAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskAnnouncementReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SourceHandlerBoundaries
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureInventory

/-! Previously announced contributing owners at actual source reporting cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Atomizing nonempty carrier values retains all group notice refs in their order. -/
theorem publicationAtoms_flatMap_groupNotices (events : List WorkQueueEvent)
    (nonempty : ∀ event ∈ events, NonemptyValues event)
    : (events.flatMap publicationAtoms).flatMap groupNoticeRefs
      = events.flatMap groupNoticeRefs := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp only [List.flatMap_cons, List.flatMap_append,
        publicationAtoms_groupNotices event (nonempty event List.mem_cons_self),
        ih (fun next member => nonempty next (List.mem_cons_of_mem _ member))]

/-- Normalizing and atomizing legal raw output preserves its exact group notices.
Witness: publisher notice copying and the nonempty payload atomization equations.
-/
theorem atomicGroupNotices (publisher : IncrementalPublisher)
    (events : List WorkQueueEvent)
    (nonempty : ∀ event ∈ events, event.NonemptyValues)
    : ((publisher.normalizeBatch events).2.flatMap publicationAtoms).flatMap
        groupNoticeRefs
      = events.flatMap rawGroupNoticeRefs := by
  have expand (outputs : List Execution.WorkQueueEvent)
      (shape : ∀ event ∈ outputs, NonemptyValues event)
      : (outputs.flatMap publicationAtoms).flatMap groupNoticeRefs
        = outputs.flatMap groupNoticeRefs := by
    induction outputs with
    | nil => rfl
    | cons event rest ih =>
        simp only [List.flatMap_cons, List.flatMap_append,
          publicationAtoms_groupNotices event (shape event (by simp)),
          ih (fun next member => shape next (List.mem_cons_of_mem _ member))]
  calc
    _ = (publisher.normalizeBatch events).2.flatMap groupNoticeRefs := by
      exact expand _ (publisher.normalizeBatch_nonemptyValues events nonempty).2
    _ = _ := publisher.normalizeBatch_groupNotices events

/-- Group-only notice refs occur in the scheduler's combined group/stream notice list.
Witness: each carrier appends its stream refs after its group refs.
-/
theorem groupNotices_subset_pending (events : List Execution.WorkQueueEvent)
    : (events.flatMap groupNoticeRefs).Subset (pendingRefs events) := by
  intro ref member
  obtain ⟨event, emitted, announced⟩ := List.mem_flatMap.mp member
  apply List.mem_flatMap.mpr
  refine ⟨event, emitted, ?_⟩
  cases event <;> simp_all [groupNoticeRefs, eventPending, List.map_append]

/-- Every source reporting cut has a contributor announced before that exact output cut.
Witness: invert its labeled block, retain the actual preceding host batches and current
snapshot, and recover the task's historical owner. Notice transport uses the same block
prefix, including silent handlers; no flattened queue-state correspondence is assumed.
-/
theorem createWorkQueue_sourceObjectFailureCuts_announcedOwner {work : Execution.Work}
    {batches : List (List GraphEvent)} (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {cut : Nat} {occurrence : Occurrence}
    (member
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        (cut, occurrence)
        ∈ sourceObjectFailureCuts 0 (queue.sourceRunBlocks publisher batches).2.2)
    : let queue := State.initialize (Work.fromExecution work)
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedRefs
              ((queue.initialGroups ++ queue.initialStreams).map
                Execution.DeliveryNode.ref)
              (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                cut) := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let blocks := (queue.sourceRunBlocks publisher batches).2.2
  obtain ⟨blockIndex, outputs, errors, atBlock, boundary⟩ :=
    sourceObjectFailureCuts_blockCut member
  obtain ⟨earlier, batch, later, localIndex, inputEq, atBatchBlock, beforeBlocks⟩ :=
    queue.sourceRunBlocks_blockCut publisher batches atBlock
  let first := queue.sourceRunBlocks publisher earlier
  let current := first.1
  let available := GraphEvent.availableFailures batch
  have inTrace := current.sourceBatchBlocks_labeledPrefix first.2.1 batch atBatchBlock rfl
  obtain ⟨before, after, batchEq, beforeTrace⟩ :=
    current.sourceOutputBlocks_labeledCut first.2.1 batch available inTrace.1 rfl
  have priorPrefix : (earlier.flatten ++ before).IsPrefix batches.flatten := by
    refine ⟨.taskFailure occurrence errors :: (after ++ later.flatten), ?_⟩
    simp only [inputEq, List.flatten_append, List.flatten_cons, batchEq]
    simp only [List.append_assoc, List.cons_append]
  have beforeValid := valid.prefix priorPrefix
  have priorValid := beforeValid.prefix (List.prefix_append earlier.flatten before)
  have stateEq : current = (queue.runNormalized earlier).1 :=
    (queue.sourceRunBlocks_agrees earlier).1
  have accepted := inputsStarted_eachAccepted work earlier later batch before
    (.taskFailure occurrence errors) (inputEq ▸ started) ⟨after, by simp [batchEq]⟩
  rw [← State.runNormalized_replayBatches] at accepted
  obtain ⟨seen, seenPrefix, accepted⟩ := accepted
  have findNode (state : State)
      (eligible : state.acceptsGraphEvent (.taskFailure occurrence errors) = true)
      : ∃ node, state.taskNode? occurrence = some node := by
    cases found : state.taskNode? occurrence with
    | none => simp only [State.acceptsGraphEvent, found, Option.isSome_none,
        Bool.false_eq_true] at eligible
    | some node => exact ⟨node, rfl⟩
  have ownerEvidence : ∃ owners owner,
      TaskHasOwners work occurrence owners ∧ owner ∈ owners
      ∧ owner ∈ queue.initialGroups.map Execution.DeliveryNode.ref
        ++ (queue.runNormalized earlier).2.flatten.flatMap groupNoticeRefs
        ++ (((queue.runNormalized earlier).1).rawEventReplay before available).2.flatMap
          rawGroupNoticeRefs := by
    obtain ⟨node, found⟩ := findNode _ accepted
    have seenValid : ValidGraphEvents work (earlier.flatten ++ seen) := beforeValid.prefix (by
      obtain ⟨remaining, same⟩ := seenPrefix
      exact ⟨remaining, by simp [← same, List.append_assoc]⟩)
    obtain ⟨owners, owner, structural, contributes, announced⟩ :=
      createWorkQueue_batchPrefix_announcedOwner earlier seen seenValid available found
    refine ⟨owners, owner, structural, contributes, ?_⟩
    rcases List.mem_append.mp announced with old | recent
    · exact List.mem_append_left _ old
    · apply List.mem_append_right
      obtain ⟨remaining, same⟩ := seenPrefix
      rw [← same, State.rawEventReplay_append _ _ _ available, List.flatMap_append]
      exact List.mem_append_left _ recent
  obtain ⟨owners, owner, structural, contributes, announced⟩ := ownerEvidence
  let priorAtoms := (queue.runNormalized earlier).2.flatten.flatMap publicationAtoms
  let immediate := (current.rawEventReplay before available).2
  let localAtoms := (first.2.1.normalizeBatch immediate).2.flatMap publicationAtoms
  have prefixEq : ((blocks.take blockIndex).flatMap Prod.snd) = priorAtoms ++ localAtoms := by
    rw [beforeBlocks, inTrace.2, beforeTrace, List.flatMap_append,
      (queue.sourceRunBlocks_agrees earlier).2,
      (current.sourceOutputBlocks_agrees first.2.1 before available).2.2]
  have outputPrefix : ((blocks.take blockIndex).flatMap Prod.snd).IsPrefix
      ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms) := by
    refine ⟨(blocks.drop blockIndex).flatMap Prod.snd, ?_⟩
    rw [← List.flatMap_append, List.take_append_drop]
    exact (queue.sourceRunBlocks_agrees batches).2
  have takeEq : ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take cut
      = (blocks.take blockIndex).flatMap Prod.snd := by
    obtain ⟨suffix, same⟩ := outputPrefix
    rw [same.symm]
    have bound : cut = ((blocks.take blockIndex).flatMap Prod.snd).length := by
      simpa only [Nat.zero_add] using boundary
    rw [bound]
    simp
  have priorNotices : priorAtoms.flatMap groupNoticeRefs
      = (queue.runNormalized earlier).2.flatten.flatMap groupNoticeRefs :=
    publicationAtoms_flatMap_groupNotices _
      (createWorkQueue_runNormalized_nonemptyValues priorValid).2
  have localNotices : localAtoms.flatMap groupNoticeRefs
      = (current.rawEventReplay before available).2.flatMap rawGroupNoticeRefs :=
    atomicGroupNotices _ _ (current.rawEventReplay_nonemptyValues before
      (fun event member => beforeValid.nonemptyItems event (List.mem_append_right _ member))
      available)
  have seen : owner ∈ queue.initialGroups.map Execution.DeliveryNode.ref
      ++ (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take cut).flatMap
          groupNoticeRefs := by
    rw [takeEq, prefixEq, List.flatMap_append, ← List.append_assoc,
      priorNotices, localNotices, stateEq]
    exact announced
  refine ⟨owners, owner, structural, contributes, ?_⟩
  rcases List.mem_append.mp seen with initial | carried
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_left _ initial
  · exact List.mem_append_right _ (groupNotices_subset_pending _ carried)

/-- Every selected availability cut retains an owner announced by that unchanged cut.
Source settlements use their actual snapshot-aware task history; aggregate causes use
an already announced failed-group contributor. First-occurrence selection changes neither. -/
theorem createWorkQueue_availableObjectFailureCuts_announcedOwner {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true) {entry : Nat × Occurrence}
    (member
      : let queue := State.initialize (Work.fromExecution work)
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        entry
        ∈ availableObjectFailureCuts work 0 (queue.sourceRunBlocks publisher batches).2.2)
    : let queue := State.initialize (Work.fromExecution work)
      ∃ owners owner,
        TaskHasOwners work entry.2 owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedRefs
              ((queue.initialGroups ++ queue.initialStreams).map
                Execution.DeliveryNode.ref)
              (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                entry.1) := by
  rcases availableObjectFailureCuts_origin member with source | report
  · exact createWorkQueue_sourceObjectFailureCuts_announcedOwner valid started source
  · exact createWorkQueue_groupReportCandidateCuts_announcedOwner generated valid report

/-- Actual replay has one complete mixed reporting inventory with prior owner notices.
Witness: unfiltered source availability and actual stream cuts retain aggregate totals;
historical starts and stream openness supply their prior contributing announcements.
-/
theorem createWorkQueue_announcedFailureInventory_exists {work : Execution.Work}
    (generated : ExecutedWork work) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches = true)
    : let queue := State.initialize (Work.fromExecution work)
      let atoms := (queue.runNormalized batches).2.flatten.flatMap publicationAtoms
      let initial :=
        (queue.initialGroups ++ queue.initialStreams).map Execution.DeliveryNode.ref
      ∃ reported : FailureCuts,
        CompleteFailureInventory work atoms reported
        ∧ FailureReportingWitness work initial atoms reported := by
  let queue := State.initialize (Work.fromExecution work)
  let publisher : IncrementalPublisher :=
    { active := queue.initialGroups ++ queue.initialStreams }
  let objects := availableObjectFailureCuts work 0 (queue.sourceRunBlocks publisher batches).2.2
  obtain ⟨matching, _, values, _, covered⟩ :=
    createWorkQueue_runNormalized_streamProducerMatching_withItemCoverage generated valid started
  obtain ⟨streams, cuts, _, supported⟩ := createWorkQueue_runNormalized_streamFailureCuts
    generated valid matching (fun index event atEvent value =>
      (values index event atEvent value).1) covered
  have inventory := createWorkQueue_completeFailureInventory generated valid cuts
    (fun entry member => (supported entry member).1)
  refine ⟨mergeFailureCuts objects streams, inventory, inventory.failureReportingWitness ?_⟩
  intro entry member
  rcases List.mem_append.mp ((mergeFailureCuts_partition objects streams).mem_iff.mp member)
      with fromStream | fromObject
  · obtain ⟨ref, owners, opened⟩ := (supported entry fromStream).2.2
    exact ⟨[ref], owners, ref, List.mem_cons_self, opened.1⟩
  · obtain ⟨owners, ref, structural, contributes, announced⟩ :=
      createWorkQueue_availableObjectFailureCuts_announcedOwner generated valid started fromObject
    exact ⟨owners, structural, ref, contributes, announced⟩

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
            ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (events.take entry.1))
    : FailureWitness work initial matching events failures
      ↔ ∀ before cut occurrence after,
          failures = before ++ (cut, occurrence) :: after
          → ¬TaskCancelled work matching (events.take cut) before occurrence := by
  rw [inventory.failureWitness_iff]
  exact ⟨And.right, fun uncancelled => ⟨announced, uncancelled⟩⟩

/-- A complete, announced mixed inventory needs only earlier-cancellation exclusion.
Witness: project the general complete-inventory equivalence after discharging notices;
the remaining clause still uses the exact ordered earlier-cut list and one matching.
-/
theorem CausalFailureInventory.failureWitness_iff_uncancelled
    {work events failures initial matching}
    (inventory : CausalFailureInventory work events failures)
    (announced
      : ∀ entry ∈ failures,
          ∃ owners,
            TaskHasOwners work entry.2 owners
            ∧ ∃ ref ∈ owners, ref ∈ announcedRefs initial (events.take entry.1))
    : FailureWitness work initial matching events failures
      ↔ ∀ before cut occurrence after,
          failures = before ++ (cut, occurrence) :: after
          → ¬TaskCancelled work matching (events.take cut) before occurrence := by
  rw [inventory.failureWitness_iff]
  exact ⟨And.right, fun uncancelled => ⟨announced, uncancelled⟩⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
