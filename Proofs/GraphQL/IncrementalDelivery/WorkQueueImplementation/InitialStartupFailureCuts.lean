import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupOutputCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAnnouncements
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureAnnouncementCuts

/-! Startup-aware source failures have contributors announced at their actual output cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A later source failure is announced before its exact output position, even when the
first host batch also forwards initial aggregate reports. Initial notices add no source
settlement; historical contributor licensing uses the actual batch/FIFO task lookup.
-/
theorem State.startup_sourceObjectFailureCuts_announcedOwner {work : Execution.Work}
    (startup : InitialStartup) {batches : List (List GraphEvent)}
    (valid : ValidGraphEvents work batches.flatten)
    (started : inputsStarted work batches startup = true) {cut : Nat}
    {occurrence : Occurrence}
    (member
      : let initial := State.initialize (Work.fromExecution work) startup
        let publisher : IncrementalPublisher :=
          { active := initial.initialGroups ++ initial.initialStreams }
        (cut, occurrence)
        ∈ sourceObjectFailureCuts 0 (initial.sourceRunBlocks publisher batches).2.2)
    : let initial := State.initialize (Work.fromExecution work) startup
      ∃ owners owner,
        TaskHasOwners work occurrence owners
        ∧ owner ∈ owners
        ∧ owner
          ∈ announcedRefs
              ((initial.initialGroups ++ initial.initialStreams).map
                Execution.DeliveryNode.ref)
              (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                cut) := by
  let initial := State.initialize (Work.fromExecution work) startup
  let queue := initial
  let publisher : IncrementalPublisher := { active := queue.initialGroups ++ queue.initialStreams }
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
    simp [inputEq, batchEq, List.append_assoc]
  have beforeValid := valid.prefix priorPrefix
  have priorValid := beforeValid.prefix (List.prefix_append earlier.flatten before)
  have stateEq : current = (queue.runNormalized earlier).1 :=
    (queue.sourceRunBlocks_withPublisher_agrees publisher earlier).1
  obtain ⟨owners, owner, structural, contributes, announced⟩ :=
    State.startup_taskFailure_announcedOwner startup earlier batch later before after occurrence
      errors batchEq (inputEq ▸ valid) (inputEq ▸ started)
  let priorAtoms := (queue.runNormalized earlier).2.flatten.flatMap publicationAtoms
  let immediate := (current.rawEventReplay before available).2
  let localAtoms := (first.2.1.normalizeBatch immediate).2.flatMap publicationAtoms
  have prefixEq : (blocks.take blockIndex).flatMap Prod.snd = priorAtoms ++ localAtoms := by
    rw [beforeBlocks, inTrace.2, beforeTrace, List.flatMap_append,
      (queue.sourceRunBlocks_withPublisher_agrees publisher earlier).2.2,
      (current.sourceOutputBlocks_agrees first.2.1 before available).2.2]
    rfl
  have outputPrefix : ((blocks.take blockIndex).flatMap Prod.snd).IsPrefix
      ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms) := by
    refine ⟨(blocks.drop blockIndex).flatMap Prod.snd, ?_⟩
    rw [← List.flatMap_append, List.take_append_drop]
    exact (queue.sourceRunBlocks_withPublisher_agrees publisher batches).2.2
  have takeEq : ((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take
      cut = (blocks.take blockIndex).flatMap Prod.snd := by
    obtain ⟨suffix, same⟩ := outputPrefix
    rw [same.symm]
    have bound : cut = ((blocks.take blockIndex).flatMap Prod.snd).length := by
      simpa only [Nat.zero_add] using boundary
    rw [bound]
    simp
  have priorNotices : priorAtoms.flatMap groupNoticeRefs
      = (queue.runNormalized earlier).2.flatten.flatMap groupNoticeRefs :=
    publicationAtoms_flatMap_groupNotices _
      (queue.runNormalized_nonemptyValues earlier priorValid.nonemptyItems).2
  have localNotices : localAtoms.flatMap groupNoticeRefs
      = (current.rawEventReplay before available).2.flatMap rawGroupNoticeRefs :=
    atomicGroupNotices _ _ (current.rawEventReplay_nonemptyValues before
      (fun event member => beforeValid.nonemptyItems event (List.mem_append_right _ member))
      available)
  have seen : owner ∈ queue.initialGroups.map Execution.DeliveryNode.ref
      ++ (((queue.runNormalized batches).2.flatten.flatMap publicationAtoms).take cut
        ).flatMap groupNoticeRefs := by
    rw [takeEq, prefixEq, List.flatMap_append, ← List.append_assoc,
      priorNotices, localNotices, stateEq]
    exact announced
  refine ⟨owners, owner, structural, contributes, ?_⟩
  rcases List.mem_append.mp seen with initial | carried
  · apply List.mem_append_left
    rw [List.map_append]
    exact List.mem_append_left _ initial
  · exact List.mem_append_right _ (groupNotices_subset_pending _ carried)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
