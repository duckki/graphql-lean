import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedStreamBatchCuts
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ActualSourceFrames
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredStreamReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationCoverage

/-! Actual successful object sources release every child stream of a retired contributor. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- An actual success releases each structural child stream before an uncancelled owner retires.
The source cut retains its cache snapshot. Complete fresh attachment feeds buffered-stream
conservation through the rest of that batch and all later actual batches.
-/
theorem ExecutedWork.success_retired_childStream_notice_forBatches
    {work inputs earlier batch later fifo tail occurrence result node owners producer
      payload ref stream dependencies}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work (List.flatten inputs))
    (started : inputsStarted work inputs = true)
    (split : inputs = earlier ++ batch :: later)
    (batchEq : batch = fifo ++ .taskSuccess occurrence result :: tail)
    (found
      : ((((State.initialize (Work.fromExecution work)).replayBatches
            earlier).replayGraphEvents
            fifo (GraphEvent.availableFailures batch)).cacheTaskFailures
          (GraphEvent.availableFailures batch)).taskNode?
          occurrence
        = some node)
    (known : TaskAt work occurrence owners producer payload) (contributes : ref ∈ owners)
    (retired
      : ((State.initialize (Work.fromExecution work)).runNormalized inputs).1.RetiredGroup
          ref)
    (uncancelled
      : ref
        ∉ ((State.initialize (Work.fromExecution work)).runNormalized
            inputs).1.cancelledGroups)
    (child : NodeAt work stream .stream dependencies (some occurrence))
    : stream.ref
      ∈ ((State.initialize (Work.fromExecution work)).rawBatches inputs).2.flatMap
          rawStreamNoticeRefs := by
  let initial := State.initialize (Work.fromExecution work)
  let available := GraphEvent.availableFailures batch
  let boundary := initial.replayBatches earlier
  let current := boundary.replayGraphEvents fifo available
  let cached := current.cacheTaskFailures available
  let after := (current.dispatchGraphEvent (.taskSuccess occurrence result) available).1
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  have frame := generated.bufferedStreamFrame_atBatchPrefix canonical earlier batch later fifo
    (split ▸ valid) (split ▸ started) ⟨.taskSuccess occurrence result :: tail, batchEq.symm⟩
  obtain ⟨sourceValid, _, _, _⟩ := generated.uncancelledFrames_atBatchEvent canonical valid
    started earlier batch later fifo (.taskSuccess occurrence result) tail split batchEq
  obtain ⟨prior, matching, fresh⟩ := validGraphEvents_last sourceValid
  have licensed : ∀ task errors, (task, errors) ∈ available →
      (GraphEvent.taskFailure task errors).MatchesWork work := by
    intro task errors member
    obtain ⟨event, received, same⟩ := List.mem_filterMap.mp member
    cases event <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    apply valid.eachMatches
    rw [split, List.flatten_append, List.flatten_cons]
    exact List.mem_append_right _ (List.mem_append_left _ received)
  have starts := split ▸ started
  rw [inputsStarted_eq_batchesStarted, State.batchesStarted_append, Bool.and_eq_true] at starts
  obtain ⟨running, batchAccepted, restStarted⟩ := boundary.batchesStarted_cons batch later starts.2
  have finalEq : initial.replayBatches inputs =
      (boundary.handleGraphEvents batch).1.replayBatches later := by
    simp only [boundary, split, State.replayBatches, List.foldl_append, List.foldl_cons]
  have finalRetired : (initial.replayBatches inputs).RetiredGroup ref := by
    rwa [State.runNormalized_replayBatches] at retired
  have finalUncancelled : ref ∉ (initial.replayBatches inputs).cancelledGroups := by
    rwa [State.runNormalized_replayBatches] at uncancelled
  have batchCancellation :=
    (boundary.handleGraphEvents batch).1.rawBatches_cancelledGroups_subset later
  rw [State.rawBatches_state, ← finalEq] at batchCancellation
  have currentCancellation := (boundary.batchPrefix_cancelledGroups_subset batchEq running).trans
    batchCancellation
  have sourceUncancelled : ref ∉ cached.cancelledGroups := by
    intro member
    apply finalUncancelled
    apply currentCancellation
    simpa only [cached, State.cacheTaskFailures_cancelledGroups] using member
  have pending := frame.source.source.pending.cacheTaskFailures available
  have registered := pending.started node (State.taskNode?_some found).1
  have identity := (State.taskNode?_some found).2
  obtain ⟨address, storedPayload, birth, _, descriptor⟩ := (pending.matching node.task registered).1
  have sameOwners : node.task.groups.map Execution.DeliveryNode.ref = owners :=
    (descriptor.unique (identity.symm ▸ known)).1
  have nodeFresh : node.task.occurrence ∉
      GraphEvent.groupSettlements (earlier.flatten ++ fifo) := by
    rw [identity]
    intro settled
    exact fresh.2.2.1 occurrence List.mem_cons_self
      (GraphEvent.groupSettlements_subsetIdentities _ settled)
  obtain ⟨owner, member, ownerRef, _⟩ := (frame.source.source.owners.cacheTaskFailures available)
    node.task registered nodeFresh ref (sameOwners.symm ▸ contributes) sourceUncancelled
  have sourceLive : ref ∈ cached.groupNodes.map (fun group => group.group.node.ref) :=
    List.mem_map.mpr ⟨owner, member, ownerRef⟩
  have origins := generated.batchPrefix_streamProducersSeen earlier fifo available prior
  have streamAbsent := (origins.cacheTaskFailures available).freshProducer_streamAbsent
    generated child
    (fresh.2.2.1 occurrence List.mem_cons_self)
  obtain ⟨buffered, stored, sameTask, value, attached⟩ :=
    State.maybeIntegrateWork_fresh_stream_attached
    (State.putTaskNode_value_lookup found result.value) result.work
    (matching.taskChildStreams_complete child) streamAbsent
  have clean := (frame.buffersCacheClean prior available licensed).cacheTaskFailures available
  have first := State.taskSuccess_preparedBufferedStreams (result := result) pending
    (frame.links.cacheTaskFailures available) (frame.children.cacheTaskFailures available) found
    (identity ▸ nodeFresh) available clean (matching.success_cacheClean available licensed)
  have prefixEq : batch = (fifo ++ [.taskSuccess occurrence result]) ++ tail := by
    simp only [batchEq, List.append_assoc, List.singleton_append]
  have baseFrame := generated.bufferedStreamFrame_atBatchPrefix canonical earlier batch later []
    (split ▸ valid) (split ▸ started) ⟨batch, by simp⟩
  simp only [State.replayGraphEvents, List.foldl_nil, List.append_nil] at baseFrame
  have remainingValid : ValidGraphEvents work (earlier.flatten ++ batch ++ later.flatten) := by
    simpa only [split, List.flatten_append, List.flatten_cons, List.append_assoc]
      using valid
  have future := baseFrame.batchTail_conserves generated canonical prefixEq remainingValid
    running batchAccepted restStarted
  have afterCancellation : after.cancelledGroups.Subset
      (initial.replayBatches inputs).cancelledGroups := by
    intro owner member
    apply batchCancellation
    apply boundary.batchPrefix_cancelledGroups_subset prefixEq running
    simpa only [after, current, available, State.replayGraphEvents, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using member
  have continuation : after.BufferedStreamsConserved (boundary.rawBatches (batch :: later)).2
      (initial.replayBatches inputs) := by
    rw [finalEq]
    simpa only [after, current, boundary, initial, available, State.replayGraphEvents,
      State.replayBatches,
      List.foldl_append, List.foldl_cons, List.foldl_nil] using future
  have combined := first.append continuation afterCancellation
  have preparedLive := State.maybeIntegrateWork_includesRefs
    (cached.putTaskNode {node with value := some result.value}) result.work (some occurrence) ref
    sourceLive
  have noticed := combined.retired_notice stored value attached
    (sameTask.symm ▸ sameOwners.symm ▸ contributes) preparedLive finalRetired.2 finalUncancelled
  have outputSubset := boundary.handler_streamNotices_subset_batch batchEq running
  rw [List.flatMap_append] at noticed
  have inRest : stream.ref ∈
      (boundary.rawBatches (batch :: later)).2.flatMap rawStreamNoticeRefs := by
    rcases List.mem_append.mp noticed with first | future
    · simp only [State.rawBatches, List.flatMap_append]
      exact List.mem_append_left _ (outputSubset first)
    · exact future
  rw [split, State.rawBatches_append]
  dsimp only
  rw [List.flatMap_append, State.rawBatches_state]
  exact List.mem_append_right _ inRest

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
