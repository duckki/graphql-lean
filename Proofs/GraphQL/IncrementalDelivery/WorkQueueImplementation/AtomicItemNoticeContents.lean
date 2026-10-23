import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NoticeCarrierPrefixes
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupCarrierNoticeContents

/-! Item-carried group notices retain actual pre-startup contents on the canonical matching. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every actual item-carried group notice retains concrete unpublished task memberships.
The exact batch/FIFO boundary supplies source metadata and the same ledger prefix. Item
origin inversion locates the introducing pruning boundary before cached startup removal. -/
theorem itemGroupNotice_unpublished
    {work inputs w index owner values groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child := by
  obtain ⟨earlier, batch, later, fifo, stream, items, tail, split, batchEq, _, notices, count⟩ :=
    Witness.itemNotice_sourceBoundary started history selected (List.mem_append_left _ noticed)
  obtain ⟨published, batches, matching, _⟩ := ledger
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, _, source, _⟩ := generated.uncancelledFrames_atBatchEvent canonical
    valid started earlier batch later fifo (.streamItems stream items) tail split batchEq
  let boundary := (initialQueue work).replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have cut := batchHandlerMembershipCut batches valid started split batchEq
  have sourceCut := batchPublicationCut batches valid started earlier batch later fifo split
    ⟨.streamItems stream items :: tail, batchEq.symm⟩
  have prior : (earlier.flatten ++ fifo).IsPrefix inputs.flatten :=
    ⟨.streamItems stream items :: tail ++ later.flatten,
      by simp [split, batchEq, List.append_assoc]⟩
  have producers : TaskProducersSucceeded work (current.cacheTaskFailures available).tasks
      inputs.flatten := by
    rw [State.cacheTaskFailures_tasks]
    exact sourceCut.1.mono prior.subset
  have input : GraphEvent.streamItems stream items ∈ inputs.flatten := by
    rw [split, List.flatten_append, List.flatten_cons, batchEq]
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))
  apply source.streamItems_leadingNotice_contents generated canonical
    (sourceValid.eachMatches (List.mem_append_right _ List.mem_cons_self)) cut producers
    input matching objects ready (notices ▸ noticed)
  simpa only [List.flatMap_append, List.length_append] using count

/-- Item-carried group notices have the same retained contents on the causal-cut witness. -/
theorem itemGroupNotice_contents
    {work inputs w index owner values groups streams child}
    (generated : ExecutedWork work) (valid : ValidGraphEvents work inputs.flatten)
    (started : inputsStarted work inputs = true)
    (history : w.events = (initialQueue work).nonterminalAtoms inputs)
    (ledger : BufferedClosureLedger work inputs w)
    (objects : GroupPublicationAdmission work w)
    (ready : StreamPublicationReady work w)
    {streamCuts : FailureCuts}
    (_partition
      : let queue := initialQueue work
        let publisher : IncrementalPublisher :=
          { active := queue.initialGroups ++ queue.initialStreams }
        w.failures.Perm
          (streamCuts
            ++ informativeObjectFailureCuts work
                (queue.sourceRunBlocks publisher inputs).2.2))
    (selected : w.events[index]? = some (.streamValues owner values groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child :=
  itemGroupNotice_unpublished generated valid started history ledger objects ready
    selected noticed

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
