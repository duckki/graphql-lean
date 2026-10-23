import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.SnapshotGroupNoticeContents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.AtomicCarrierCoverage

/-! Canonical group carriers retain concrete unpublished contents at actual source cuts. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

namespace ConformancePlan

/-- Every canonical group notice retains unpublished tasks.
Witness: the actual source boundary supplies the carrier's object rank and its exact
owner-fold or pre-startup drain contents. The common
publication ledger supplies nonpublication without assuming the child's notice admission.
-/
theorem groupGroupNotice_unpublished
    {work inputs w index group groups streams child}
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
    (selected : w.events[index]? = some (.groupSuccess group groups streams))
    (noticed : child ∈ groups)
    : RetainedNoticeContents work w.matching (w.events.take index)
        (failedBefore w.failures index) inputs.flatten child := by
  obtain ⟨published, batches, matching, _⟩ := ledger
  obtain ⟨atFull, beforeEq⟩ := Witness.canonical_event history selected
  obtain ⟨position, atRaw, atomicCount⟩ :=
    createWorkQueue_runNormalized_groupSuccess_rawPrefix started atFull
  obtain ⟨earlier, batch, later, fifo, event, tail, localIndex, split, batchEq, emitted,
    count⟩ := (initialQueue work).rawBatches_groupSuccess_handlerCut inputs atRaw
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨sourceValid, _, source, _⟩ := generated.uncancelledFrames_atBatchEvent canonical
    valid started earlier batch later fifo event tail split batchEq
  let boundary := (initialQueue work).replayBatches earlier
  let available := GraphEvent.availableFailures batch
  let current := boundary.replayGraphEvents fifo available
  have cut := batchHandlerMembershipCut batches valid started split batchEq
  have sourceCut := batchPublicationCut batches valid started earlier batch later fifo split
    ⟨event :: tail, batchEq.symm⟩
  have prior : (earlier.flatten ++ fifo).IsPrefix inputs.flatten :=
    ⟨event :: tail ++ later.flatten, by simp [split, batchEq, List.append_assoc]⟩
  have producers : TaskProducersSucceeded work (current.cacheTaskFailures available).tasks
      inputs.flatten := by
    rw [State.cacheTaskFailures_tasks]
    exact sourceCut.1.mono prior.subset
  have input : event ∈ inputs.flatten := by
    rw [split, List.flatten_append, List.flatten_cons, batchEq]
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ List.mem_cons_self))
  apply source.groupNotice_unpublished generated canonical (valid.eachMatches input) cut
    producers input matching objects ready emitted noticed
  rw [← beforeEq, atomicCount, count]
  simp only [List.flatMap_append, List.length_append]

end ConformancePlan
end GraphQL.IncrementalDelivery.ReferenceWorkQueue
